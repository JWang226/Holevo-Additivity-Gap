# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Pinned checker preparation shared by the portable verification modes."""
from datetime import datetime, timezone
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REVISION = "a4f696825c583ed8a5b4060d9a0faa5b882d365b"
DEPENDENCIES = {"lean4export": "048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d",
                "Lean4Checker": "b7398199245524275543dec6113229c9bb4902e5"}
REPOSITORY = "https://github.com/leanprover/comparator.git"
DEFAULT_CONFIGS = ["ComparatorChallenges/" + name + ".json" for name in (
    "A_PrescribedDimensions", "B_OperationalCoding", "C_SmallInformationSeparation", "D_WeylAllUses", "E_InputCost")]
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(arguments, cwd=ROOT, **kwargs):
    print("+ " + " ".join(map(str, arguments)), flush=True)
    environment = dict(os.environ, LEAN_ABORT_ON_PANIC="1")
    environment.update(kwargs.pop("env", {}))
    return subprocess.run(list(map(str, arguments)), cwd=cwd, env=environment,
                          check=True, **kwargs)


def output(arguments, cwd=ROOT):
    return subprocess.check_output(list(map(str, arguments)), cwd=cwd, text=True).strip()


def bindings():
    sources = sorted((ROOT / "Nonadditivity").rglob("*.lean"))
    sources += [ROOT / name for name in ("Nonadditivity.lean", "Audit.lean", "All.lean")]
    artifacts = [ROOT / name for name in (
        "verification/kernel_common.py", "verification/comparator/check_local.py",
        "verification/comparator/ReplayExports.lean", "verification/nanoda/check_nanoda.py",
        "verification/nanoda/toolchain.json", "scripts/verify.sh", "scripts/test_nanoda_check.py",
        "lake-manifest.json", "lean-toolchain", "metadata/results.json", "formalization.yaml",
        "lakefile.toml", "verification/lean/run.sh", "verification/comparator/run.sh",
        "verification/nanoda/run.sh", "verification/check_reports.py", "build.sh", "check.sh", "lean.sh",
        "scripts/compiler.py", "scripts/validate_release.py", "scripts/check_declarations.py",
        "scripts/check_challenges.py", "requirements-validation.txt")]
    artifacts += sorted((ROOT / "ComparatorChallenges").glob("*.lean"))
    artifacts += sorted((ROOT / "ComparatorChallenges").glob("*.json"))
    return {"proof_source_sha256": {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(sources)},
            "artifact_sha256": {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(artifacts)}}


def prepare_comparator():
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.29.0-rc6":
        raise ValueError("The checker pin requires Lean 4.29.0-rc6.")
    if "version 4.29.0-rc6," not in output(["lean", "--version"]):
        raise ValueError("Select the committed Lean toolchain before checking.")
    directory = ROOT / ".verify-work/comparator"
    directory.parent.mkdir(parents=True, exist_ok=True)
    if not directory.exists():
        run(["git", "clone", "--no-checkout", REPOSITORY, directory])
        new = True
    else:
        new = False
    if output(["git", "remote", "get-url", "origin"], directory) != REPOSITORY:
        raise ValueError("Unexpected Comparator origin.")
    if not new and output(["git", "status", "--porcelain", "--untracked-files=no"], directory):
        raise ValueError("Comparator has tracked edits; use a clean checkout.")
    exists = subprocess.run(["git", "cat-file", "-e", REVISION + "^{commit}"], cwd=directory,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if exists.returncode:
        run(["git", "fetch", "origin", REVISION], cwd=directory)
    run(["git", "checkout", "--detach", REVISION], cwd=directory)
    if output(["git", "rev-parse", "HEAD"], directory) != REVISION:
        raise ValueError("Comparator checkout revision mismatch.")
    if (directory / "lean-toolchain").read_text().strip() != toolchain:
        raise ValueError("Comparator toolchain mismatch.")
    manifest = directory / "lake-manifest.json"
    before = manifest.read_bytes()
    packages = {p["name"]: p["rev"] for p in json.loads(before)["packages"]}
    if packages != DEPENDENCIES:
        raise ValueError("Comparator dependency revisions differ from the pins.")
    run(["lake", "build", "Comparator", "Lean4Checker", "lean4export"], directory)
    if manifest.read_bytes() != before:
        raise ValueError("Comparator build changed its committed manifest.")
    for name, revision in DEPENDENCIES.items():
        package = directory / ".lake/packages" / name
        if output(["git", "rev-parse", "HEAD"], package) != revision:
            raise ValueError("Checker dependency checkout differs: " + name)
        if output(["git", "status", "--porcelain", "--untracked-files=no"], package):
            raise ValueError("Checker dependency has tracked edits: " + name)
    if output(["git", "status", "--porcelain", "--untracked-files=no"], directory):
        raise ValueError("Comparator build modified tracked sources.")
    exporter = directory / ".lake/packages/lean4export/.lake/build/bin/lean4export"
    if not exporter.is_file():
        raise ValueError("Pinned exporter was not built.")
    return directory, exporter


def replay(directory, config, expected, solution):
    run(["lake", "env", "lean", "--run", ROOT / "verification/comparator/ReplayExports.lean",
         config, expected, solution], directory)


def validate_configs(config_names):
    paths = [(ROOT / name).resolve() for name in config_names]
    if not paths or len(set(paths)) != len(paths):
        raise ValueError("Duplicate configuration.")
    for path in paths:
        if path.parent != ROOT / "ComparatorChallenges" or path.suffix != ".json":
            raise ValueError("Use a committed Comparator challenge configuration.")
        config = json.loads(path.read_text())
        names = config.get("theorem_names")
        if (not isinstance(names, list) or not names or any(not isinstance(n, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9\']*(?:\.[A-Za-z_][A-Za-z_0-9\']*)*", n) for n in names) or len(set(names)) != len(names)):
            raise ValueError("Invalid or duplicate theorem roots")
        if set(config["permitted_axioms"]) != AXIOMS or config["enable_nanoda"] is not False:
            raise ValueError("Expected exactly the three standard axioms and separate Nanoda mode.")
    return paths


def report(mode, cases, snapshot, **extra):
    if bindings() != snapshot:
        raise ValueError("Verification inputs changed during execution; rerun on stable sources.")
    return {"schema_version": 1, "status": "passed", "mode": mode, "sandboxed": False,
            "upstream_sandboxed_comparator": "not_run",
            "completed_at_utc": datetime.now(timezone.utc).isoformat(),
            "git_commit": output(["git", "rev-parse", "HEAD"]),
            "worktree_dirty": bool(output(["git", "status", "--porcelain"])),
            "binding_note": "Source and artifact hashes identify checked inputs; the base commit alone does not identify uncommitted changes.",
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "lean_version": output(["lean", "--version"]),
            "comparator_commit": REVISION, "checker_dependencies": DEPENDENCIES,
            "permitted_axioms": sorted(AXIOMS), "cases": cases, **snapshot, **extra}
