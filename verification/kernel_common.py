# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Pinned checker preparation shared by the portable verification modes."""
from datetime import datetime, timezone
import hashlib
import json
import os
import re
from pathlib import Path, PurePosixPath
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REVISION = "a4f696825c583ed8a5b4060d9a0faa5b882d365b"
DEPENDENCIES = {"lean4export": "048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d",
                "Lean4Checker": "b7398199245524275543dec6113229c9bb4902e5"}
REPOSITORY = "https://github.com/leanprover/comparator.git"
DEFAULT_CONFIGS = ["ComparatorChallenges/" + name + ".json" for name in (
    "A_PrescribedDimensions", "B_OperationalCoding", "C_SmallInformationSeparation", "D_WeylAllUses", "E_InputCost", "F_TwoUseSeparation")]
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


def certificate_artifacts():
    """Bind the selected source gate and its retained evidence, without executing it.

    The release validator checks the certificate's semantics. Portable checker
    snapshots also retain the exact bytes on which that gate depends, including
    the historical Lake file used by the explicitly additive certificate.
    """
    files = {}

    def local_file(name):
        if (not isinstance(name, str) or not name or "\\" in name or ":" in name
                or PurePosixPath(name).is_absolute()
                or any(part in {"", ".", ".."} for part in name.split("/"))):
            raise ValueError("Unsafe source-certificate artifact path: " + str(name))
        path = ROOT / name
        if not path.is_file() or not path.resolve().is_relative_to(ROOT.resolve()):
            raise ValueError("Missing or escaping source-certificate artifact: " + name)
        return path

    def add(name, expected=None):
        path = local_file(name)
        actual = digest(path)
        if expected is not None and (not isinstance(expected, str)
                or not re.fullmatch(r"[0-9a-f]{64}", expected) or actual != expected):
            raise ValueError("Stale or invalid source-certificate artifact hash: " + name)
        if name in files and files[name] != actual:
            raise ValueError("Source-certificate artifact changed during snapshot: " + name)
        files[name] = actual
        return path

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("Duplicate source-certificate artifact JSON key: " + key)
            result[key] = value
        return result

    def read(path):
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
        if not isinstance(value, dict):
            raise ValueError("Expected source-certificate artifact JSON object: " + str(path))
        return value

    def reference(value, label):
        if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
            raise ValueError("Invalid source-certificate " + label + " reference")
        if not isinstance(value["sha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["sha256"]):
            raise ValueError("Invalid source-certificate " + label + " hash")
        return add(value["path"], value["sha256"])

    metadata = read(add("metadata/results.json"))
    if "verification_current" not in metadata:
        return files
    current = metadata["verification_current"]
    if not isinstance(current, dict):
        raise ValueError("Invalid current source-certificate selection")
    if "source_certificate" not in current:
        return files
    name = current["source_certificate"]
    if not isinstance(name, str) or PurePosixPath(name).suffix != ".json":
        raise ValueError("Invalid current source-certificate selection")
    certificate_path = add(name)
    certificate = read(certificate_path)
    historical_lakefile = None
    schema = certificate.get("schema_version")
    if type(schema) is int and schema == 2:
        historical_lakefile = reference(certificate.get("historical_lakefile"), "historical Lake file")
        certificate_path = reference(certificate.get("base_certificate"), "base certificate")
        certificate = read(certificate_path)
        schema = certificate.get("schema_version")
    if type(schema) is not int or schema != 1:
        raise ValueError("Unsupported source-certificate artifact schema")

    summary = read(reference(certificate.get("build_summary"), "build summary"))
    reference(certificate.get("audit_log"), "audit log")
    comparison = read(reference(certificate.get("public_type_comparison"), "public-type comparison"))
    reference(comparison.get("checker"), "public-type checker")
    if (not isinstance(comparison.get("after_export_sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", comparison["after_export_sha256"])):
        raise ValueError("Invalid source-certificate public-type export hash")
    add(comparison.get("after_export_path"), comparison.get("after_export_sha256"))

    # Proof and challenge sources already have their complete current inventories
    # in bindings(). Include the measured driver inputs as gate dependencies too.
    drivers = summary.get("source_hashes_before")
    if not isinstance(drivers, dict) or not drivers:
        raise ValueError("Missing source-certificate measured input bindings")
    proofs = {p.relative_to(ROOT).as_posix() for p in (ROOT / "Nonadditivity").rglob("*.lean")}
    proofs.update(("Nonadditivity.lean", "Audit.lean", "All.lean"))
    for driver, expected in drivers.items():
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("Invalid source-certificate measured input hash: " + driver)
        if driver in proofs:
            continue
        if driver == "lakefile.toml" and historical_lakefile is not None:
            if digest(historical_lakefile) != expected:
                raise ValueError("Historical Lake file differs from source-certificate measured inputs")
        else:
            add(driver, expected)
    if any(digest(local_file(name)) != sha for name, sha in files.items()):
        raise ValueError("Source-certificate artifacts changed during snapshot")
    return files


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
        "scripts/check_challenges.py", "requirements-validation.txt", "scripts/source_certificate.py",
        "paper/nonadditivity.tex", "paper/arxiv-v2.json", "verification/manuscript-v2-20261008/source.tar.gz")]
    artifacts += sorted((ROOT / "ComparatorChallenges").glob("*.lean"))
    artifacts += sorted((ROOT / "ComparatorChallenges").glob("*.json"))
    artifact_hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(artifacts)}
    artifact_hashes.update(certificate_artifacts())
    return {"proof_source_sha256": {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(sources)},
            "artifact_sha256": dict(sorted(artifact_hashes.items()))}


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
