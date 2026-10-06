#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Fixed operations for one trusted, public-repository elaboration runner.

Copy this helper outside the checkout before running. JSON never contains shell
commands: it chooses only serial warm A/B profiles or the final after snapshot.
Fetches are public HTTPS, checkout credentials are not persisted, and candidate
trees may change only existing own Lean source files. Compiler, dependencies,
build drivers and this measurement implementation remain byte-identical.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import socket
import statistics
import subprocess
import sys
import time

PUBLIC_REPO = "https://github.com/JWang226/Holevo-Additivity-Gap.git"
CONTROL_FILE = "elaboration-request.json"
SHA = re.compile(r"[0-9a-f]{40}\Z")
REF = re.compile(r"[A-Za-z0-9][A-Za-z0-9_./-]{0,160}\Z")


def utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def save(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def command(root: Path, args: list[str], *, check=True) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=root, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=check)


def git(root: Path, *args: str) -> str:
    return command(root, ["git", *args]).stdout.strip()


def safe_ref(ref: str) -> str:
    if not REF.fullmatch(ref) or ".." in ref or ref.endswith("/") or "@{" in ref:
        raise ValueError("Invalid branch ref")
    return ref


def fetch(root: Path, ref: str, destination: str) -> str:
    safe_ref(ref)
    git(root, "-c", "credential.helper=", "fetch", "--no-tags", PUBLIC_REPO,
        "+refs/heads/" + ref + ":refs/remotes/elaboration/" + destination)
    return git(root, "rev-parse", "refs/remotes/elaboration/" + destination)


def load_harness(root: Path):
    spec = importlib.util.spec_from_file_location("elaboration_harness", root / "scripts/elaboration_test.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader
    spec.loader.exec_module(module)
    return module


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def request_schema(value: dict, state: dict) -> None:
    if not isinstance(value, dict):
        raise ValueError("Request must be an object")
    common = {"schema_version", "sequence", "mode", "baseline_sha"}
    expected = (common | {"candidate_sha", "modules", "repetitions"}
                if value.get("mode") == "profile" else common | {"after_sha"})
    if set(value) != expected or value.get("schema_version") != 1:
        raise ValueError("Request fields or schema version do not match")
    if type(value["sequence"]) is not int or value["sequence"] != state["next_sequence"]:
        raise ValueError("Request sequence must equal " + str(state["next_sequence"]))
    if value["baseline_sha"] != state["baseline_sha"]:
        raise ValueError("Request baseline SHA does not match measured baseline")
    if value["mode"] not in ("profile", "final"):
        raise ValueError("Allowed modes: profile, final")
    field = "candidate_sha" if value["mode"] == "profile" else "after_sha"
    if not isinstance(value[field], str) or not SHA.fullmatch(value[field]):
        raise ValueError("A complete lowercase commit SHA is required")
    if value["mode"] == "profile":
        modules = value["modules"]
        if (not isinstance(modules, list) or not 1 <= len(modules) <= 10
                or any(not isinstance(item, str) for item in modules)
                or len(set(modules)) != len(modules)
                or set(modules) - state["modules"].keys()):
            raise ValueError("Supply 1..10 distinct baseline own modules")
        if type(value["repetitions"]) is not int or value["repetitions"] != 3:
            raise ValueError("A/B uses exactly three runs of each variant")


def changed_sources(root: Path, baseline: str, candidate: str, modules: dict, *, require_change=True) -> set[str]:
    # Check the complete tree, not just a path-filtered diff: no executable,
    # dependency pin, configuration, helper, symlink or renamed file may change.
    rows = git(root, "diff", "--raw", "--no-abbrev", "--no-renames", baseline, candidate).splitlines()
    reverse = {path: module for module, path in modules.items()}
    changed = set()
    for row in rows:
        details, path = row.split("\t", 1)
        old_mode, new_mode, _old_sha, _new_sha, status = details.removeprefix(":").split()
        if status != "M" or old_mode != "100644" or new_mode != "100644" or path not in reverse:
            raise ValueError("Candidate changes an unapproved tree entry: " + path)
        changed.add(reverse[path])
    if require_change and not changed:
        raise ValueError("Candidate contains no own Lean source change")
    return changed


def ancestor(root: Path, baseline: str, candidate: str) -> None:
    git(root, "cat-file", "-e", candidate + "^{commit}")
    if command(root, ["git", "merge-base", "--is-ancestor", baseline, candidate], check=False).returncode:
        raise ValueError("Candidate must descend from the measured baseline")


def checkout(root: Path, sha: str) -> None:
    # The runner is dedicated and the helper is frozen outside its checkout.
    # Never reset or delete caches. Any dirty tracked source is an error.
    if git(root, "status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError("Tracked files became dirty outside the continuation")
    git(root, "-c", "core.hooksPath=/dev/null", "checkout", "--detach", sha)


def artifact_guard(root: Path, state: dict, harness) -> None:
    if harness.own_artifact_manifest(root) != state["own_artifacts"]:
        raise RuntimeError("Own artifacts changed outside the fixed full-build stages")
    for path, expected in state["dependency_artifacts"].items():
        if harness.stat_entry(Path(path)) != expected:
            raise RuntimeError("Upstream compiled cache changed: " + path)
    if digest(Path(state["compiler"])) != state["compiler_sha256"]:
        raise RuntimeError("Pinned compiler executable changed")
    if digest(Path(state["time_bin"])) != state["time_sha256"]:
        raise RuntimeError("GNU time executable changed")
    if socket.gethostname() != state["host"]:
        raise RuntimeError("Continuation moved to another host")


def output(name: str, value: str) -> None:
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a") as file:
            file.write(name + "=" + value + "\n")


def profile_once(root: Path, directory: Path, module: str, state: dict, harness) -> dict:
    directory.mkdir(parents=True)
    (directory / "logs").mkdir()
    (directory / "timings").mkdir()
    config = {"root": str(root), "output": str(directory), "compiler": state["compiler"],
              "time_bin": state["time_bin"], "phase": "profile", "modules": state["modules"],
              "source_stats": harness.source_stat_manifest(root),
              "source_hashes": harness.source_hash_manifest(root)}
    save(directory / "wrapper-config.json", config)
    save(directory / "artifact-state.json", harness.own_artifact_manifest(root))
    wrapper = directory / "timed-compiler"
    wrapper.write_text("#!" + sys.executable + "\nimport subprocess,sys\n"
                       "sys.exit(subprocess.run(" + repr([sys.executable,
                       str(root / "scripts/elaboration_test.py"), "_compiler",
                       str(directory / "wrapper-config.json")]) + " + sys.argv[1:]).returncode)\n")
    wrapper.chmod(0o755)
    env = os.environ.copy()
    env.update({"LC_ALL": "C", "NONADDITIVITY_LEAN": str(wrapper),
                "NONADDITIVITY_PARALLEL": "0",
                "NONADDITIVITY_LEAN_PATH": str(Path(state["compiler"]).parent.parent / "lib/lean")})
    arguments = [str(root / "lean.sh"), "--profile", state["modules"][module]]
    try:
        rc = harness.guarded_subprocess(arguments, directory / "driver.log", config, env)
        record = json.loads((directory / "measurements.jsonl").read_text().splitlines()[-1])
        record["valid"] = (rc == 0 and not record["guard_errors"] and bool(record.get("profile", {}).get("phases_s")))
    except Exception as error:
        record = {"module": module, "valid": False, "error": str(error)}
    save(directory / "result.json", record)
    return record


def summarize(records: list[dict], modules: list[str]) -> dict:
    result = {}
    for module in modules:
        grouped = {variant: [item["record"] for item in records
                   if item["variant"] == variant and item["module"] == module]
                   for variant in ("baseline", "candidate")}
        metrics = {}
        phases = set()
        for rows in grouped.values():
            for row in rows:
                phases.update(row.get("profile", {}).get("phases_s", {}))
        for name in ("wall_s", "cpu_s", "user_s", "sys_s", *sorted(phases)):
            values = {}
            for variant, rows in grouped.items():
                raw = [(row.get("timing", {}).get(name) if name in {"wall_s", "cpu_s", "user_s", "sys_s"}
                        else row.get("profile", {}).get("phases_s", {}).get(name)) for row in rows]
                raw = [number for number in raw if number is not None]
                values[variant] = {"runs": raw, "median": statistics.median(raw) if raw else None,
                                   "mean": statistics.mean(raw) if raw else None}
            before, after = values["baseline"]["median"], values["candidate"]["median"]
            values["median_delta_s"] = after - before if before is not None and after is not None else None
            values["median_change_percent"] = 100 * (after / before - 1) if before and after is not None else None
            metrics[name] = values
        result[module] = {"all_runs_valid": all(row.get("valid") for rows in grouped.values() for row in rows),
                          "metrics": metrics}
    return result


def profile_pair(root: Path, directory: Path, request: dict, state: dict, harness) -> dict:
    candidate = request["candidate_sha"]
    ancestor(root, state["baseline_sha"], candidate)
    changed = changed_sources(root, state["baseline_sha"], candidate, state["modules"])
    requested = set(request["modules"])
    if changed - requested:
        raise ValueError("All changed source modules must be included in the requested profiles")
    checkout(root, candidate)
    graph, _ = harness.import_graph(root, state["modules"])
    # Existing baseline artifacts are valid only for unchanged dependencies.
    # Support independent leaf interventions, never stale dependency profiles.
    def dependencies(module: str, seen=None) -> set[str]:
        seen = set() if seen is None else seen
        for dependency in graph[module]:
            if dependency not in seen:
                seen.add(dependency)
                dependencies(dependency, seen)
        return seen
    for module in requested:
        if changed & dependencies(module):
            raise ValueError("Changed imported module would make this warm profile use stale artifacts: " + module)
    records = []
    for repetition in range(3):
        order = ("baseline", "candidate") if repetition % 2 == 0 else ("candidate", "baseline")
        for variant in order:
            sha = state["baseline_sha"] if variant == "baseline" else candidate
            checkout(root, sha)
            artifact_guard(root, state, harness)
            for module in request["modules"]:
                leaf = directory / f"run-{repetition + 1}-{variant}" / module.replace(".", "_")
                record = profile_once(root, leaf, module, state, harness)
                records.append({"variant": variant, "sha": sha, "repetition": repetition + 1,
                                "module": module, "record": record})
                print(json.dumps({"event": "profile_complete", "variant": variant, "module": module,
                      "repetition": repetition + 1, "valid": record.get("valid"),
                      "timing": record.get("timing"),
                      "phases_s": record.get("profile", {}).get("phases_s")}), flush=True)
                artifact_guard(root, state, harness)
    return {"records": records, "comparison": summarize(records, request["modules"])}


def initialize(args) -> None:
    root = args.root.resolve()
    harness = load_harness(root)
    before = json.loads((args.evidence / "before/summary.json").read_text())
    if before["invalid_reasons"]:
        raise RuntimeError("Baseline evidence is invalid")
    baseline = git(root, "rev-parse", "HEAD")
    if baseline != before["provenance"]["commit"]:
        raise RuntimeError("Baseline checkout no longer matches completed measurement")
    dependencies = json.loads((args.evidence / "before/dependencies-after.json").read_text())
    state = {"schema_version": 1, "baseline_sha": baseline, "host": socket.gethostname(),
             "compiler": before["provenance"]["compiler"], "time_bin": before["provenance"]["time_bin"],
             "compiler_sha256": before["provenance"]["compiler_sha256"],
             "time_sha256": before["provenance"]["time_sha256"],
             "modules": before["modules"], "own_artifacts": harness.own_artifact_manifest(root),
             "dependency_artifacts": dependencies["artifacts"], "next_sequence": 1,
             "control_ref": safe_ref(args.control_ref), "after_ref": safe_ref(args.after_ref),
             "deadline_epoch": time.time() + 7200, "created_utc": utc(), "history": []}
    save(args.state, state)
    save(args.evidence / "continuation-initial.json", state)
    print("Baseline uploaded; awaiting sequence 1 on public control branch " + state["control_ref"], flush=True)


def wait_and_run(args) -> None:
    root, evidence = args.root.resolve(), args.evidence.resolve()
    state = json.loads(args.state.read_text())
    harness = load_harness(root)
    sequence = state["next_sequence"]
    directory = evidence / "trials" / str(sequence)
    directory.mkdir(parents=True, exist_ok=False)
    output("sequence", str(sequence))
    request = None
    last_error = None
    while time.time() < state["deadline_epoch"]:
        try:
            control_sha = fetch(root, state["control_ref"], "control")
            candidate_request = json.loads(git(root, "show", control_sha + ":" + CONTROL_FILE))
            if isinstance(candidate_request, dict) and candidate_request.get("sequence", 0) < sequence:
                time.sleep(20)
                continue
            request_schema(candidate_request, state)
            request = candidate_request
            save(directory / "request.json", request)
            break
        except Exception as error:
            message = str(error)
            if message != last_error:
                print("Waiting for valid request: " + message, flush=True)
                last_error = message
            time.sleep(20)
    if request is None:
        save(directory / "result.json", {"valid": False, "error": "Overall two-hour continuation deadline expired",
                                           "last_poll_error": last_error, "finished_utc": utc()})
        raise RuntimeError("Overall two-hour continuation deadline expired")
    result = {"request": request, "started_utc": utc(), "baseline_sha": state["baseline_sha"],
              "same_host": state["host"], "helper_sha256": digest(Path(__file__))}
    try:
        artifact_guard(root, state, harness)
        if request["mode"] == "final":
            after_sha = fetch(root, state["after_ref"], "after")
            if request["after_sha"] != after_sha:
                raise ValueError("Final SHA must equal the explicit after branch head")
            ancestor(root, state["baseline_sha"], after_sha)
            changed = changed_sources(root, state["baseline_sha"], after_sha, state["modules"], require_change=False)
            checkout(root, after_sha)
            artifact_guard(root, state, harness)
            result.update({"valid": True, "after_sha": after_sha, "changed_modules": sorted(changed)})
            output("done", "true")
            output("after_sha", after_sha)
            if os.environ.get("GITHUB_ENV"):
                with open(os.environ["GITHUB_ENV"], "a") as file:
                    file.write("ELAB_FINISHED=1\nELAB_AFTER_SHA=" + after_sha + "\n")
        else:
            # Only fetch the explicit source branch, then require its complete
            # request SHA to be in the fetched object history.
            candidate_tip = fetch(root, state["after_ref"], "candidates")
            ancestor(root, request["candidate_sha"], candidate_tip)
            result.update(profile_pair(root, directory, request, state, harness))
            result["valid"] = all(row["all_runs_valid"] for row in result["comparison"].values())
    except Exception as error:
        result.update({"valid": False, "error": str(error)})
        print("Candidate request rejected or failed: " + str(error), flush=True)
    finally:
        if not result.get("after_sha"):
            checkout(root, state["baseline_sha"])
        result["finished_utc"] = utc()
        save(directory / "result.json", result)
        state["history"].append({"sequence": sequence, "mode": request["mode"],
                                  "valid": result["valid"], "result": str(directory / "result.json")})
        state["next_sequence"] += 1
        save(args.state, state)
    print(json.dumps({"event": "request_complete", "sequence": sequence, "valid": result["valid"],
                      "comparison": result.get("comparison"), "error": result.get("error")}), flush=True)


def matched_profiles(args) -> None:
    """Supplement, rather than rewrite, the after run's independently chosen top8."""
    root, evidence = args.root.resolve(), args.evidence.resolve()
    state = json.loads(args.state.read_text())
    harness = load_harness(root)
    before = json.loads((evidence / "before/summary.json").read_text())
    after = json.loads((evidence / "after/summary.json").read_text())
    if not after["valid"] or not after["comparison"]["matched_timing_setup"]:
        raise RuntimeError("After measurement does not establish a valid matched runner setup")
    after_sha = git(root, "rev-parse", "HEAD")
    if after_sha != after["provenance"]["commit"]:
        raise RuntimeError("After checkout no longer matches completed measurement")
    # Full after rebuild legitimately replaced own objects. Their completed,
    # guarded manifest becomes the immutable state for these no-output profiles.
    state["own_artifacts"] = json.loads((evidence / "after/artifacts-after.json").read_text())
    changed = changed_sources(root, state["baseline_sha"], after_sha, state["modules"], require_change=False)
    prior_modules = {row["module"] for row in before["profiles"]}
    after_modules = {row["module"] for row in after["profiles"]}
    requested = sorted((prior_modules | changed) - after_modules)
    directory = evidence / "matched-profiles"
    directory.mkdir(parents=True, exist_ok=False)
    records = []
    artifact_guard(root, state, harness)
    for module in requested:
        records.append(profile_once(root, directory / module.replace(".", "_"), module, state, harness))
        artifact_guard(root, state, harness)
    result = {"valid": all(row.get("valid") for row in records), "after_sha": after_sha,
              "requested_modules": requested, "baseline_top8_modules": sorted(prior_modules),
              "after_top8_modules": sorted(after_modules), "edited_modules": sorted(changed),
              "profiles": records, "compiler_sha256": state["compiler_sha256"],
              "time_sha256": state["time_sha256"], "host": state["host"], "finished_utc": utc(),
              "scope": "Supplemental serial no-output warm profiles; original after summary is unchanged"}
    save(directory / "summary.json", result)
    if not result["valid"]:
        raise RuntimeError("A supplemental matched profile failed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("init", "wait", "matched"))
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--state", required=True, type=Path)
    parser.add_argument("--control-ref")
    parser.add_argument("--after-ref")
    args = parser.parse_args()
    if args.operation == "init":
        if not args.control_ref or not args.after_ref:
            parser.error("init requires --control-ref and --after-ref")
        initialize(args)
    elif args.operation == "wait":
        wait_and_run(args)
    else:
        matched_profiles(args)


if __name__ == "__main__":
    main()
