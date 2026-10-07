#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Finish one observed Linux capture after its recorder's axiom-parser failure.

No Lean command runs. The failed GitHub job remains a failure. Whole-artifact,
Git/source, command, generated-source and retained-output checks precede a new
mechanical record. The normal recorder supplies record construction/validation.
"""
from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[2]
EXECUTION = "38b360705c55fe4ee28e52f6cc493495fb7c1955"
RUN_ID = 37577412179
ARTIFACT_SHA256 = "d42a68ff1cbf3b3a4062cdd117fabbe5eac73de367e2155a061c145d4d543f61"
JOB_RECORD = "verification/github-actions-release-all-38b36070.json"
OUT = "verification/statement-audit-20261007"
ORIGINAL = OUT + "/record_checks.executed-38b36070.py"
RECEIPT = OUT + "/recovery.json"
PUBLIC_TYPES = "verification/elaboration-20261006/public-types.json"
ERROR = "STATEMENT DELTA CAPTURE FAILED: The root axiom probe did not record exactly the six permitted closures"
RECORDER = ROOT / OUT / "record_checks.py"
record = {"__file__": str(RECORDER), "__name__": "statement_recovery_recorder"}
exec(compile(RECORDER.read_bytes(), str(RECORDER), "exec"), record)
check = record["namespace"]
require = check["require"]


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def object_json(raw: bytes, label: str) -> dict:
    value = json.loads(raw.decode("utf-8"), object_pairs_hook=check["_unique_object"])
    require(isinstance(value, dict), "Expected recovery JSON object: " + label)
    return value


def verified_archive(path: Path, artifact: dict) -> dict[str, bytes]:
    raw = path.read_bytes()
    require(sha(raw) == artifact["sha256"] and len(raw) == artifact["size_in_bytes"],
            "Recovery ZIP differs from the retained GitHub artifact")
    entries = {}
    with zipfile.ZipFile(path) as archive:
        for item in archive.infolist():
            name = item.filename
            relative = PurePosixPath(name)
            require(not relative.is_absolute() and "\\" not in name and ":" not in name
                    and all(part not in {"", ".", ".."} for part in name.split("/"))
                    and name not in entries and not item.is_dir()
                    and (item.external_attr >> 16) & 0o170000 != 0o120000,
                    "Unsafe or duplicate recovery ZIP entry: " + name)
            entries[name] = archive.read(item)
    return entries


def commit_blobs(names: set[str]) -> dict[str, bytes]:
    ordered = sorted(names)
    request = "".join(EXECUTION + ":" + name + "\n" for name in ordered).encode()
    result = subprocess.run(["git", "cat-file", "--batch"], input=request, cwd=ROOT,
                            capture_output=True, check=True)
    raw, offset, result = result.stdout, 0, {}
    for name in ordered:
        end = raw.index(b"\n", offset)
        header = raw[offset:end].split()
        require(len(header) == 3 and header[1] == b"blob" and header[2].isdigit(),
                "Execution commit lacks required input: " + name)
        size = int(header[2])
        offset = end + 1
        result[name] = raw[offset:offset + size]
        require(len(result[name]) == size and raw[offset + size:offset + size + 1] == b"\n",
                "Incomplete execution-commit input: " + name)
        offset += size + 1
    require(offset == len(raw), "Unexpected execution-commit output")
    return result


def match_current_inputs(blobs: dict[str, bytes], original_recorder: bytes) -> dict[str, str]:
    recorder_name = OUT + "/record_checks.py"
    require(original_recorder == blobs[recorder_name], "Archived recorder differs from the execution commit")
    for name, raw in blobs.items():
        if name != recorder_name:
            require(check["local_file"](ROOT, name).read_bytes() == raw,
                    "Current recovery input differs from the execution commit: " + name)
    return {name: sha(raw) for name, raw in blobs.items()}


def check_root_failure_flow(original: bytes) -> list[str]:
    """Support the root exit-code inference from the exact executed driver."""
    tree = ast.parse(original)
    functions = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    driver = functions["main"]
    calls = [node for node in ast.walk(driver) if isinstance(node, ast.Call)]
    root_calls = [node for node in calls if isinstance(node.func, ast.Name) and node.func.id == "run"
                  and isinstance(node.args[0], ast.List) and len(node.args[0].elts) == 2
                  and isinstance(node.args[0].elts[0], ast.Constant) and node.args[0].elts[0].value == "./lean.sh"]
    require(len(root_calls) == 1, "Original recorder has no unique root probe command")
    root_call = root_calls[0]
    root_argument = root_call.args[0].elts[1]
    require(isinstance(root_argument, ast.BinOp) and isinstance(root_argument.op, ast.Add)
            and isinstance(root_argument.left, ast.Name) and root_argument.left.id == "OUT"
            and isinstance(root_argument.right, ast.Constant) and root_argument.right.value == "/Roots.lean",
            "Original root command differs from the retained probe")
    failure = [node for node in calls if isinstance(node.func, ast.Name) and node.func.id == "require"
               and any(isinstance(arg, ast.Constant) and arg.value == ERROR.split(": ", 1)[1]
                       for arg in node.args)]
    require(len(failure) == 1 and root_call.lineno < failure[0].lineno,
            "Recorded failure does not establish that the root probe returned")
    run_source = ast.get_source_segment(original.decode(), functions["run"])
    require("if result.returncode:" in run_source and "raise ValueError" in run_source
            and '"exit_code": result.returncode' in run_source,
            "Original recorder does not reject a nonzero root-command exit")
    return ["./lean.sh", OUT + "/Roots.lean"]


def statement_commands(entries: dict[str, bytes], report: dict) -> tuple[list[dict], set[str]]:
    require(report.get("status") == "passed" and report.get("method")
            == "local_lean_elaboration_and_solution_against_explicit_expected_type"
            and report.get("baseline_modules_recompiled") is False
            and report.get("comparator_execution") == report.get("nanoda_execution") == "not_run"
            and report.get("theorems_checked") == 6 and report.get("challenge_modules_checked") == 5,
            "Recovery statement report has unexpected status or scope")
    checker_name = "scripts/check_challenges.py"
    helper = {"__file__": str(ROOT / checker_name), "__name__": "recovered_statement_source_checker"}
    exec(compile(check["local_file"](ROOT, checker_name).read_bytes(), checker_name, "exec"), helper)
    commands, retained, seen, roots = [], {OUT + "/challenge-checks.json", OUT + "/check-challenges.log"}, set(), set()
    checks = report.get("checks")
    require(isinstance(checks, list) and len(checks) == 5, "Recovery statement report has incomplete cases")
    for item in checks:
        name = item.get("config")
        require(name in check["CONFIGS"] and name not in seen, "Wrong or duplicate recovery configuration")
        seen.add(name)
        stem = Path(name).stem
        config = check["read_json"](ROOT, name)
        source = str(Path(name).with_suffix(".lean"))
        generated = ".lake/challenge-checks/StatementChecks/" + stem + ".lean"
        require(item.get("config_sha256") == record["digest"](name)
                and item.get("challenge_source") == source
                and item.get("challenge_source_sha256") == record["digest"](source)
                and item.get("theorem_names") == config["theorem_names"]
                and item.get("generated_statement_check") == generated,
                "Recovery statement source/configuration binding differs: " + name)
        require(not roots.intersection(item["theorem_names"]), "Duplicate recovered theorem target")
        roots.update(item["theorem_names"])
        archived_source = OUT + "/" + stem + ".lean"
        expected_source = helper["proof_check_source"]((ROOT / source).read_text(), config, stem).encode()
        require(entries[archived_source] == expected_source,
                "Recovered generated check differs from the exact expected source: " + name)
        retained.add(archived_source)
        for field, argv, suffix in (
            ("challenge_elaboration", ["./lean.sh", "-o", ".lake/challenge-checks/expected/" + stem + ".olean", source], "_expected.log"),
            ("proof_against_expected_statement", ["./lean.sh", "--root=.lake/challenge-checks", generated], "_statement.log"),
        ):
            child = item.get(field)
            original_log = ".lake/challenge-checks/" + stem + suffix
            archived_log = OUT + "/" + stem + suffix
            require(isinstance(child, dict) and child.get("status") == "passed"
                    and type(child.get("exit_code")) is int and child["exit_code"] == 0
                    and child.get("command") == argv and child.get("log") == original_log,
                    "Recovered child command did not pass exactly as recorded: " + name + ": " + field)
            require(archived_log in entries, "Missing recovered child command log: " + archived_log)
            if field == "proof_against_expected_statement":
                require(not entries[archived_log].strip(), "Successful expected-type proof emitted unexpected diagnostics")
            commands.append({**child, "log": archived_log, "execution_log": original_log})
            retained.add(archived_log)
    require(seen == set(check["CONFIGS"]) and roots == set(check["current_targets"](ROOT)),
            "Recovered statement commands do not cover exactly the configured roots")
    expected_progress = "".join(Path(name).stem + ": expected statement and solution/type check passed\n"
                                for name in sorted(check["CONFIGS"]))
    expected_progress += "Saved .lake/challenge-checks.json. Comparator execution remains not_run.\n"
    require(entries[OUT + "/check-challenges.log"].decode() == expected_progress,
            "Recovered statement driver log does not record complete success")
    return commands, retained


def recover(artifact_path: Path, dry_run: bool = False) -> None:
    require(not (ROOT / record["DELTA"]).exists() and not (ROOT / OUT / "checks.json").exists()
            and not (ROOT / check["CURRENT_AUDIT_PATH"]).exists(), "Preserve existing statement records")
    job = check["read_json"](ROOT, JOB_RECORD)
    require(job.get("commit") == EXECUTION and job.get("run_id") == RUN_ID and job.get("run_attempt") == 1
            and job.get("status") == "completed" and job.get("conclusion") == "failure"
            and job["artifact"]["sha256"] == ARTIFACT_SHA256,
            "Recovery requires the exact retained failed GitHub execution")
    stages = job["verification_stages"]
    require(all(stages[name]["status"] == "passed" for name in ("all_mode", "portable_archive", "declaration_export"))
            and stages["statement_capture"]["status"] == "failed"
            and stages["statement_capture"]["error"] == ERROR
            and stages["statement_capture"]["statement_manifest_published"] is False,
            "Recovery is not the observed post-command axiom-parser failure")
    excerpt_path = "verification/" + job["log_excerpt"]
    excerpt = check["local_file"](ROOT, excerpt_path).read_bytes()
    require(sha(excerpt) == job["log_excerpt_sha256"] and ERROR in excerpt.decode(),
            "Retained failed-job excerpt differs")
    entries = verified_archive(artifact_path, job["artifact"])
    original_name = OUT + "/record_checks.py"
    original = entries[original_name]
    parent = check["read_json"](ROOT, check["AUDIT_PATH"])
    extras = {record["REPORT"], OUT + "/Roots.lean", original_name, OUT + "/delta-review.json",
              OUT + "/proof-source-delta.patch", "verification/check_statement_audit.py",
              "verification/elaboration-20261006/dead-code.json", PUBLIC_TYPES,
              "scripts/compare_public_types.py", check["AUDIT_PATH"]}
    blobs = commit_blobs(set(parent["source_bindings"]) | extras)
    execution_inputs = match_current_inputs(blobs, original)
    require(check["required_sources"](ROOT) <= parent["source_bindings"].keys(), "Recovery proof inventory changed")
    for name in extras & entries.keys():
        require(entries[name] == blobs[name], "Artifact review/probe input differs from execution commit: " + name)
    sys.path.insert(0, str(ROOT / "verification"))
    import check_reports
    portable = check_reports.load_records()
    portable_names = set()
    for proof_report in portable.values():
        require(proof_report["git_commit"] == EXECUTION, "Portable report identifies a different execution")
        portable_names.update(proof_report["proof_source_sha256"] | proof_report["artifact_sha256"])
    portable_blobs = commit_blobs(portable_names)
    for relative, raw in portable_blobs.items():
        require(sha(raw) == record["digest"](relative),
                "Portable input differs from the actual execution: " + relative)
    for item in job["retained_portable_evidence"].values():
        require(entries[item["path"]] == check["local_file"](ROOT, item["path"]).read_bytes()
                and sha(entries[item["path"]]) == item["sha256"], "Retained portable evidence changed")
    # Check all selected portable bytes, including the two logs omitted by the job's concise listing.
    for name in check_reports.EVIDENCE_FILES | {"run-summary.json"}:
        relative = check_reports.portable_directory() + "/" + name
        require(entries[relative] == check["local_file"](ROOT, relative).read_bytes(),
                "Current portable output differs from the GitHub artifact: " + relative)
    capture = stages["statement_capture"]
    require(capture["statement_report_artifact_entry"] == OUT + "/challenge-checks.json"
            and capture["root_probe_artifact_entry"] == OUT + "/roots.log"
            and sha(entries[capture["statement_report_artifact_entry"]]) == capture["statement_report_sha256"]
            and sha(entries[capture["root_probe_artifact_entry"]]) == capture["root_probe_sha256"],
            "Recovered statement report/root log differs from retained job evidence")
    challenge_report = object_json(entries[OUT + "/challenge-checks.json"], "statement report")
    commands, retained = statement_commands(entries, challenge_report)
    roots = check["current_targets"](ROOT)
    root_text = entries[OUT + "/roots.log"].decode()
    axioms = record["parse_root_axioms"](root_text, roots)
    require(not re.search(r"\berror:|\bsorryAx\b|declaration uses 'sorry'", root_text), "Recovered root probe contains an error/hole")
    root_argv = check_root_failure_flow(original)
    commands.append({"command": root_argv, "exit_code": 0, "log": OUT + "/roots.log",
                     "exit_code_provenance": "Inferred from exact original run() flow: this observed parser failure occurs only after run() rejects nonzero exits and returns."})
    retained.add(OUT + "/roots.log")
    for name in retained:
        require(entries[name] == check["local_file"](ROOT, name).read_bytes(),
                "Retained raw capture output differs from the original artifact: " + name)
    sources = {name: execution_inputs[name] for name in parent["source_bindings"]}
    review = check["read_json"](ROOT, OUT + "/delta-review.json")
    audit = record["make_audit"](EXECUTION, PUBLIC_TYPES, parent, record["digest"](check["AUDIT_PATH"]), sources, review)
    check["check_delta"](ROOT, audit, sources, audit["report_bindings"])
    if dry_run:
        print("RECOVERY GUARDS PASSED: exact Linux artifact, execution inputs, ten child commands and six root closures; no files written or Lean rerun.")
        return
    require(not (ROOT / ORIGINAL).exists() and not (ROOT / RECEIPT).exists(), "Preserve existing recovery provenance")
    (ROOT / ORIGINAL).write_bytes(original)
    provenance = {
        "schema_version": 1, "mode": "completed_commands_recovered_after_recorder_failure",
        "recovered_at_utc": datetime.now(timezone.utc).isoformat(), "execution_commit": EXECUTION,
        "github_run_id": RUN_ID, "overall_job_conclusion": "failure", "proof_commands_rerun": False,
        "artifact": job["artifact"], "artifact_entries_sha256": {name: sha(raw) for name, raw in sorted(entries.items())},
        "job_record": {"path": JOB_RECORD, "sha256": record["digest"](JOB_RECORD)},
        "job_excerpt": {"path": excerpt_path, "sha256": record["digest"](excerpt_path)},
        "executed_recorder": {"execution_path": original_name, "retained_path": ORIGINAL, "sha256": sha(original)},
        "execution_inputs": execution_inputs,
        "root_exit_code_basis": commands[-1]["exit_code_provenance"],
        "driver_argv": "The original sys.executable wrapper argv was not retained and is not reconstructed. Ten child argv are retained exactly; root argv follows the exact executed driver.",
        "scope": "Recovery parses completed output and publishes missing evidence. The failed GitHub job is not upgraded; website generation was skipped in that job.",
    }
    record["write_json"](RECEIPT, provenance)
    current_input_names = set(execution_inputs) - {original_name}
    current_input_names |= {ORIGINAL, RECEIPT, JOB_RECORD, excerpt_path, original_name, OUT + "/recover_checks.py"}
    inputs = {name: record["digest"](name) for name in sorted(current_input_names)}
    logs = {name: sha(entries[name]) for name in sorted(retained)}
    evidence = record["make_evidence"](EXECUTION, sources, inputs, logs, commands, roots, axioms)
    evidence["checked_at_utc"] = job["jobs"][0]["steps"][8]["completed_at"]
    evidence["recorded_at_utc"] = provenance["recovered_at_utc"]
    evidence["capture_provenance"] = {"path": RECEIPT, "sha256": record["digest"](RECEIPT)}
    evidence["notes"] += ["Completed Linux commands recovered after recorder failure; no rerun.",
                          "Source commit is the actual execution commit, not the later recovery-tool checkout.",
                          "Original executed recorder retained separately. Current recorder/recovery script hashes bind the publication tools only.",
                          "Overall GitHub workflow remains failed; its skipped website stage is not claimed as successful."]
    record["publish_records"](evidence, audit)
    print("RECOVERED STATEMENT RECORDS PUBLISHED: actual Linux commands at " + EXECUTION + "; no proof command rerun.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, required=True, help="Downloaded original GitHub artifact ZIP")
    parser.add_argument("--dry-run", action="store_true", help="Validate all recovery guards without publishing")
    args = parser.parse_args()
    try:
        recover(args.artifact, args.dry_run)
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError, zipfile.BadZipFile) as error:
        print("STATEMENT RECOVERY FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
