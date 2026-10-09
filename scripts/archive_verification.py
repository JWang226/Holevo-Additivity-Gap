#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Retain an actually successful all-mode run, with its original input bindings."""
from datetime import datetime, timezone
import argparse
import json
from pathlib import Path
import platform
import re
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification"))
import kernel_common as common
import check_reports


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-log", type=Path, required=True)
    args = parser.parse_args()
    published = False
    staged = None
    try:
        full_log = args.full_log.resolve()
        require(full_log.is_relative_to(ROOT / ".verify-work"), "Full log must be in .verify-work")
        text = full_log.read_text()
        directories = re.findall(r"^Fresh logs: (.+)$", text, re.MULTILINE)
        require(len(directories) == 1, "Full log must identify exactly one new run")
        run = Path(directories[0]).resolve()
        require(run.is_relative_to(ROOT / ".verify-work") and run.name.startswith("run-"),
                "Run directory is outside .verify-work")
        require((run / "result.txt").read_text().strip() == "VERIFICATION PASSED: all",
                "All requested verification stages did not pass")
        require("VERIFICATION FAILED:" not in text and text.rstrip().endswith(str(run)),
                "Full log does not end with successful wrapper completion")
        info = read_json(run / "run-info.json")
        require(info["mode"] == "all" and info["sandboxed"] is False
                and info["nanoda_binary_source"] == "build_from_recorded_pin",
                "Expected full unsandboxed run with pinned Nanoda build")
        snapshot = common.bindings()
        reports = {name: read_json(run / (name + "-result.json"))
                   for name in ("comparator", "nanoda")}
        for name, report in reports.items():
            require(report["status"] == "passed"
                    and all(report[key] == value for key, value in snapshot.items()),
                    "Current inputs differ from the completed " + name + " run")
        lean_log = (run / "lean.log").read_text()
        builds = re.findall(r"^BUILD PASSED: (\d+) project modules\.$", lean_log, re.MULTILINE)
        audits = re.findall(r"^AUDIT PASSED: (\d+) project declarations, (\d+) theorems;", lean_log, re.MULTILINE)
        require(builds == ["369"] and audits == [("9107", "7219")],
                "Fresh full build and complete axiom audit were not recorded")
        require("LEAN REPRODUCTION PASSED." in lean_log,
                "Lean reproducer did not complete")
        controls_log = (run / "nanoda-controls.log").read_text()
        # The controls runner prints one final JSON object after tool diagnostics.
        start = controls_log.rfind('\n{')
        require(start >= 0, "Missing controls result")
        controls = json.loads(controls_log[start + 1:])
        require(controls["status"] == "passed" and len(controls["checks"]) == 13,
                "Acceptance/rejection controls did not all pass")
        validation = read_json(ROOT / ".lake/release-validation.json")
        check_reports.check_certificate_invocation(info, validation)
        challenges = read_json(ROOT / ".lake/challenge-checks.json")
        targets = check_reports.configured_targets()
        theorem_count = sum(len(names) for names in targets.values())
        require(validation["lean_declaration_check"] == "passed"
                and validation["unique_mapped_declarations"] == 49
                and validation["proof_source_sha256"] == snapshot["proof_source_sha256"]
                and all(validation["metadata_sha256"][key] == value for key, value
                        in snapshot["artifact_sha256"].items() if key in validation["metadata_sha256"]),
                "Fresh mapped-declaration validation is missing or stale")
        require(challenges["status"] == "passed" and challenges["theorems_checked"] == theorem_count
                and challenges["challenge_modules_checked"] == len(targets),
                "Fresh expected statement checks did not all pass")
        directory = ROOT / check_reports.portable_directory()
        require(not directory.exists(), "Preserve existing records; choose a versioned successor")
        directory.parent.mkdir(parents=True, exist_ok=True)
        staged = Path(tempfile.mkdtemp(prefix="portable-evidence-", dir=ROOT / ".verify-work"))
        files = {name: run / name for name in (
            "comparator-result.json", "comparator.log", "lean.log", "nanoda-build.json",
            "nanoda-build.log", "nanoda-controls.log", "nanoda-result.json", "nanoda.log",
            "result.txt", "run-info.json")}
        files.update({"all.log": full_log,
                      "release-validation.json": ROOT / ".lake/release-validation.json",
                      "challenge-checks.json": ROOT / ".lake/challenge-checks.json"})
        for name, source in files.items():
            shutil.copyfile(source, staged / name)
        summary = {
            "schema_version": 1, "status": "passed", "mode": "all", "sandboxed": False,
            "completed_at_utc": datetime.now(timezone.utc).isoformat(),
            "platform": platform.platform(), "project_modules_rebuilt": int(builds[0]),
            "audited_project_declarations": int(audits[0][0]),
            "audited_theorem_constants": int(audits[0][1]), "mapped_declarations_checked": 49,
            "challenge_configurations": len(targets), "theorem_roots": theorem_count,
            "permitted_axioms": sorted(common.AXIOMS),
            "dependency_boundary": "Pinned prebuilt Mathlib/dependency cache reused; all project modules rebuilt from source.",
            "command": "bash scripts/verify.sh all --source-certificate " + info["source_certificate"],
            "kernel_checks": "Pinned Comparator statement comparison, Lean replay and Nanoda independent kernel; unsandboxed.",
            "control_status": controls["status"], "controls": controls["checks"],
            "upstream_sandboxed_comparator": "not_run",
            "evidence_sha256": {name: common.digest(staged / name) for name in sorted(files)},
        }
        (staged / "run-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        staged.rename(directory)
        published = True
        check_reports.load_records()
        print("Retained verified current-source portable evidence: " + str(directory.relative_to(ROOT)))
        return 0
    except (OSError, ValueError, KeyError) as error:
        if published:
            directory.rename(staged)
        print("VERIFICATION ARCHIVE FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
