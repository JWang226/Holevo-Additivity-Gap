#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Validate published portable records against the currently checked sources.

This validates evidence freshness and scope; it does not re-execute proof checks.
"""
import json
from pathlib import Path
import kernel_common as common

RECORDS = {"comparator": "verification/portable-20261002/comparator-result.json",
           "nanoda": "verification/portable-20261002/nanoda-result.json"}


def load_records():
    bindings = common.bindings()
    expected = {name: json.loads((common.ROOT / name).read_text())["theorem_names"]
                for name in common.DEFAULT_CONFIGS}
    modes = {"comparator": "unsandboxed_comparator_lean_replay",
             "nanoda": "unsandboxed_independent_kernel"}
    records = {}
    for name, filename in RECORDS.items():
        record = json.loads((common.ROOT / filename).read_text())
        if (record["status"] != "passed" or record["mode"] != modes[name]
                or record["sandboxed"] is not False
                or record["upstream_sandboxed_comparator"] != "not_run"
                or record["comparator_commit"] != common.REVISION
                or record["checker_dependencies"] != common.DEPENDENCIES
                or set(record["permitted_axioms"]) != common.AXIOMS
                or any(record[field] != hashes for field, hashes in bindings.items())
                or set(record["cases"]) != set(expected)):
            raise ValueError("Portable evidence is stale or has unexpected scope: " + filename)
        for case, names in expected.items():
            item = record["cases"][case]
            if (item["status"] != "passed" or item["theorem_names"] != names
                    or item["config_sha256"] != common.digest(common.ROOT / case)):
                raise ValueError("Unexpected recorded theorem targets: " + case)
        if name == "nanoda":
            pin = json.loads((common.ROOT / "verification/nanoda/toolchain.json").read_text())
            receipt = record["nanoda_build_receipt"]
            if (record["nanoda"] != pin or not record["unpermitted_axiom_hard_error"]
                    or not record["unknown_pp_declar_hard_error"]
                    or not all(c["exported_theorems_present"] for c in record["cases"].values())
                    or record["nanoda_binary_source"] != "built_from_recorded_source_and_rust_pins"
                    or receipt["pin"] != pin
                    or receipt["binary_sha256"] != record["nanoda_binary_sha256"]):
                raise ValueError("Unexpected Nanoda options or build provenance")
        records[name] = record
    summary = json.loads((common.ROOT / "verification/portable-20261002/run-summary.json").read_text())
    if (summary["status"] != "passed" or summary["mode"] != "all"
            or summary["sandboxed"] is not False
            or summary["project_modules_rebuilt"] != 369
            or summary["audited_project_declarations"] != 9107
            or summary["audited_theorem_constants"] != 7219
            or summary["control_status"] != "passed"
            or len(summary["controls"]) != 13
            or summary["challenge_configurations"] != 5
            or summary["theorem_roots"] != 6):
        raise ValueError("Unexpected portable full-run summary")
    for filename, sha in summary["evidence_sha256"].items():
        if common.digest(common.ROOT / "verification/portable-20261002" / filename) != sha:
            raise ValueError("Portable evidence log/report differs: " + filename)
    return records


if __name__ == "__main__":
    load_records()
    print("PORTABLE EVIDENCE FRESH: five configurations, six roots, Comparator/Lean replay and Nanoda.")
