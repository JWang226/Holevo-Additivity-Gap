#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Validate published portable records against the currently checked sources.

This validates evidence freshness and scope; it does not re-execute proof checks.
"""
import json
from pathlib import PurePosixPath
import re
import kernel_common as common

HISTORICAL_DIRECTORY = "verification/portable-20261002"
RECORD_FILES = {"comparator": "comparator-result.json", "nanoda": "nanoda-result.json"}
EVIDENCE_FILES = {
    "all.log", "challenge-checks.json", "comparator-result.json", "comparator.log",
    "lean.log", "nanoda-build.json", "nanoda-build.log", "nanoda-controls.log",
    "nanoda-result.json", "nanoda.log", "release-validation.json", "result.txt", "run-info.json",
}
CONTROLS = (
    "valid theorem accepted", "Comparator: valid theorem accepted",
    "missing target rejected by wrapper and kernel", "Comparator: missing target rejected",
    "non-theorem root rejected", "badAxiom rejected by real kernel axiom policy",
    "Comparator: badAxiom rejected by axiom policy", "proofHole rejected by real kernel axiom policy",
    "Comparator: proofHole rejected by axiom policy", "ill-typed proof rejected by real kernel",
    "Comparator: ill-typed proof rejected", "Comparator: mismatched expected statement rejected",
    "empty, duplicate, and malformed target selections rejected",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local_file(name):
    require(isinstance(name, str) and bool(name), "Missing portable evidence path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and "\\" not in name and ":" not in name
            and all(part not in {"", ".", ".."} for part in name.split("/")),
            "Unsafe portable evidence path: " + name)
    absolute = common.ROOT / name
    require(absolute.resolve().is_relative_to(common.ROOT.resolve()),
            "Portable evidence path escapes repository: " + name)
    if not absolute.is_file():
        raise FileNotFoundError("Missing portable evidence file: " + name)
    return absolute


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate portable JSON key: " + key)
        result[key] = value
    return result


def read_json(name):
    value = json.loads(local_file(name).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    require(isinstance(value, dict), "Expected portable JSON object: " + name)
    return value


def axiom_policy(value):
    return (isinstance(value, list) and len(value) == len(common.AXIOMS)
            and all(isinstance(item, str) for item in value) and set(value) == common.AXIOMS)


def configured_targets():
    """Read the current exact inventory; historical counts are not substitutes."""
    require(len(common.DEFAULT_CONFIGS) == len(set(common.DEFAULT_CONFIGS)),
            "Duplicate current portable configuration")
    expected, seen = {}, set()
    for name in common.DEFAULT_CONFIGS:
        names = read_json(name).get("theorem_names")
        require(isinstance(names, list) and bool(names)
                and all(isinstance(target, str) and bool(target) for target in names),
                "Invalid current portable theorem targets: " + name)
        require(len(names) == len(set(names)) and not seen.intersection(names),
                "Duplicate current portable theorem target: " + name)
        expected[name] = names
        seen.update(names)
    return expected



def portable_directory():
    """Select the explicit published evidence; never infer freshness from a date."""
    metadata = json.loads(local_file("metadata/results.json").read_text(encoding="utf-8"),
                          object_pairs_hook=unique_object)
    if not isinstance(metadata, dict):
        raise ValueError("Expected release metadata object for portable evidence selection")
    if "portable_verification_current" not in metadata:
        return HISTORICAL_DIRECTORY
    selection = metadata["portable_verification_current"]
    if not isinstance(selection, dict) or set(selection) != {"directory"}:
        raise ValueError("Invalid current portable evidence selection")
    directory = selection["directory"]
    if (not isinstance(directory, str)
            or re.fullmatch(r"verification/portable-[0-9]{8}", directory) is None
            or not (common.ROOT / directory).resolve().is_relative_to(common.ROOT.resolve())):
        raise ValueError("Unsafe current portable evidence directory")
    return directory


def check_certificate_invocation(run, validation):
    """Require the invoked source gate to be the explicitly selected gate."""
    metadata = read_json("metadata/results.json")
    current = metadata.get("verification_current", {})
    require(isinstance(current, dict), "Invalid current source-certificate selection")
    selected = current.get("source_certificate")
    require(run.get("source_certificate") == selected,
            "Portable invocation used a different source certificate")
    if selected is not None:
        sha = common.digest(local_file(selected))
        integrity = validation.get("source_integrity")
        require(isinstance(integrity, dict) and integrity.get("path") == selected
                and integrity.get("sha256") == sha,
                "Portable release validation used a different or stale source certificate")


def load_records():
    directory = portable_directory()
    bindings = common.bindings()
    for hashes in bindings.values():
        for filename in hashes:
            local_file(filename)
    expected = configured_targets()
    theorem_count = sum(len(names) for names in expected.values())
    modes = {"comparator": "unsandboxed_comparator_lean_replay",
             "nanoda": "unsandboxed_independent_kernel"}
    records = {}
    for name, basename in RECORD_FILES.items():
        filename = directory + "/" + basename
        record = read_json(filename)
        if (type(record.get("schema_version")) is not int or record["schema_version"] != 1
                or record["status"] != "passed" or record["mode"] != modes[name]
                or record["sandboxed"] is not False
                or record["upstream_sandboxed_comparator"] != "not_run"
                or record["comparator_commit"] != common.REVISION
                or record["checker_dependencies"] != common.DEPENDENCIES
                or not axiom_policy(record["permitted_axioms"])
                or any(record[field] != hashes for field, hashes in bindings.items())
                or set(record["cases"]) != set(expected)):
            raise ValueError("Portable evidence is stale or has unexpected scope: " + filename)
        for case, names in expected.items():
            item = record["cases"][case]
            if (item["status"] != "passed" or item["theorem_names"] != names
                    or item["config_sha256"] != common.digest(common.ROOT / case)):
                raise ValueError("Unexpected recorded theorem targets: " + case)
        if name == "nanoda":
            pin = read_json("verification/nanoda/toolchain.json")
            receipt = record["nanoda_build_receipt"]
            if (record["nanoda"] != pin or record["unpermitted_axiom_hard_error"] is not True
                    or record["unknown_pp_declar_hard_error"] is not True
                    or not all(c["exported_theorems_present"] is True for c in record["cases"].values())
                    or record["nanoda_binary_source"] != "built_from_recorded_source_and_rust_pins"
                    or receipt["pin"] != pin
                    or receipt["binary_sha256"] != record["nanoda_binary_sha256"]
                    or re.fullmatch(r"[0-9a-f]{64}", record["nanoda_binary_sha256"]) is None
                    or "commit-hash: " + pin["rust_commit"] not in receipt.get("rust_version", "")
                    or receipt != read_json(directory + "/nanoda-build.json")):
                raise ValueError("Unexpected Nanoda options or build provenance")
        records[name] = record
    summary = read_json(directory + "/run-summary.json")
    if (type(summary.get("schema_version")) is not int or summary["schema_version"] != 1
            or summary["status"] != "passed" or summary["mode"] != "all"
            or summary["sandboxed"] is not False
            or summary["project_modules_rebuilt"] != 369
            or summary["audited_project_declarations"] != 9107
            or summary["audited_theorem_constants"] != 7219
            or summary["control_status"] != "passed"
            or summary["controls"] != list(CONTROLS)
            or summary.get("mapped_declarations_checked") != 49
            or not axiom_policy(summary.get("permitted_axioms"))
            or summary.get("upstream_sandboxed_comparator") != "not_run"
            or summary["challenge_configurations"] != len(expected)
            or summary["theorem_roots"] != theorem_count):
        raise ValueError("Unexpected portable full-run summary")
    evidence = summary.get("evidence_sha256")
    require(isinstance(evidence, dict) and set(evidence) == EVIDENCE_FILES,
            "Incomplete portable retained-evidence inventory")
    for filename, sha in evidence.items():
        require(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) is not None,
                "Invalid portable retained-evidence hash: " + filename)
        if common.digest(local_file(directory + "/" + filename)) != sha:
            raise ValueError("Portable evidence log/report differs: " + filename)
    run = read_json(directory + "/run-info.json")
    require(run.get("mode") == "all" and run.get("sandboxed") is False
            and run.get("nanoda_binary_source") == "build_from_recorded_pin"
            and run.get("supplied_nanoda_binary") is None,
            "Unexpected portable all-run invocation or binary provenance")
    check_certificate_invocation(run, read_json(directory + "/release-validation.json"))
    control_log = local_file(directory + "/nanoda-controls.log").read_text(encoding="utf-8")
    control_start = control_log.rfind("\n{\n")
    control_text = control_log[control_start + 1:] if control_start >= 0 else control_log
    control_result = json.loads(control_text, object_pairs_hook=unique_object)
    require(isinstance(control_result, dict) and control_result.get("status") == "passed"
            and control_result.get("checks") == list(CONTROLS),
            "Retained kernel controls do not match the portable summary")
    require(local_file(directory + "/result.txt").read_text(encoding="utf-8").strip()
            == "VERIFICATION PASSED: all", "Retained portable all-run result did not pass")
    return records


if __name__ == "__main__":
    load_records()
    targets = configured_targets()
    print(f"PORTABLE EVIDENCE FRESH: {len(targets)} configurations, "
          f"{sum(len(names) for names in targets.values())} roots, Comparator/Lean replay and Nanoda.")
