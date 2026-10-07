# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Validate recorded cleanup source evidence without executing proof checks.

This is a narrow alternative to historical byte identity, selected explicitly
by validate_release.py --source-certificate. It cannot create passing evidence,
and it makes no Comparator, Nanoda, or statement-semantics review claim.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

BEFORE_COMMIT = "a92c087e85603032cd0ece7b766b1f192b17a69e"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PUBLIC_FLAGS = ["is_private", "is_internal", "is_internal_detail"]
IDENTITY_FIELDS = ["name", "kind", "module", "file", "level_parameters"]
DRIVER_FILES = ("build.sh", "lean.sh", "scripts/compiler.py", "lean-toolchain",
                "lakefile.toml", "lake-manifest.json", "scripts/elaboration_test.py")
CONFIGS = tuple("ComparatorChallenges/" + name + ".json" for name in (
    "A_PrescribedDimensions", "B_OperationalCoding", "C_SmallInformationSeparation",
    "D_WeylAllUses", "E_InputCost"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def local_file(root: Path, name: str) -> Path:
    require(isinstance(name, str) and bool(name), "Missing certificate input path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and "\\" not in name and ":" not in name
            and all(part not in {"", ".", ".."} for part in name.split("/")),
            "Unsafe certificate path: " + name)
    absolute = root / name
    require(absolute.is_file() and absolute.resolve().is_relative_to(root),
            "Missing or escaping certificate input: " + name)
    return absolute


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate certificate JSON key: " + key)
        result[key] = value
    return result


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    require(isinstance(value, dict), "Expected certificate JSON object: " + str(path))
    return value


def hash_bindings(root: Path, value: object, label: str) -> dict[str, str]:
    require(isinstance(value, dict) and bool(value), "Missing " + label)
    for name, sha256 in value.items():
        require(isinstance(sha256, str) and re.fullmatch(r"[0-9a-f]{64}", sha256),
                "Invalid " + label + " hash: " + name)
        require(digest(local_file(root, name)) == sha256, "Stale " + label + ": " + name)
    return value


def reference(root: Path, value: object, label: str) -> tuple[Path, str]:
    require(isinstance(value, dict) and set(value) == {"path", "sha256"},
            "Invalid " + label + " reference")
    hash_bindings(root, {value["path"]: value["sha256"]}, label)
    return local_file(root, value["path"]), value["sha256"]


def check_committed_snapshot(root: Path, commit: str, hashes: dict[str, str]) -> None:
    """Check the harness's claimed committed snapshot with one Git batch read."""
    resolved = subprocess.run(["git", "rev-parse", commit + "^{commit}"], cwd=root,
                              capture_output=True, check=False)
    require(resolved.returncode == 0 and resolved.stdout.decode().strip() == commit,
            "Recorded rebuild source commit is unavailable or does not resolve exactly")
    names = sorted(hashes)
    requests = "".join(commit + ":" + name + "\n" for name in names).encode()
    response = subprocess.run(["git", "cat-file", "--batch"], cwd=root, input=requests,
                              capture_output=True, check=False)
    require(response.returncode == 0, "Cannot read recorded rebuild Git snapshot")
    data, offset = response.stdout, 0
    for name in names:
        end = data.find(b"\n", offset)
        require(end != -1, "Incomplete recorded Git snapshot: " + name)
        fields = data[offset:end].split()
        require(len(fields) == 3 and fields[1] == b"blob" and fields[2].isdigit(),
                "Missing recorded source/driver blob: " + name)
        size = int(fields[2])
        payload = data[end + 1:end + 1 + size]
        require(len(payload) == size and data[end + 1 + size:end + 2 + size] == b"\n",
                "Incomplete source/driver blob: " + name)
        require(hashlib.sha256(payload).hexdigest() == hashes[name],
                "Source/driver hashes differ from recorded committed snapshot: " + name)
        offset = end + size + 2
    require(offset == len(data), "Unexpected trailing Git snapshot data")


def load_source_certificate(root: Path, name: str, proof_paths: set[str]) -> dict:
    """Require full current-source coverage and fresh recorded rebuild/type evidence."""
    certificate_path = local_file(root, name)
    certificate_sha256 = digest(certificate_path)
    certificate = read_json(certificate_path)
    require(type(certificate.get("schema_version")) is int and certificate["schema_version"] == 1
            and certificate.get("status") == "passed"
            and certificate.get("scope") == "source_rebuild_with_exact_public_types",
            "Unsupported or incomplete current-source certificate")
    commit = certificate.get("source_commit")
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit),
            "Invalid certificate source commit")
    require(set(certificate.get("permitted_transitive_axioms", [])) == AXIOMS,
            "Unexpected certificate axiom policy")
    for flag in ("external_comparator_execution", "independent_kernel_execution"):
        require(certificate.get(flag) == "not_run", "This certificate must retain its Lean-only scope")
    sources = hash_bindings(root, certificate.get("proof_source_sha256"), "certificate proof sources")
    require(set(sources) == proof_paths, "Certificate proof-source inventory differs from the release")

    summary_path, _ = reference(root, certificate.get("build_summary"), "build summary")
    summary = read_json(summary_path)
    require(summary.get("valid") is True and summary.get("invalid_reasons") == []
            and summary.get("build", {}).get("returncode") == 0,
            "Recorded full project rebuild did not pass")
    provenance = summary.get("provenance", {})
    require(provenance.get("commit") == commit
            and provenance.get("pin") == local_file(root, "lean-toolchain").read_text().strip(),
            "Build source commit or Lean pin differs from certificate")
    expected_modules = {path.removesuffix(".lean").replace("/", "."): path for path in proof_paths}
    require(summary.get("modules") == expected_modules, "Measured rebuild module inventory differs")
    coverage = summary.get("coverage", {})
    require(coverage.get("complete") is True and coverage.get("order_matches") is True
            and coverage.get("expected") == coverage.get("measured") == len(proof_paths)
            and all(coverage.get(field) == [] for field in ("missing", "unexpected", "duplicates", "failed")),
            "Measured rebuild lacks complete successful module coverage")
    measured_inputs = hash_bindings(root, summary.get("source_hashes_before"), "measured source/driver inputs")
    require(set(measured_inputs) == proof_paths | set(DRIVER_FILES),
            "Measured source/driver inventory differs from complete proofs plus seven drivers")
    require(summary.get("source_hashes_after") == measured_inputs
            and all(measured_inputs.get(path) == sha for path, sha in sources.items())
            and summary.get("source_changes") == [] and summary.get("dependency_artifact_changes") == [],
            "Measured source/dependency guards did not establish stable inputs")
    check_committed_snapshot(root, commit, measured_inputs)
    health = summary.get("health", {})
    require(all(health.get(field) == 0 for field in
                ("error_count", "sorry_warning_count", "unauthorized_sorry_tokens"))
            and health.get("allowed_sorry_modules") == [],
            "Recorded rebuild contains errors or authorized proof holes")

    comparison_path, _ = reference(root, certificate.get("public_type_comparison"), "public-type comparison")
    comparison = read_json(comparison_path)
    require(type(comparison.get("schema_version")) is int and comparison["schema_version"] == 1
            and comparison.get("status") == "passed"
            and comparison.get("scope") == "exact_public_declaration_inventory_and_decoded_kernel_type_bytes"
            and comparison.get("before_commit") == BEFORE_COMMIT
            and comparison.get("before_export_path") == "metadata/declarations.json"
            and comparison.get("after_export_path") == "metadata/declarations.json"
            and comparison.get("selection") == {"all_false": PUBLIC_FLAGS}
            and comparison.get("identity_fields") == IDENTITY_FIELDS
            and comparison.get("lean_or_kernel_executed") is False,
            "Unexpected public-type comparison source, format, or scope")
    require(all(type(comparison.get(field)) is int and comparison[field] == 5323 for field in
                ("expected_public_declarations", "before_public_declarations", "after_public_declarations",
                 "compared_public_declarations"))
            and all(comparison.get(field) == [] for field in
                    ("missing_public_declarations", "added_public_declarations", "differences")),
            "Public declaration inventory or exact types changed")
    reference(root, comparison.get("checker"), "public-type comparison script")
    fresh_export = local_file(root, "metadata/declarations.json")
    require(digest(fresh_export) == comparison.get("after_export_sha256"), "Stale compared declaration export")
    export_inputs = hash_bindings(root, comparison.get("after_source_sha256"), "compared export inputs")
    require(all(export_inputs.get(path) == sha for path, sha in sources.items()),
            "Compared export omits the checked proof sources")
    expected_challenge_paths = set(CONFIGS) | {name.removesuffix(".json") + ".lean" for name in CONFIGS}
    challenge_inputs = hash_bindings(root, comparison.get("challenge_sha256"), "unchanged challenge inputs")
    require(set(challenge_inputs) == expected_challenge_paths, "Unexpected compared challenge inventory")
    targets = []
    for filename in CONFIGS:
        names = read_json(local_file(root, filename)).get("theorem_names")
        require(isinstance(names, list), "Invalid challenge roots")
        targets.extend(names)
    roots = comparison.get("challenge_root_types")
    require(len(targets) == len(set(targets)) == 6 and isinstance(roots, dict) and set(roots) == set(targets),
            "Public-type comparison does not cover all six roots")
    for root_name, entry in roots.items():
        require(isinstance(entry, dict) and isinstance(entry.get("before_type_sha256"), str)
                and re.fullmatch(r"[0-9a-f]{64}", entry["before_type_sha256"])
                and entry["before_type_sha256"] == entry.get("after_type_sha256"),
                "Challenge root type changed: " + root_name)

    audit_path, audit_sha256 = reference(root, certificate.get("audit_log"), "full rebuild/audit log")
    original_build_log = summary.get("build", {}).get("log")
    require(isinstance(original_build_log, str) and bool(original_build_log)
            and Path(original_build_log).is_absolute(), "Missing original measured build-log path")
    require(certificate.get("audit_log_archive_receipt") == {
        "original_path": original_build_log, "sha256": audit_sha256},
        "Retained full rebuild log is not associated with the measured output's exact-copy receipt")
    build_log = audit_path.read_text()
    checked_sources = re.findall(r"(?m)^Checking ([^\r\n]+\.lean)\s*$", build_log)
    build_completions = re.findall(r"(?m)^BUILD PASSED: (\d+) project modules\.\s*$", build_log)
    require(set(checked_sources) == proof_paths and len(checked_sources) == len(proof_paths)
            and build_completions == [str(len(proof_paths))],
            "Retained audit is not the complete measured project rebuild log")
    completions = re.findall(r"(?m)^AUDIT PASSED: (\d+) project declarations, (\d+) theorems; "
                             r"transitive axioms \[([^\]]*)\]\.\s*$", build_log)
    require(len(completions) == 1, "Expected one retained full rebuild audit completion")
    declarations, theorems, actual_axioms = completions[0]
    require({item.strip() for item in actual_axioms.split(",")} == AXIOMS,
            "Recorded full audit has unexpected transitive axioms")
    require(int(declarations) == certificate.get("audited_project_declarations")
            == comparison.get("after_export_declarations")
            and int(theorems) == certificate.get("audited_theorem_constants")
            == comparison.get("after_export_theorems"),
            "Fresh audit and compared export counts disagree")
    require(digest(certificate_path) == certificate_sha256, "Certificate changed during validation")
    return {"method": "full_rebuild_and_exact_public_types", "path": name,
            "sha256": certificate_sha256, "source_commit": commit, "proof_source_sha256": sources}
