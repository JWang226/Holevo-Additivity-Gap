#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Compare actual exported public kernel types with an immutable Git snapshot.

Run only after recompiling the current sources and generating a fresh export.
This reads Git and exported metadata; it never invokes Lean, Lake, or a kernel.
Compression bytes, readable pretty-printing, proof dependencies, and internal
helper inventories are deliberately outside this public-type contract.
"""
from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

BEFORE_COMMIT = "a92c087e85603032cd0ece7b766b1f192b17a69e"
EXPORT_PATH = "metadata/declarations.json"
TYPE_FORMAT = "lean-kernel-expr-dag-v1"
SEMANTICS = "declaration-export-v3-kernel-expr-dag-v1-structural-roundtrip-readable-projection-refs"
PUBLIC_FLAGS = ("is_private", "is_internal", "is_internal_detail")
IDENTITY_FIELDS = ("name", "kind", "module", "file", "level_parameters")
CONFIGS = tuple("ComparatorChallenges/" + name + ".json" for name in (
    "A_PrescribedDimensions", "B_OperationalCoding", "C_SmallInformationSeparation",
    "D_WeylAllUses", "E_InputCost"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_file(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(data: bytes) -> dict:
    value = json.loads(data, object_pairs_hook=unique_object)
    require(isinstance(value, dict), "Expected a JSON object")
    return value


def safe_relative(name: str) -> str:
    require(isinstance(name, str) and bool(name), "Missing relative path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and "\\" not in name and ":" not in name
            and all(part not in {"", ".", ".."} for part in name.split("/")),
            "Unsafe relative path: " + name)
    return name


def local_file(root: Path, name: str) -> Path:
    path = root / safe_relative(name)
    require(path.is_file() and path.resolve().is_relative_to(root),
            "Missing or escaping input: " + name)
    return path


def git_blob(root: Path, commit: str, name: str) -> bytes:
    return subprocess.check_output(["git", "show", commit + ":" + safe_relative(name)], cwd=root)


def indexed_export(data: dict, label: str) -> dict[str, dict]:
    require(data.get("schema_version") == 1, label + ": unsupported export schema")
    provenance = data.get("provenance", {})
    require(provenance.get("extractor_semantics_version") == SEMANTICS,
            label + ": unexpected extractor semantics")
    declarations = data.get("declarations")
    require(isinstance(declarations, list) and data.get("count") == len(declarations),
            label + ": declaration count mismatch")
    indexed = {}
    for item in declarations:
        require(isinstance(item, dict) and isinstance(item.get("name"), str),
                label + ": invalid declaration record")
        name = item["name"]
        require(name not in indexed, label + ": duplicate declaration " + name)
        require(all(type(item.get(flag)) is bool for flag in PUBLIC_FLAGS),
                label + ": missing public-selection flag on " + name)
        require(all(field in item for field in IDENTITY_FIELDS),
                label + ": missing identity field on " + name)
        indexed[name] = item
    return indexed


def is_public(item: dict) -> bool:
    return not any(item[flag] for flag in PUBLIC_FLAGS)


def decoded_type(item: dict) -> bytes:
    name = item["name"]
    require(item.get("type_encoding") == "gzip+base64"
            and item.get("type_representation") == TYPE_FORMAT,
            "Unexpected full-type encoding/format: " + name)
    payload = gzip.decompress(base64.b64decode(item["type"], validate=True))
    require(type(item.get("type_uncompressed_bytes")) is int
            and len(payload) == item["type_uncompressed_bytes"]
            and digest_bytes(payload) == item.get("type_sha256"),
            "Decoded type size or SHA-256 mismatch: " + name)
    payload.decode("utf-8")
    return payload


def check_current_provenance(root: Path, export: dict) -> dict[str, str]:
    hashes = export.get("provenance", {}).get("source_sha256")
    require(isinstance(hashes, dict) and bool(hashes), "Fresh export has no source hashes")
    required = {p.relative_to(root).as_posix() for p in (root / "Nonadditivity").rglob("*.lean")}
    required.update({"Nonadditivity.lean", "Audit.lean", "All.lean", "lean-toolchain",
                     "lake-manifest.json", "lakefile.toml", "scripts/export_declarations.py",
                     "scripts/export_declarations.lean"})
    require(required <= hashes.keys(), "Fresh export omits current proof/tool inputs")
    bound_proofs = {name for name in hashes if name.endswith(".lean")
                    and (name.startswith("Nonadditivity/") or name in
                         {"Nonadditivity.lean", "Audit.lean", "All.lean"})}
    expected_proofs = {name for name in required if name.endswith(".lean")
                       and not name.startswith("scripts/")}
    require(bound_proofs == expected_proofs, "Fresh export proof inventory differs from the tree")
    for name, expected in hashes.items():
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                "Malformed provenance hash: " + name)
        require(digest_file(local_file(root, name)) == expected, "Stale fresh export: " + name)
    return dict(hashes)


def compare(root: Path, before_commit: str, after_path: Path, expected_count: int) -> dict:
    require(re.fullmatch(r"[0-9a-f]{40}", before_commit) is not None, "Use a full before-commit SHA")
    actual_commit = subprocess.check_output(
        ["git", "rev-parse", before_commit + "^{commit}"], cwd=root, text=True).strip()
    require(actual_commit == before_commit, "Before commit did not resolve exactly")
    checker_path = Path(__file__).resolve()
    require(checker_path.is_relative_to(root), "Keep the comparison script inside the repository")
    checker_sha256 = digest_file(checker_path)
    before_bytes = git_blob(root, before_commit, EXPORT_PATH)
    after_bytes = after_path.read_bytes()
    before, after = read_json(before_bytes), read_json(after_bytes)
    before_records, after_records = indexed_export(before, "before"), indexed_export(after, "after")
    current_inputs = check_current_provenance(root, after)
    before_public = {name: item for name, item in before_records.items() if is_public(item)}
    after_public = {name: item for name, item in after_records.items() if is_public(item)}
    require(len(before_public) == expected_count,
            f"Expected {expected_count} before public declarations, found {len(before_public)}")
    missing = sorted(before_public.keys() - after_public.keys())
    added = sorted(after_public.keys() - before_public.keys())
    differences = []
    for name in sorted(before_public.keys() & after_public.keys()):
        old, new = before_public[name], after_public[name]
        changed = [field for field in IDENTITY_FIELDS if old[field] != new[field]]
        if decoded_type(old) != decoded_type(new):
            changed.append("decoded_canonical_type")
        if changed:
            differences.append({"declaration": name, "changed_fields": changed})
    targets, challenge_hashes = [], {}
    for config_path in CONFIGS:
        original = git_blob(root, before_commit, config_path)
        current = local_file(root, config_path).read_bytes()
        require(original == current, "Challenge configuration changed: " + config_path)
        config = read_json(current)
        names = config.get("theorem_names")
        require(isinstance(names, list) and bool(names)
                and all(isinstance(name, str) and name for name in names),
                "Invalid configured roots: " + config_path)
        targets.extend(names)
        challenge_hashes[config_path] = digest_bytes(current)
        source_path = config_path.removesuffix(".json") + ".lean"
        original_source = git_blob(root, before_commit, source_path)
        current_source = local_file(root, source_path).read_bytes()
        require(original_source == current_source, "Expected-statement source changed: " + source_path)
        challenge_hashes[source_path] = digest_bytes(current_source)
    require(len(targets) == 6 and len(set(targets)) == 6, "Expected six unique challenge roots")
    roots = {}
    for name in sorted(targets):
        require(name in before_public and name in after_public,
                "Challenge root is absent or no longer public: " + name)
        require(before_public[name]["kind"] == after_public[name]["kind"] == "theorem",
                "Challenge root is not a theorem: " + name)
        roots[name] = {"before_type_sha256": before_public[name]["type_sha256"],
                       "after_type_sha256": after_public[name]["type_sha256"]}
    require(check_current_provenance(root, after) == current_inputs,
            "Current export inputs changed during comparison")
    require(digest_file(after_path) == digest_bytes(after_bytes),
            "Fresh export changed during comparison")
    require(digest_file(checker_path) == checker_sha256, "Comparison script changed during execution")
    for name, expected in challenge_hashes.items():
        require(digest_file(local_file(root, name)) == expected,
                "Challenge input changed during comparison: " + name)
    return {
        "schema_version": 1, "status": "passed" if not (missing or added or differences) else "failed",
        "scope": "exact_public_declaration_inventory_and_decoded_kernel_type_bytes",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "before_commit": before_commit, "before_export_path": EXPORT_PATH,
        "before_export_sha256": digest_bytes(before_bytes),
        "after_export_path": after_path.relative_to(root).as_posix(),
        "after_export_sha256": digest_bytes(after_bytes),
        "checker": {"path": checker_path.relative_to(root).as_posix(), "sha256": checker_sha256},
        "after_export_declarations": len(after_records),
        "after_export_theorems": sum(item["kind"] == "theorem" for item in after_records.values()),
        "selection": {"all_false": list(PUBLIC_FLAGS)},
        "identity_fields": list(IDENTITY_FIELDS),
        "type_comparison": "Byte equality after independent base64/gzip decode, size and SHA-256 validation",
        "expected_public_declarations": expected_count,
        "before_public_declarations": len(before_public), "after_public_declarations": len(after_public),
        "compared_public_declarations": len(before_public.keys() & after_public.keys()),
        "missing_public_declarations": missing, "added_public_declarations": added,
        "differences": differences, "challenge_root_types": roots,
        "challenge_sha256": challenge_hashes, "after_source_sha256": current_inputs,
        "lean_or_kernel_executed": False,
        "limitations": "Type identity does not prove unchanged definition bodies or English-to-Lean equivalence.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--before-commit", default=BEFORE_COMMIT)
    parser.add_argument("--after-export", default=EXPORT_PATH,
                        help="Repository-relative fresh export, normally metadata/declarations.json")
    parser.add_argument("--expected-public-count", type=int, default=5323)
    parser.add_argument("--report", required=True, help="Fresh repository-relative JSON report path")
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        require(args.expected_public_count > 0, "Public count must be positive")
        output = root / safe_relative(args.report)
        require(output.resolve().is_relative_to(root) and not output.exists(),
                "Use a fresh report path inside the repository")
        report = compare(root, args.before_commit, local_file(root, args.after_export),
                         args.expected_public_count)
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2)
            handle.write("\n")
        print(f"PUBLIC TYPE COMPARISON {report['status'].upper()}: "
              f"{report['compared_public_declarations']} declarations, six roots; {args.report}")
        return 0 if report["status"] == "passed" else 1
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print("PUBLIC TYPE COMPARISON FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
