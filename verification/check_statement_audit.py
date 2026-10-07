#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Check the freshness and scope of recorded manuscript/statement reviews.

This original implementation checks hashes, references, and recorded mechanical
provenance. It does not execute Lean, verify a reviewer's reasoning, or certify
mathematical equivalence. A fresh review may report a mismatch or remain unresolved.
"""
from __future__ import annotations

import hashlib
import argparse
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDIT_PATH = "verification/statement-audit.json"
CURRENT_AUDIT_PATH = "verification/statement-audit-current.json"
CONFIGS = tuple("ComparatorChallenges/" + stem + ".json" for stem in (
    "A_PrescribedDimensions", "B_OperationalCoding", "C_SmallInformationSeparation",
    "D_WeylAllUses", "E_InputCost"))
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VERDICTS = {"consistent", "qualified", "mismatch", "unresolved"}
SCOPE = "incremental_exact_type_application_and_axiom_checks"
FIXED_SOURCES = {
    "All.lean", "Audit.lean", "Nonadditivity.lean", "paper/nonadditivity.tex",
    "metadata/declarations.json", "metadata/results.json", "lean-toolchain",
    "lake-manifest.json", "scripts/check_challenges.py", "lean.sh", "scripts/compiler.py",
    *CONFIGS, *(str(PurePosixPath(name).with_suffix(".lean")) for name in CONFIGS),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def local_file(root: Path, name: str) -> Path:
    """Require an unambiguous repository-relative file, including symlink checks."""
    require(isinstance(name, str) and bool(name), "Missing relative file path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and "\\" not in name and ":" not in name
            and all(part not in {"", ".", ".."} for part in name.split("/"))
            and path.as_posix() == name, "Unsafe relative path: " + name)
    absolute = root / name
    require(absolute.resolve().is_relative_to(root), "Path escapes repository: " + name)
    require(absolute.is_file(), "Missing bound file: " + name)
    return absolute


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(root: Path, name: str) -> dict:
    value = json.loads(local_file(root, name).read_text(encoding="utf-8"),
                       object_pairs_hook=_unique_object)
    require(isinstance(value, dict), "Expected JSON object: " + name)
    return value


def string_list(value: object, label: str, *, nonempty: bool = True) -> list[str]:
    require(isinstance(value, list) and (bool(value) or not nonempty),
            "Expected string list: " + label)
    require(all(isinstance(item, str) and bool(item.strip()) for item in value),
            "Invalid string list: " + label)
    require(len(value) == len(set(value)), "Duplicate item: " + label)
    return value


def hash_bindings(root: Path, value: object, label: str) -> dict[str, str]:
    require(isinstance(value, dict) and bool(value), "Missing hash bindings: " + label)
    for name, sha in value.items():
        path = local_file(root, name)
        require(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) is not None,
                "Invalid SHA-256: " + label + ": " + name)
        require(digest(path) == sha, "Stale " + label + ": " + name)
    return value


def bound_reference(root: Path, value: object, label: str) -> tuple[str, dict]:
    require(isinstance(value, dict), "Missing " + label + " reference")
    name, sha = value.get("path"), value.get("sha256")
    hash_bindings(root, {name: sha}, label)
    return name, read_json(root, name)


def selected_audit_path(root: Path = ROOT, audit_path: str | None = None) -> str:
    """Use an explicitly selected current record, retaining historical fallback."""
    root = root.resolve()
    if audit_path is not None:
        local_file(root, audit_path)
        return audit_path
    selector = root / CURRENT_AUDIT_PATH
    if not selector.exists() and not selector.is_symlink():
        return AUDIT_PATH
    selection = read_json(root, CURRENT_AUDIT_PATH)
    require(type(selection.get("schema_version")) is int and selection["schema_version"] == 1,
            "Unsupported statement-audit selector schema")
    name, _ = bound_reference(root, selection.get("audit"), "selected statement audit")
    require(name != CURRENT_AUDIT_PATH, "Statement-audit selector cannot select itself")
    return name


def check_delta(root: Path, audit: dict, sources: dict, reports: dict) -> None:
    """Validate a bounded continuation without restamping its historical parent."""
    parent_path, parent = bound_reference(root, audit.get("parent_audit"), "historical statement audit")
    require(parent_path == AUDIT_PATH and parent.get("schema_version") == 1
            and parent.get("review_kind") == "independent_ai_source_semantics_review"
            and parent.get("machine_equivalence_certified") is False,
            "Unexpected historical statement-audit parent")
    # Parent source hashes are intentionally historical. Bind its exact record,
    # reports and logs, without requiring its old input bytes to be current.
    old_sources = parent.get("source_bindings")
    require(isinstance(old_sources, dict) and set(old_sources) == set(sources),
            "Delta review changed the source-binding inventory")
    old_reports = hash_bindings(root, parent.get("report_bindings"), "historical report bindings")
    _, old_evidence = bound_reference(root, parent.get("mechanical_evidence"), "historical mechanical evidence")
    hash_bindings(root, old_evidence.get("logs"), "historical mechanical logs")
    require(all(reports.get(name) == sha for name, sha in old_reports.items()),
            "Delta review omitted a historical report binding")

    changes = audit.get("changed_sources")
    require(isinstance(changes, list) and bool(changes), "Missing reviewed source delta")
    changed = {name for name in sources if sources[name] != old_sources[name]}
    found = set()
    kinds = {"redundant_local_imports_and_comments", "explicit_summability_summand",
             "fresh_declaration_export", "release_metadata_only"}
    for change in changes:
        require(isinstance(change, dict), "Invalid reviewed source change")
        name = change.get("path")
        require(name in changed and name not in found, "Wrong or duplicate reviewed source change")
        found.add(name)
        require(change.get("before_sha256") == old_sources[name]
                and change.get("after_sha256") == sources[name], "Incorrect reviewed delta hashes")
        kind = change.get("kind")
        require(kind in kinds, "Unsupported cleanup delta kind")
        require((kind == "release_metadata_only" and name == "metadata/results.json")
                or (kind == "fresh_declaration_export" and name == "metadata/declarations.json")
                or (kind == "redundant_local_imports_and_comments" and name.endswith(".lean"))
                or (kind == "explicit_summability_summand"
                    and name == "Nonadditivity/RegularCoefficientEnergy.lean"),
                "Cleanup delta kind does not match its source path")
        require(isinstance(change.get("review"), str) and bool(change["review"].strip()),
                "Missing source delta review explanation")
    require(found == changed, "Reviewed source delta is incomplete")
    require(audit.get("meaning_carrying_definition_changes") == [],
            "This cleanup continuation does not admit meaning-carrying definition changes")

    review_path, review = bound_reference(root, audit.get("source_delta_review"), "source delta review")
    require(reports.get(review_path) == audit["source_delta_review"]["sha256"],
            "Source delta review is not report-bound")
    require(type(review.get("schema_version")) is int and review["schema_version"] == 1
            and review.get("review_kind") == "bounded_cleanup_source_delta_review"
            and review.get("machine_equivalence_certified") is False,
            "Unexpected source delta review schema or scope")
    semantic_report = review.get("semantic_report")
    require(semantic_report in reports
            and all(entry.get("report") == semantic_report for entry in audit["entries"]),
            "Delta entries do not point to the bound semantic review")
    reviewed_changes = review.get("changed_proof_sources")
    require(isinstance(reviewed_changes, list), "Missing proof-source delta inventory")
    expected_proof_changes = {item["path"]: item for item in changes if item["path"].endswith(".lean")}
    reviewed_proofs = {}
    for item in reviewed_changes:
        require(isinstance(item, dict) and item.get("path") in expected_proof_changes
                and item["path"] not in reviewed_proofs, "Wrong or duplicate proof delta review")
        name = item["path"]
        require(all(item.get(field) == expected_proof_changes[name].get(field)
                    for field in ("before_sha256", "after_sha256", "kind")),
                "Source delta review does not bind the actual reviewed proof change")
        reviewed_proofs[name] = item
    require(set(reviewed_proofs) == set(expected_proof_changes), "Proof-source delta review is incomplete")
    patch_path, patch_sha = review.get("patch", {}).get("path"), review.get("patch", {}).get("sha256")
    hash_bindings(root, {patch_path: patch_sha}, "reviewed source patch")
    require(reports.get(patch_path) == patch_sha, "Reviewed source patch is not report-bound")

    _, comparison = bound_reference(root, audit.get("public_type_comparison"), "public type comparison")
    require(type(comparison.get("schema_version")) is int and comparison["schema_version"] == 1
            and comparison.get("status") == "passed"
            and comparison.get("scope") == "exact_public_declaration_inventory_and_decoded_kernel_type_bytes",
            "Unexpected public type comparison status or scope")
    require(comparison.get("after_export_path") == "metadata/declarations.json"
            and comparison.get("after_export_sha256") == sources["metadata/declarations.json"],
            "Public type comparison does not bind the current declaration export")
    require(comparison.get("before_export_sha256") == old_sources["metadata/declarations.json"],
            "Public type comparison does not bind the historical declaration export")
    require(comparison.get("before_commit") == review.get("before_commit")
            and comparison.get("selection") == {"all_false": ["is_private", "is_internal", "is_internal_detail"]}
            and comparison.get("identity_fields") == ["name", "kind", "module", "file", "level_parameters"],
            "Unexpected public comparison baseline or public selection")
    checker_path, checker_sha = comparison.get("checker", {}).get("path"), comparison.get("checker", {}).get("sha256")
    require(checker_path == "scripts/compare_public_types.py", "Unexpected public type comparison checker")
    hash_bindings(root, {checker_path: checker_sha}, "public comparison checker")
    for field in ("missing_public_declarations", "added_public_declarations", "differences"):
        require(comparison.get(field) == [], "Public declaration comparison has differences")
    counts = [comparison.get(name) for name in ("expected_public_declarations", "before_public_declarations",
              "after_public_declarations", "compared_public_declarations")]
    require(all(type(count) is int and count > 0 for count in counts) and len(set(counts)) == 1,
            "Incomplete public declaration type comparison")
    proof_names = {name for name in sources if name.endswith(".lean") and
                   (name.startswith("Nonadditivity/") or name in {"Nonadditivity.lean", "All.lean", "Audit.lean"})}
    inventory = string_list(review.get("proof_source_inventory"), "source delta proof inventory")
    require(set(inventory) == proof_names, "Source delta proof inventory differs from current sources")
    compared_sources = hash_bindings(root, comparison.get("after_source_sha256"), "public comparison sources")
    require(all(compared_sources.get(name) == sources[name] for name in proof_names),
            "Public type comparison does not bind all current proof sources")
    challenge_names = set(CONFIGS) | {str(PurePosixPath(name).with_suffix(".lean")) for name in CONFIGS}
    compared_challenges = hash_bindings(root, comparison.get("challenge_sha256"), "public comparison challenges")
    require(set(compared_challenges) == challenge_names
            and all(compared_challenges[name] == sources[name] for name in challenge_names),
            "Public type comparison challenge coverage differs")
    declarations = read_json(root, "metadata/declarations.json")["declarations"]
    public = [item for item in declarations
              if all(item.get(field) is False for field in ("is_private", "is_internal", "is_internal_detail"))]
    require(counts[0] == len(public), "Public comparison count differs from the current export")
    by_name = {item["name"]: item for item in declarations}
    parent_records = parent.get("entries")
    require(isinstance(parent_records, list) and len(parent_records) == 6
            and all(isinstance(item, dict) and isinstance(item.get("declaration"), str) for item in parent_records),
            "Invalid historical statement-audit entries")
    parent_entries = {item["declaration"]: item for item in parent_records}
    require(len(parent_entries) == 6, "Duplicate historical statement-audit target")
    roots = comparison.get("challenge_root_types")
    require(isinstance(roots, dict) and set(roots) == set(parent_entries), "Public comparison root coverage differs")
    for entry in audit["entries"]:
        old = parent_entries.get(entry["declaration"])
        require(isinstance(old, dict), "Delta review has a new target")
        for field in ("id", "declaration", "config", "result_ids", "source_labels", "verdict", "qualifications", "type_sha256"):
            require(entry.get(field) == old.get(field), "Delta review changed historical " + field)
        require(entry.get("historical_report") == old["report"], "Wrong historical entry report")
        require(isinstance(entry.get("delta_finding"), str) and bool(entry["delta_finding"].strip()),
                "Missing per-root delta finding")
        root_types = roots[entry["declaration"]]
        require(root_types.get("before_type_sha256") == old["type_sha256"]
                and root_types.get("after_type_sha256") == old["type_sha256"]
                and by_name[entry["declaration"]].get("type_sha256") == old["type_sha256"],
                "Delta root type changed")


def required_sources(root: Path = ROOT) -> set[str]:
    """Discover proof sources afresh so adding a proof file invalidates coverage."""
    root = root.resolve()
    proof_root = root / "Nonadditivity"
    require(proof_root.is_dir() and proof_root.resolve().is_relative_to(root),
            "Missing or escaping Nonadditivity source directory")
    # rglob does not traverse directory symlinks. Reject those instead of silently
    # omitting an additional source tree from this freshness envelope.
    for path in proof_root.rglob("*"):
        if path.is_symlink():
            require(path.resolve().is_relative_to(root),
                    "Proof-source symlink escapes repository: " + path.relative_to(root).as_posix())
            require(not path.is_dir(),
                    "Proof-source directory symlink is not supported: " + path.relative_to(root).as_posix())
    sources = {path.relative_to(root).as_posix() for path in proof_root.rglob("*.lean")}
    require(bool(sources), "No Nonadditivity proof sources found")
    return FIXED_SOURCES | sources


def current_targets(root: Path) -> dict[str, str]:
    configs = {path.relative_to(root).as_posix()
               for path in (root / "ComparatorChallenges").glob("*.json")}
    require(configs == set(CONFIGS), "Expected the five current Comparator configurations")
    targets = {}
    for filename in CONFIGS:
        config = read_json(root, filename)
        names = string_list(config.get("theorem_names"), filename + " theorem_names")
        require(config.get("challenge_module") == PurePosixPath(filename).with_suffix("").as_posix().replace("/", "."),
                "Challenge module/path mismatch: " + filename)
        require(set(string_list(config.get("permitted_axioms"), filename + " permitted_axioms")) == AXIOMS,
                "Unexpected challenge axiom policy: " + filename)
        require(config.get("enable_nanoda") is False, "Unexpected challenge Nanoda flag: " + filename)
        for name in names:
            require(name not in targets, "Duplicate configured theorem: " + name)
            targets[name] = filename
    require(len(targets) == 6, "Expected exactly six configured theorem targets")
    return targets


def check_mechanical(root: Path, audit: dict, sources: dict, targets: dict) -> None:
    reference = audit.get("mechanical_evidence")
    require(isinstance(reference, dict), "Missing mechanical evidence reference")
    filename, sha = reference.get("path"), reference.get("sha256")
    local_file(root, filename)
    hash_bindings(root, {filename: sha}, "mechanical evidence")
    evidence = read_json(root, filename)
    require(evidence.get("status") == "passed" and evidence.get("scope") == SCOPE,
            "Unexpected recorded mechanical status or scope")
    require(evidence.get("source_commit") == audit["reviewed_commit"],
            "Mechanical evidence source commit differs from reviewed commit")
    for flag in ("compiled_sources_from_scratch", "comparator_rerun", "nanoda_rerun"):
        require(evidence.get(flag) is False, "Unexpected mechanical scope flag: " + flag)
    names = string_list(evidence.get("theorem_names"), "mechanical theorem_names")
    require(set(names) == set(targets), "Mechanical evidence has different theorem targets")
    require(set(string_list(evidence.get("permitted_axioms"), "mechanical permitted_axioms")) == AXIOMS,
            "Unexpected mechanical axiom policy")
    root_axioms = evidence.get("root_axioms")
    require(isinstance(root_axioms, dict) and set(root_axioms) == set(targets),
            "Mechanical root axiom coverage differs")
    for name, axioms in root_axioms.items():
        require(set(string_list(axioms, name + " mechanical root axioms")) == AXIOMS,
                "Unexpected mechanical root axiom closure: " + name)
    inputs = hash_bindings(root, evidence.get("inputs"), "mechanical inputs")
    require(all(inputs.get(name) == sha for name, sha in sources.items()),
            "Mechanical inputs do not cover all reviewed source bindings")
    logs = hash_bindings(root, evidence.get("logs"), "mechanical logs")
    commands = evidence.get("commands")
    require(isinstance(commands, list) and bool(commands), "Missing mechanical commands")
    for command in commands:
        require(isinstance(command, dict), "Invalid mechanical command record")
        argv = command.get("command")
        require(isinstance(argv, list) and bool(argv)
                and all(isinstance(arg, str) and bool(arg) for arg in argv),
                "Invalid recorded mechanical command")
        require(type(command.get("exit_code")) is int and command["exit_code"] == 0,
                "Recorded mechanical command did not pass")
        local_file(root, command.get("log"))
        require(command["log"] in logs, "Mechanical command log is not hash-bound")


def load_audit(root: Path = ROOT, audit_path: str | None = None) -> dict:
    """Return a fresh audit record, preserving its human/AI semantic verdicts."""
    root = root.resolve()
    audit = read_json(root, selected_audit_path(root, audit_path))
    schema = audit.get("schema_version")
    require(type(schema) is int and schema in {1, 2},
            "Unsupported statement-audit schema")
    expected_kind = "independent_ai_source_semantics_review" if schema == 1 else "incremental_ai_source_semantics_review"
    require(audit.get("review_kind") == expected_kind,
            "Unexpected statement-review kind")
    require(audit.get("machine_equivalence_certified") is False,
            "A statement audit must not claim machine-certified semantic equivalence")
    commit = audit.get("reviewed_commit")
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "Invalid reviewed source commit")
    sources = hash_bindings(root, audit.get("source_bindings"), "source bindings")
    missing = required_sources(root) - sources.keys()
    require(not missing, "Unbound current source files: " + ", ".join(sorted(missing)))
    reports = hash_bindings(root, audit.get("report_bindings"), "report bindings")
    targets = current_targets(root)

    declarations = read_json(root, "metadata/declarations.json").get("declarations")
    require(isinstance(declarations, list), "Missing declaration metadata")
    by_name = {}
    for declaration in declarations:
        require(isinstance(declaration, dict) and isinstance(declaration.get("name"), str),
                "Invalid declaration metadata")
        name = declaration["name"]
        require(name not in by_name, "Duplicate declaration metadata: " + name)
        by_name[name] = declaration
    results = read_json(root, "metadata/results.json").get("results")
    require(isinstance(results, list), "Missing result metadata")
    by_id = {}
    for result in results:
        require(isinstance(result, dict) and isinstance(result.get("id"), str), "Invalid result metadata")
        require(result["id"] not in by_id, "Duplicate result metadata: " + result["id"])
        by_id[result["id"]] = result
    paper = local_file(root, "paper/nonadditivity.tex").read_text(encoding="utf-8")
    paper = re.sub(r"(?<!\\)%[^\n]*", "", paper)
    labels = set(re.findall(r"\\label\s*\{([^{}]+)\}", paper))

    entries = audit.get("entries")
    require(isinstance(entries, list) and len(entries) == 6, "Expected six statement-audit entries")
    entry_ids, seen = set(), set()
    for entry in entries:
        require(isinstance(entry, dict), "Invalid statement-audit entry")
        for field in ("id", "declaration", "reviewer"):
            require(isinstance(entry.get(field), str) and bool(entry[field].strip()),
                    "Missing entry " + field)
        require(entry["id"] not in entry_ids, "Duplicate statement-audit entry ID: " + entry["id"])
        entry_ids.add(entry["id"])
        name = entry["declaration"]
        require(name in targets and name not in seen, "Wrong or duplicate audit target: " + name)
        seen.add(name)
        declaration = by_name.get(name)
        require(isinstance(declaration, dict) and declaration.get("kind") == "theorem",
                "Audit target is not an exported theorem: " + name)
        require(entry.get("config") == targets[name], "Audit target/config mismatch: " + name)
        report = entry.get("report")
        local_file(root, report)
        require(report in reports, "Entry report is not hash-bound: " + report)
        reviewed = string_list(entry.get("reviewed_files"), name + " reviewed_files")
        for filename in reviewed:
            local_file(root, filename)
            require(filename in sources, "Reviewed file is not source-bound: " + filename)
        source_file = declaration.get("file")
        local_file(root, source_file)
        require(source_file in reviewed, "Target's declaration file was not listed as reviewed: " + name)
        result_ids = string_list(entry.get("result_ids"), name + " result_ids")
        found = False
        for result_id in result_ids:
            require(result_id in by_id, "Unknown cited result ID: " + result_id)
            result = by_id[result_id]
            lean = result.get("lean")
            require(isinstance(lean, list) and all(isinstance(item, dict) for item in lean),
                    "Invalid result Lean references: " + result_id)
            matches = [item for item in lean if item.get("declaration") == name]
            if matches:
                require(all(item.get("file") == source_file for item in matches),
                        "Result/declaration source file mismatch: " + result_id)
                require(result.get("comparator_config") == targets[name],
                        "Result/target Comparator configuration mismatch: " + result_id)
                found = True
        require(found, "Cited results do not contain audit target: " + name)
        source_labels = string_list(entry.get("source_labels"), name + " source_labels")
        require(set(source_labels) <= labels, "Unknown manuscript source label: " + name)
        require(isinstance(entry.get("verdict"), str) and entry["verdict"] in VERDICTS,
                "Unknown semantic-review verdict: " + name)
        string_list(entry.get("qualifications"), name + " qualifications", nonempty=False)
    require(seen == set(targets), "Audit does not cover the configured theorem targets")
    if schema == 2:
        check_delta(root, audit, sources, reports)
    check_mechanical(root, audit, sources, targets)
    return audit


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", help="Repository-relative audit manifest; otherwise use current selector, then historical fallback")
    args = parser.parse_args()
    try:
        audit = load_audit(audit_path=args.audit)
    except (ValueError, OSError) as error:
        print("STATEMENT AUDIT INVALID: " + str(error), file=sys.stderr)
        return 1
    counts = {verdict: sum(entry["verdict"] == verdict for entry in audit["entries"])
              for verdict in sorted(VERDICTS)}
    mode = "cleanup delta continuation" if audit["schema_version"] == 2 else "historical review"
    print("STATEMENT AUDIT RECORDS FRESH (" + mode + "): five configurations, six targets; "
          + ", ".join(f"{count} {verdict}" for verdict, count in counts.items())
          + ". Recorded reviews, not machine-certified semantic equivalence.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
