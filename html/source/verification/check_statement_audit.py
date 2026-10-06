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
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
AUDIT_PATH = "verification/statement-audit.json"
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


def load_audit(root: Path = ROOT) -> dict:
    """Return a fresh audit record, preserving its human/AI semantic verdicts."""
    root = root.resolve()
    audit = read_json(root, AUDIT_PATH)
    require(type(audit.get("schema_version")) is int and audit["schema_version"] == 1,
            "Unsupported statement-audit schema")
    require(audit.get("review_kind") == "independent_ai_source_semantics_review",
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
    check_mechanical(root, audit, sources, targets)
    return audit


def main() -> int:
    try:
        audit = load_audit()
    except (ValueError, OSError) as error:
        print("STATEMENT AUDIT INVALID: " + str(error), file=sys.stderr)
        return 1
    counts = {verdict: sum(entry["verdict"] == verdict for entry in audit["entries"])
              for verdict in sorted(VERDICTS)}
    print("STATEMENT AUDIT RECORDS FRESH: five configurations, six targets; "
          + ", ".join(f"{count} {verdict}" for verdict, count in counts.items())
          + ". Recorded reviews, not machine-certified semantic equivalence.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
