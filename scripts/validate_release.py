#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Validate this release's metadata, source integrity, and Lean references.

The embedded schemas are repository consistency checks for the v0.3-style
metadata layout, not a claim of certification against an official schema.
The default additionally invokes Lean on every mapped declaration. Use
--static-only before building; that option does not verify any proof.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

import jsonschema
import yaml

from check_declarations import NAME, check_declarations


HEADER = (
    "/-\nCopyright (c) 2026 the Nonadditivity project contributors.\n"
    "All rights reserved. See COPYRIGHT.md for licensing and attribution.\n-/\n\n"
).encode("utf-8")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TEXT = {"type": "string", "minLength": 1}
STRINGS = {"type": "array", "items": TEXT, "uniqueItems": True}
LEAN_REF = {
    "type": "object", "required": ["declaration", "file", "role"],
    "properties": {
        "declaration": TEXT, "file": TEXT,
        "role": {"enum": ["theorem", "unproved_predicate"]},
    },
    "additionalProperties": False,
}
RESULTS_SCHEMA = {
    "type": "object",
    "required": ["schema_version", "manuscript", "formalization", "results"],
    "properties": {
        "schema_version": {"const": "1.0"},
        "manuscript": {
            "type": "object", "required": ["file", "sha256", "edited"],
            "properties": {
                "file": TEXT, "sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
                "edited": {"type": "boolean"},
            },
        },
        "formalization": {"type": "object"},
        "results": {
            "type": "array", "minItems": 1,
            "items": {
                "type": "object",
                "required": ["id", "name", "paper", "status", "correspondence", "lean", "notes"],
                "properties": {
                    "id": TEXT, "name": TEXT,
                    "paper": {
                        "type": "object", "required": ["labels", "locator"],
                        "properties": {"labels": STRINGS, "locator": {"type": "string"}},
                        "additionalProperties": False,
                    },
                    "status": {"enum": ["proved", "corrected", "not_formalized"]},
                    "correspondence": {"enum": ["exact_endpoint", "alternate_argument", "specialization", "broader_unformalized", "corrected_proof"]},
                    "lean": {"type": "array", "items": LEAN_REF},
                    "notes": {"type": "string"}, "comparator_config": TEXT,
                },
                "additionalProperties": False,
            },
        },
    },
}
MAIN_RESULTS_SCHEMA = {
    "type": "array", "minItems": 1,
    "items": {
        "type": "object",
        "required": ["name", "declaration", "file", "sorry_count", "axioms", "comparator_config"],
        "properties": {"name": TEXT, "declaration": TEXT, "file": TEXT, "sorry_count": {"const": 0}, "axioms": STRINGS, "comparator_config": TEXT},
    },
}
YAML_SCHEMA = {
    "type": "object",
    "required": ["version", "project", "sources", "status", "automation", "review"],
    "properties": {
        "version": {"const": "v0.3"},
        "project": {
            "type": "object", "required": ["name", "authors", "license"],
            "properties": {"name": TEXT, "authors": STRINGS, "license": TEXT},
        },
        "sources": {"type": "array", "minItems": 1, "items": {"type": "object", "required": ["title", "authors", "id", "type"]}},
        "status": {
            "type": "object", "required": ["scope", "sorry_count", "sorry_in_definitions", "axioms", "main_results"],
            "properties": {"scope": TEXT, "sorry_count": {"const": 0}, "sorry_in_definitions": {"const": 0}, "axioms": STRINGS, "main_results": MAIN_RESULTS_SCHEMA},
        },
        "automation": {"type": "object"}, "review": {"type": "object"},
    },
}
COMPARATOR_SCHEMA = {
    "type": "object",
    "required": ["challenge_module", "solution_module", "theorem_names", "permitted_axioms", "enable_nanoda"],
    "properties": {
        "challenge_module": TEXT, "solution_module": TEXT,
        "theorem_names": {**STRINGS, "minItems": 1},
        "permitted_axioms": STRINGS, "enable_nanoda": {"type": "boolean"},
    },
    "additionalProperties": False,
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def local_file(root: Path, value: str) -> Path:
    relative = Path(value)
    require(not relative.is_absolute() and ".." not in relative.parts, f"Nonlocal path: {value}")
    path = root / relative
    require(path.is_file() and path.resolve().is_relative_to(root), f"Missing/nonlocal file: {value}")
    return path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text: str) -> str:
    """Remove nested comments and strings for supplemental lexical checks."""
    output = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                output[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                output[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                output[i:i + 2] = "  "
                i += 2
            else:
                string = text[i] != '"'
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            output[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            stop = text.find("\n", i)
            stop = len(text) if stop == -1 else stop
            output[i:stop] = " " * (stop - i)
            i = stop
        elif text[i] == '"':
            string = True
            output[i] = " "
            i += 1
        else:
            i += 1
    require(depth == 0 and not string, "Unclosed Lean comment/string in lexical scan")
    return "".join(output)


def imports(path: Path) -> set[str]:
    result: set[str] = set()
    for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)", lean_code(path.read_text(encoding="utf-8"))):
        result.update(match.group(1).split())
    return result


def static_checks(root: Path) -> tuple[dict, dict]:
    metadata_bytes = {name: local_file(root, name).read_bytes() for name in ("metadata/results.json", "formalization.yaml")}
    data = json.loads(metadata_bytes["metadata/results.json"])
    formalization = yaml.safe_load(metadata_bytes["formalization.yaml"])
    jsonschema.validate(data, RESULTS_SCHEMA)
    jsonschema.validate(formalization, YAML_SCHEMA)
    manuscript = local_file(root, data["manuscript"]["file"])
    require(sha256(manuscript) == data["manuscript"]["sha256"], "Manuscript checksum mismatch")
    labels = set(re.findall(r"\\label\s*\{([^}]+)\}", manuscript.read_text(encoding="utf-8")))
    ids, refs, linked_configs = set(), {}, set()
    for result in data["results"]:
        require(result["id"] not in ids, f"Duplicate result id: {result['id']}")
        ids.add(result["id"])
        require(bool(result["paper"]["labels"] or result["paper"]["locator"]), f"No manuscript locator: {result['id']}")
        for label in result["paper"]["labels"]:
            require(label in labels, f"Unknown manuscript label: {label}")
        if result["status"] in {"proved", "corrected"}:
            require(any(ref["role"] == "theorem" for ref in result["lean"]), f"Proved result has no theorem: {result['id']}")
        if result["status"] == "not_formalized":
            require(all(ref["role"] == "unproved_predicate" for ref in result["lean"]), f"Unformalized result claims a theorem: {result['id']}")
        for ref in result["lean"]:
            source = local_file(root, ref["file"])
            require(source.suffix == ".lean" and ref["file"].startswith("Nonadditivity/"), f"Mapped reference outside proof library: {ref}")
            require(bool(NAME.fullmatch(ref["declaration"])), f"Invalid declaration name: {ref['declaration']}")
            old = refs.setdefault(ref["declaration"], ref)
            require(old == ref, f"Conflicting declaration references: {ref['declaration']}")
        if "comparator_config" in result:
            linked_configs.add(result["comparator_config"])
            local_file(root, result["comparator_config"])

    expected_axioms = formalization["status"]["axioms"]
    require(set(expected_axioms) == AXIOMS, "formalization.yaml has unexpected permitted axioms")
    require(set(data["formalization"]["permitted_transitive_axioms"]) == AXIOMS, "results.json has unexpected permitted axioms")
    require(data["formalization"]["sorry_count"] == 0 and data["formalization"]["custom_axioms"] == [], "results.json proof placeholder/axiom status is inconsistent")
    require(data["formalization"]["toolchain"] == local_file(root, "lean-toolchain").read_text().strip(), "Toolchain metadata mismatch")
    lake = json.loads(local_file(root, "lake-manifest.json").read_text())
    mathlib = [pkg for pkg in lake["packages"] if pkg["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == data["formalization"]["mathlib_revision"], "Mathlib revision mismatch")

    configs, target_count = {}, 0
    for path in sorted((root / "ComparatorChallenges").glob("*.json")):
        config = json.loads(path.read_text(encoding="utf-8"))
        jsonschema.validate(config, COMPARATOR_SCHEMA)
        relative = path.relative_to(root).as_posix()
        configs[relative] = config
        require(set(config["permitted_axioms"]) == AXIOMS, f"Unexpected comparator permitted axioms: {relative}")
        require(config["enable_nanoda"] is False, f"Document separately before enabling optional nanoda: {relative}")
        for key in ("challenge_module", "solution_module"):
            require(bool(NAME.fullmatch(config[key])), f"Invalid module name in {relative}")
            local_file(root, config[key].replace(".", "/") + ".lean")
        require(config["challenge_module"].startswith("ComparatorChallenges."), f"Challenge namespace mismatch: {relative}")
        require(config["solution_module"].startswith("Nonadditivity."), f"Solution namespace mismatch: {relative}")
        for name in config["theorem_names"]:
            require(name in refs and refs[name]["role"] == "theorem", f"Unmapped Comparator target: {name}")
            target_count += 1
    require(set(configs) == linked_configs, "Comparator files and mapping links differ")
    for result in data["results"]:
        if "comparator_config" in result:
            names = {ref["declaration"] for ref in result["lean"]}
            require(set(configs[result["comparator_config"]]["theorem_names"]) <= names, f"Comparator targets missing from result: {result['id']}")
    for main in formalization["status"]["main_results"]:
        name = main["declaration"]
        require(name in refs and refs[name]["role"] == "theorem", f"Unmapped main result: {name}")
        require(main["file"] == refs[name]["file"], f"Wrong main result file: {name}")
        require(set(main["axioms"]) == AXIOMS, f"Unexpected main result axioms: {name}")
        config = configs.get(main["comparator_config"])
        require(config is not None and name in config["theorem_names"], f"Comparator misses main result: {name}")

    baseline = json.loads(local_file(root, "verification/baseline-verification.json").read_text())
    historical = {name: digest for name, digest in baseline["file_sha256"].items() if name.endswith(".lean")}
    require(len(historical) == baseline["compiled_modules"], "Historical proof manifest module count mismatch")
    proof_files = sorted((root / "Nonadditivity").rglob("*.lean")) + [root / name for name in ("Nonadditivity.lean", "Audit.lean", "All.lean")]
    require({p.relative_to(root).as_posix() for p in proof_files} == set(historical) | {"All.lean"}, "Release proof file inventory differs from baseline plus All.lean")
    proof_modules = {".".join(p.relative_to(root).with_suffix("").parts): p for p in proof_files}
    all_imports = {}
    for module, path in proof_modules.items():
        raw = path.read_bytes()
        require(raw.startswith(HEADER), f"Missing standard copyright header: {path.relative_to(root)}")
        relative = path.relative_to(root).as_posix()
        if relative in historical:
            require(hashlib.sha256(raw[len(HEADER):]).hexdigest() == historical[relative], f"Proof body differs from audited baseline: {relative}")
        code = lean_code(raw.decode("utf-8"))
        require(not re.search(r"(?<![\w.])(?:sorry|admit)(?!\w)", code), f"Placeholder in proof source: {relative}")
        require(not re.search(r"(?m)^\s*(?:private\s+)?axiom\b", code), f"Project axiom in source: {relative}")
        imported = imports(path)
        require(not any(name.startswith("ComparatorChallenges") for name in imported), f"Proof source imports a challenge: {relative}")
        all_imports[module] = imported
    reached = set()
    def visit(module: str) -> None:
        if module in reached:
            return
        reached.add(module)
        for dependency in all_imports[module] & proof_modules.keys():
            visit(dependency)
    visit("Audit")
    require(set(proof_modules) - {"All"} <= reached, "Audit does not import every proof module")
    require(all_imports["All"] in ({"Nonadditivity"}, {"Audit"}, {"Nonadditivity", "Audit"}), "All.lean must aggregate the proof library and/or its audit")

    return data, {
        "result_rows": len(ids), "unique_mapped_declarations": len(refs),
        "comparator_configurations": len(configs), "comparator_targets": target_count,
        "baseline_proof_bodies_unchanged": len(historical), "proof_modules_including_all": len(proof_files),
        "manuscript_sha256": sha256(manuscript),
        "schema_validation": "repository consistency schema for v0.3-style metadata",
        "comparator_executed": False,
        "metadata_sha256": {name: hashlib.sha256(raw).hexdigest() for name, raw in metadata_bytes.items()},
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--static-only", action="store_true", help="Skip Lean declaration checks; no proof verification is claimed")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        data, report = static_checks(root)
        report["lean_declaration_check"] = "not_run" if args.static_only else "passed"
        if not args.static_only:
            check_declarations(root, data)
        require(all(sha256(root / name) == digest for name, digest in report["metadata_sha256"].items()), "Metadata changed during validation; rerun with stable input files")
        report["validated_at_utc"] = datetime.now(timezone.utc).isoformat()
        (root / ".lake").mkdir(exist_ok=True)
        (root / ".lake/release-validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        kind = "STATIC RELEASE CHECKS" if args.static_only else "RELEASE CHECKS"
        print(f"{kind} PASSED: {report['result_rows']} mappings, {report['unique_mapped_declarations']} declarations, {report['baseline_proof_bodies_unchanged']} unchanged baseline proof bodies.")
        if args.static_only:
            print("Lean declarations were not checked; run without --static-only after compiling the proof library.")
    except (OSError, ValueError, KeyError, jsonschema.ValidationError) as exc:
        print(f"RELEASE VALIDATION FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
