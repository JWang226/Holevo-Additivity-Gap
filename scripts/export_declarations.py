#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Export actual project constant types and expression dependencies from Lean.

From a checkout with ``lake build All`` already completed, run:

    python3 scripts/export_declarations.py

``./lean.sh`` also supports a compatible local compiler and previously built
offline objects. Logs and raw output remain in .lake/. No proofs are rebuilt by
this exporter. The imported All objects must come from the current sources;
building All and running the audit is the separate proof verification step.

Completed records are checkpointed in .lake/ and resumed when the proof inputs
and extractor semantics version match. ``--fresh`` ignores that checkpoint;
``--check`` always performs a fresh export and compares decoded type bytes and
all other metadata. Gzip streams may differ between zlib versions. Output has
no wall-clock timestamp and is sorted deterministically.
"""

from __future__ import annotations

import argparse
import base64
from collections import Counter
import hashlib
import gzip
import io
import json
import os
import re
from pathlib import Path
import subprocess
import sys


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tracked_inputs(root: Path) -> dict[str, str]:
    sources = [root / "Nonadditivity.lean", root / "Audit.lean", root / "All.lean"]
    sources += sorted((root / "Nonadditivity").rglob("*.lean"))
    sources += [root / "lean-toolchain", root / "lake-manifest.json", root / "lakefile.toml"]
    sources += [root / "scripts/export_declarations.lean", root / "scripts/export_declarations.py"]
    return {path.relative_to(root).as_posix(): sha256(path) for path in sorted(sources)}


def proof_source_commit(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "log", "-1", "--format=%H", "--", "Nonadditivity", "Nonadditivity.lean", "Audit.lean", "All.lean"],
            cwd=root, text=True, stderr=subprocess.DEVNULL,
        ).strip() or None
    except (OSError, subprocess.CalledProcessError):
        return None


EXTRACTOR_SEMANTICS_VERSION = "declaration-export-v3-kernel-expr-dag-v1-structural-roundtrip-readable-projection-refs"


def compiler_identity(root: Path) -> tuple[str, str]:
    result = subprocess.run([str(root / "lean.sh"), "--version"], cwd=root,
                            text=True, capture_output=True, check=False)
    match = re.search(r"version ([^,]+),.*?commit ([0-9a-f]+)", result.stdout)
    if result.returncode or not match:
        raise ValueError("Cannot identify the actual Lean compiler: " + result.stdout + result.stderr)
    expected = (root / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
    if match.group(1) != expected:
        raise ValueError(f"Running Lean {match.group(1)} differs from pinned toolchain {expected}")
    return match.group(1), match.group(2)


def encode_type(text: str) -> dict:
    original = text.encode("utf-8")
    compressed = io.BytesIO()
    with gzip.GzipFile(fileobj=compressed, mode="wb", filename="", mtime=0, compresslevel=9) as handle:
        handle.write(original)
    return {
        "type": base64.b64encode(compressed.getvalue()).decode("ascii"),
        "type_encoding": "gzip+base64",
        "type_sha256": hashlib.sha256(original).hexdigest(),
        "type_uncompressed_bytes": len(original),
    }


def decoded_type(record: dict) -> bytes:
    if record.get("type_encoding") != "gzip+base64":
        raise ValueError(f"Unsupported type encoding: {record['name']}")
    data = gzip.decompress(base64.b64decode(record["type"], validate=True))
    if len(data) != record["type_uncompressed_bytes"] or hashlib.sha256(data).hexdigest() != record["type_sha256"]:
        raise ValueError(f"Full type size or SHA256 mismatch: {record['name']}")
    data.decode("utf-8")
    return data


def semantic_equal(left: dict, right: dict) -> bool:
    if left.keys() != right.keys():
        return False
    if {key: value for key, value in left.items() if key != "declarations"} != {
        key: value for key, value in right.items() if key != "declarations"
    }:
        return False
    if len(left["declarations"]) != len(right["declarations"]):
        return False
    for before, after in zip(left["declarations"], right["declarations"]):
        if {key: value for key, value in before.items() if key != "type"} != {
            key: value for key, value in after.items() if key != "type"
        } or decoded_type(before) != decoded_type(after):
            return False
    return True


def repair_last_checkpoint_line(path: Path) -> None:
    # Do not read a multi-gigabyte raw checkpoint into memory. A flushed record
    # ends in a newline; preserve those records and remove only a partial tail.
    with path.open("r+b") as handle:
        handle.seek(0, os.SEEK_END)
        size = handle.tell()
        if not size:
            return
        handle.seek(size - 1)
        if handle.read(1) == b"\n":
            return
        position = size
        while position:
            start = max(0, position - 65536)
            handle.seek(start)
            block = handle.read(position - start)
            end = block.rfind(b"\n")
            if end >= 0:
                handle.truncate(start + end + 1)
                return
            position = start
        handle.truncate(0)


def export(root: Path, *, fresh: bool = False, package_checkpoint: bool = False) -> dict:
    scratch = root / ".lake"
    scratch.mkdir(exist_ok=True)
    raw_path = scratch / "declarations.raw.json"
    log_path = scratch / "export-declarations.log"
    inputs = tracked_inputs(root)
    lean_version, lean_commit = compiler_identity(root)
    checkpoint_path = scratch / "declarations.records.jsonl"
    checkpoint_meta = scratch / "declarations.checkpoint.json"
    checkpoint_identity = {
        "format": EXTRACTOR_SEMANTICS_VERSION,
        "source_sha256": {key: value for key, value in inputs.items() if not key.startswith("scripts/")},
    }
    old_identity = json.loads(checkpoint_meta.read_text()) if checkpoint_meta.is_file() else None
    if package_checkpoint and old_identity != checkpoint_identity:
        raise ValueError("Completed checkpoint does not match current proof inputs and extractor semantics")
    if fresh or old_identity != checkpoint_identity:
        checkpoint_path.unlink(missing_ok=True)
    elif checkpoint_path.is_file():
        repair_last_checkpoint_line(checkpoint_path)
    checkpoint_meta.write_text(json.dumps(checkpoint_identity, sort_keys=True, indent=2) + "\n")
    cache_path = scratch / "declarations.readable-cache.jsonl"
    cache_meta = scratch / "declarations.readable-cache.identity.json"
    cache_identity = {
        "format": "readable-pp-fullNames-universes-privateNames-width100-v1",
        "source_sha256": checkpoint_identity["source_sha256"],
    }
    old_cache_identity = json.loads(cache_meta.read_text()) if cache_meta.is_file() else None
    # Adopt the preserved same-source cache from the earlier exporter once;
    # every later reuse requires the cache's own explicit source identity.
    adopt = old_cache_identity is None and old_identity is not None and old_identity.get("source_sha256") == cache_identity["source_sha256"]
    if old_cache_identity != cache_identity and not adopt:
        cache_path.unlink(missing_ok=True)
    cache_meta.write_text(json.dumps(cache_identity, sort_keys=True, indent=2) + "\n")
    env = os.environ.copy()
    env["NONADDITIVITY_DECLARATIONS_RAW"] = str(raw_path)
    env["NONADDITIVITY_DECLARATIONS_RECORDS"] = str(checkpoint_path)
    env["NONADDITIVITY_DECLARATIONS_PROGRESS"] = str(scratch / "export-declarations-progress.json")
    env["NONADDITIVITY_DECLARATIONS_READABLE_CACHE"] = str(scratch / "declarations.no-readable-cache" if fresh else cache_path)
    env.pop("NONADDITIVITY_DECLARATION_LIMIT", None)
    if not package_checkpoint:
        raw_path.unlink(missing_ok=True)
        with log_path.open("w", encoding="utf-8") as log:
            proc = subprocess.run(
                [str(root / "lean.sh"), "scripts/export_declarations.lean"],
                cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, check=False,
            )
        if proc.returncode or not raw_path.is_file():
            print(log_path.read_text(encoding="utf-8")[-8000:], file=sys.stderr)
            raise ValueError(f"Lean export failed; see {log_path}")
    if inputs != tracked_inputs(root):
        raise ValueError("Export inputs changed during the Lean run; export again")
    completed = re.search(r"DECLARATION EXPORT PASSED: (\d+) project constants", log_path.read_text(encoding="utf-8"))
    if not completed or not raw_path.is_file():
        raise ValueError("No completed Lean export evidence; partial checkpoints cannot be published")
    declarations = []
    with checkpoint_path.open("r", encoding="utf-8") as records:
        for line in records:
            declaration = json.loads(line)
            full_type = declaration["type"]
            dag = json.loads(full_type)
            if declaration.get("type_representation") != "lean-kernel-expr-dag-v1" or dag.get("format") != "lean-kernel-expr-dag-v1":
                raise ValueError(f"Unexpected kernel type representation: {declaration['name']}")
            declaration.update(encode_type(full_type))
            declarations.append(declaration)
    declarations.sort(key=lambda declaration: declaration["name"])
    names = {declaration["name"] for declaration in declarations}
    if len(names) != int(completed.group(1)) or len(declarations) != int(completed.group(1)):
        raise ValueError("Export declaration count or name uniqueness is inconsistent")
    baseline = json.loads((root / "verification/baseline-verification.json").read_text(encoding="utf-8"))
    expected = baseline["audited_project_declarations"]
    if len(names) != expected:
        raise ValueError(f"Lean export has {len(names)} constants, audited inventory has {expected}")
    theorem_count = sum(item["kind"] == "theorem" for item in declarations)
    expected_theorems = baseline["audited_theorem_constants_including_generated_helpers"]
    if theorem_count != expected_theorems:
        raise ValueError(f"Lean export has {theorem_count} theorems, audited inventory has {expected_theorems}")
    modules = {}
    for declaration in declarations:
        if not declaration["name"].startswith(("Nonadditivity.", "_private.Nonadditivity.")):
            raise ValueError(f"Exported name is outside Audit's project prefixes: {declaration['name']}")
        if not (root / declaration["file"]).is_file():
            raise ValueError(f"Defining module source is absent: {declaration['file']}")
        modules[declaration["module"]] = declaration["file"]
        for key in ("type_dependencies", "value_dependencies", "project_dependencies"):
            declaration[key] = sorted(set(declaration[key]))
        missing = set(declaration["project_dependencies"]) - names
        if missing:
            raise ValueError(f"Project dependency has no exported constant: {sorted(missing)}")
        source_range = declaration["source_range"]
        if source_range is not None:
            line_count = len((root / declaration["file"]).read_text(encoding="utf-8").splitlines())
            if not 1 <= source_range["start_line"] <= source_range["end_line"] <= line_count:
                raise ValueError(f"Invalid Lean source range: {declaration['name']}")
    return {
        "schema_version": 1,
        "provenance": {
            "method": "Lean environment imported from All; not source-text declaration scanning",
            "lean_toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "actual_lean_version": lean_version,
            "actual_lean_commit": lean_commit,
            "proof_source_commit": proof_source_commit(root),
            "source_sha256": inputs,
            "hash_algorithm": "sha256",
            "selection": "Structural Lean Name prefixes Nonadditivity. and _private.Nonadditivity.; exporter checks equality with Audit's literal printed-name prefix predicate over every imported constant, with the same audited inventory counts.",
            "type_format": "Canonical compact Lean kernel Expr DAG, format lean-kernel-expr-dag-v1; all arguments, universe levels, binder kinds, let nonDep flags, projections, literal values and Name components preserved. Expr.mdata annotations alone are omitted as kernel-semantically irrelevant; closed compiled types must have no fvars/mvars. Each JSON DAG is decoded back into Lean Expr and structurally compared with the original compiled type after recursive mdata removal before export.",
            "type_encoding": "Lossless gzip+base64 of UTF-8 canonical kernel type DAG JSON, empty gzip filename and mtime=0; type_sha256 and type_uncompressed_bytes describe the decoded JSON. Compression streams may vary with zlib; --check compares decoded canonical JSON bytes and all other metadata.",
            "extractor_semantics_version": EXTRACTOR_SEMANTICS_VERSION,
            "type_readable_format": "Lean PrettyPrinter.ppExpr of the same type; pp.all=false, pp.fullNames=true, pp.universes=true, pp.privateNames=true, pp.maxSteps=10000000; width=100. Default notation and implicit/proof argument elision are retained; complete kernel expression DAG is in type.",
            "dependencies": "Direct constant and structure-projection names occurring in elaborated type or value; no unfolding or transitive closure. Proof terms are not exported.",
            "dependency_limitations": "Inductive constructor lists and recursor reduction rules are not expression-value edges. References outside the project remain in type_dependencies/value_dependencies but have no local browser record.",
            "source_ranges": "All source_range fields are null. Imported baseline objects may carry declaration positions from before publication copyright headers were added. Defining module/file links are authoritative; no line positions are guessed.",
            "internal_flags": "Lean Name.isInternal, Lean isPrivateName and Lean Name.isInternalDetail; these flags do not classify all generated declarations.",
            "verification_scope": "This export inspects already compiled objects. Build All and run Audit to verify the proofs; the export is not an independent kernel or Comparator run.",
        },
        "count": len(declarations),
        "module_count": len(modules),
        "kind_counts": dict(sorted(Counter(item["kind"] for item in declarations).items())),
        "modules": dict(sorted(modules.items())),
        "declarations": declarations,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, help="Default: metadata/declarations.json under project root")
    parser.add_argument("--check", action="store_true", help="Re-export and compare to the existing output")
    parser.add_argument("--fresh", action="store_true", help="Ignore completed record checkpoints")
    parser.add_argument("--package-checkpoint", action="store_true", help="Package a completed matching Lean export without rerunning Lean")
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output.resolve() if args.output else root / "metadata/declarations.json"
    try:
        if args.package_checkpoint and (args.check or args.fresh):
            raise ValueError("--package-checkpoint cannot be combined with --check or --fresh")
        result = export(root, fresh=args.fresh or args.check, package_checkpoint=args.package_checkpoint)
        text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
        if args.check:
            if not semantic_equal(json.loads(output.read_text(encoding="utf-8")), result):
                raise ValueError(f"Fresh Lean export differs from {output}; regenerate before publication")
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            temporary = output.with_suffix(output.suffix + ".tmp")
            temporary.write_text(text, encoding="utf-8")
            temporary.replace(output)
        print(f"DECLARATION EXPORT PASSED: {result['count']} constants, {result['module_count']} defining modules; {output.relative_to(root) if output.is_relative_to(root) else output}")
        print(f"Theorems: {result['kind_counts'].get('theorem', 0)}; source metadata and direct expression references exported.")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"DECLARATION EXPORT FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
