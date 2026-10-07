#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Run and record current-source statement checks after the project is built.

This publishes a delta continuation only on observed success. It never rebuilds
the proof library or executes Comparator/Nanoda, and never edits its parent.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = "verification/statement-audit-20261007"
DELTA = "verification/statement-audit-delta-20261007.json"
REPORT = "docs/STATEMENT_AUDIT_DELTA.md"
CHECKER = ROOT / "verification/check_statement_audit.py"
namespace = {"__file__": str(CHECKER), "__name__": "statement_audit_checker"}
exec(compile(CHECKER.read_bytes(), str(CHECKER), "exec"), namespace)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def write_json(name: str, value: dict) -> None:
    (ROOT / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def run(command: list[str], log: str) -> dict:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    (ROOT / log).write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        raise ValueError(f"Command failed ({result.returncode}): see {log}")
    return {"command": command, "exit_code": result.returncode, "log": log}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-commit", required=True,
                        help="Actual frozen checkout used for these incremental checks")
    parser.add_argument("--public-types", default="verification/elaboration-20261006/public-types.json",
                        help="Current fresh exact public-type comparison; repository-relative JSON")
    args = parser.parse_args()
    require = namespace["require"]
    try:
        actual = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True,
                                capture_output=True, text=True).stdout.strip()
        require(re.fullmatch(r"[0-9a-f]{40}", args.source_commit) is not None
                and actual == args.source_commit, "--source-commit must be the actual current checkout")
        require(not (ROOT / DELTA).exists() and not (ROOT / OUT / "checks.json").exists(),
                "Current statement records already exist; preserve them and create a versioned successor")
        parent = namespace["read_json"](ROOT, namespace["AUDIT_PATH"])
        parent_sha = digest(namespace["AUDIT_PATH"])
        sources = {name: digest(name) for name in sorted(parent["source_bindings"])}
        require(namespace["required_sources"](ROOT) <= sources.keys(), "Current proof inventory changed")
        review = namespace["read_json"](ROOT, OUT + "/delta-review.json")
        for change in review["changed_proof_sources"]:
            require(sources[change["path"]] == change["after_sha256"], "Reviewed proof delta changed")
        namespace["hash_bindings"](ROOT, {review["patch"]["path"]: review["patch"]["sha256"]}, "reviewed delta patch")
        old_metadata = json.loads(subprocess.run(
            ["git", "show", review["before_commit"] + ":metadata/results.json"], cwd=ROOT,
            check=True, capture_output=True, text=True).stdout)
        current_metadata = namespace["read_json"](ROOT, "metadata/results.json")
        # New references/status records may be added alongside the reviewed map.
        # Every previously reviewed mathematical mapping and limitation stays exact.
        release_fields = {"verification_current", "statement_audit_current", "verification_release",
                          "portable_verification_current"}
        require({key: value for key, value in old_metadata.items() if key not in release_fields}
                == {key: value for key, value in current_metadata.items() if key not in release_fields},
                "Result metadata changed beyond current release evidence references")
        namespace["local_file"](ROOT, args.public_types)
        extras = {REPORT, OUT + "/Roots.lean", OUT + "/record_checks.py", OUT + "/delta-review.json",
                  OUT + "/proof-source-delta.patch", "verification/check_statement_audit.py",
                  "verification/elaboration-20261006/dead-code.json", args.public_types}
        inputs = sources | {name: digest(name) for name in sorted(extras)}
        commands = [run([sys.executable, "scripts/check_challenges.py"], OUT + "/check-challenges.log")]
        challenge_report = namespace["read_json"](ROOT, ".lake/challenge-checks.json")
        require(challenge_report.get("status") == "passed"
                and challenge_report.get("theorems_checked") == 6
                and challenge_report.get("challenge_modules_checked") == 5,
                "Current exact-statement applications did not all pass")
        (ROOT / OUT / "challenge-checks.json").write_bytes((ROOT / ".lake/challenge-checks.json").read_bytes())
        for item in challenge_report["checks"]:
            generated = item["generated_statement_check"]
            (ROOT / OUT / Path(generated).name).write_bytes((ROOT / generated).read_bytes())
            for key in ("challenge_elaboration", "proof_against_expected_statement"):
                record = item[key]
                require(record.get("exit_code") == 0, "A recorded statement command failed")
                archived = OUT + "/" + Path(record["log"]).name
                (ROOT / archived).write_bytes((ROOT / record["log"]).read_bytes())
                commands.append({"command": record["command"], "exit_code": 0, "log": archived})
        commands.append(run(["./lean.sh", OUT + "/Roots.lean"], OUT + "/roots.log"))
        text = (ROOT / OUT / "roots.log").read_text(encoding="utf-8")
        roots = namespace["current_targets"](ROOT)
        axioms = {}
        for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
            require(name in roots and name not in axioms, "Wrong or duplicate root axiom record")
            axioms[name] = sorted(value.strip() for value in values.split(",") if value.strip())
        require(set(axioms) == set(roots) and all(set(values) == namespace["AXIOMS"] for values in axioms.values()),
                "The root axiom probe did not record exactly the six permitted closures")
        require(not re.search(r"\berror:|\bsorryAx\b|declaration uses 'sorry'", text), "Root probe contains an error or hole")
        require(all(digest(name) == sha for name, sha in inputs.items()), "Statement-check inputs changed during execution")
        require(digest(namespace["AUDIT_PATH"]) == parent_sha, "Historical statement audit changed")
        logs = {record["log"]: digest(record["log"]) for record in commands}
        logs[OUT + "/challenge-checks.json"] = digest(OUT + "/challenge-checks.json")
        for item in challenge_report["checks"]:
            name = OUT + "/" + Path(item["generated_statement_check"]).name
            logs[name] = digest(name)
        evidence = {
            "schema_version": 1, "status": "passed", "scope": namespace["SCOPE"],
            "checked_at_utc": datetime.now(timezone.utc).isoformat(), "source_commit": actual,
            "theorem_names": list(roots), "permitted_axioms": sorted(namespace["AXIOMS"]),
            "inputs": inputs, "logs": logs, "commands": commands, "root_axioms": axioms,
            "compiled_sources_from_scratch": False, "comparator_rerun": False, "nanoda_rerun": False,
            "notes": ["Actual incremental expected-statement applications and type/axiom probe; project objects reused.",
                      "Fresh full project rebuild, Comparator and Nanoda executions have separate release records.",
                      "Generated check sources and original command outputs are copied exactly; commands retain their execution paths."],
        }
        write_json(OUT + "/checks.json", evidence)
        reports = dict(parent["report_bindings"])
        reports[REPORT] = digest(REPORT)
        reports[OUT + "/delta-review.json"] = digest(OUT + "/delta-review.json")
        reports[OUT + "/proof-source-delta.patch"] = digest(OUT + "/proof-source-delta.patch")
        entries = deepcopy(parent["entries"])
        decls = {item["name"]: item for item in namespace["read_json"](ROOT, "metadata/declarations.json")["declarations"]}
        context = ["Nonadditivity/Channels.lean", "Nonadditivity/ActualConsequences.lean",
                   "Nonadditivity/QuantumHolevo.lean", "Nonadditivity/StateEnsembles.lean",
                   "Nonadditivity/RegularCoefficientEnergy.lean", "paper/nonadditivity.tex",
                   "metadata/declarations.json", "metadata/results.json"]
        for entry in entries:
            entry["historical_report"] = entry["report"]
            entry["report"] = REPORT
            entry["reviewer"] = "cleanup-delta-ai-reviewer"
            entry["reviewed_files"] = sorted(set(context + [decls[entry["declaration"]]["file"],
                                                entry["config"], str(Path(entry["config"]).with_suffix(".lean"))]))
            entry["delta_finding"] = "No changed root statement or meaning-carrying definition; reviewed cleanup preserves this endpoint with every historical qualification retained. See the per-root context in the delta report."
        changes = []
        proof_changes = {item["path"]: item for item in review["changed_proof_sources"]}
        for name in sorted(sources):
            if sources[name] == parent["source_bindings"][name]:
                continue
            if name in proof_changes:
                kind = proof_changes[name]["kind"]
                explanation = "Reviewed exact source patch: " + kind.replace("_", " ") + "; data-valued definitions and all theorem types preserved."
            elif name == "metadata/declarations.json":
                kind, explanation = "fresh_declaration_export", "Fresh complete declaration metadata; exact canonical public types checked against the historical export."
            elif name == "metadata/results.json":
                kind, explanation = "release_metadata_only", "Current evidence references only; the recorder verified every other top-level mathematical/result-map field unchanged."
            else:
                raise ValueError("An unreviewed source input changed: " + name)
            changes.append({"path": name, "before_sha256": parent["source_bindings"][name],
                            "after_sha256": sources[name], "kind": kind, "review": explanation})
        audit = {
            "schema_version": 2, "review_kind": "incremental_ai_source_semantics_review",
            "review_date": datetime.now(timezone.utc).date().isoformat(),
            "machine_equivalence_certified": False, "reviewed_commit": actual,
            "parent_audit": {"path": namespace["AUDIT_PATH"], "sha256": parent_sha},
            "method": {"scope": "AI source-delta review and six endpoint-definition-context checks; historical independent reviews retained, not repeated in full.",
                       "review_report": REPORT, "cross_review": "Release integration cross-check; no independent human certification."},
            "source_bindings": sources, "report_bindings": reports, "changed_sources": changes,
            "source_delta_review": {"path": OUT + "/delta-review.json", "sha256": digest(OUT + "/delta-review.json")},
            "meaning_carrying_definition_changes": [], "entries": entries,
            "public_type_comparison": {"path": args.public_types, "sha256": digest(args.public_types)},
            "mechanical_evidence": {"path": OUT + "/checks.json", "sha256": digest(OUT + "/checks.json")},
        }
        # Validate all actual evidence before publishing a selected current record.
        namespace["check_delta"](ROOT, audit, sources, reports)
        namespace["check_mechanical"](ROOT, audit, sources, roots)
        write_json(DELTA, audit)
        namespace["load_audit"](ROOT, DELTA)
        write_json(namespace["CURRENT_AUDIT_PATH"], {
            "schema_version": 1, "audit": {"path": DELTA, "sha256": digest(DELTA)},
            "scope": "Historical independent reviews continued by the current cleanup delta; not machine-certified semantic equivalence.",
        })
        print(f"Recorded current statement applications, six root closures and delta continuation: {DELTA}")
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print("STATEMENT DELTA CAPTURE FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
