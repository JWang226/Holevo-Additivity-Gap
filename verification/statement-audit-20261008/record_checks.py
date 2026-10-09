#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Record observed seven-root checks and publish the arXiv v2 review successor.

This is an incremental statement/axiom recorder, not a full proof rebuild or
independent kernel checker. Historical manifests, reports and logs stay exact.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = "verification/statement-audit-20261008"
MANIFEST = "verification/statement-audit-delta-20261008.json"
PARENT = "verification/statement-audit-delta-20261007.json"
REPORT = "docs/STATEMENT_AUDIT_V2.md"
CERTIFICATE = "verification/additive-20261008/source-certificate.json"
LEGACY_RECORDER = "verification/statement-audit-20261007/record_checks.py"
sys.path.insert(0, str(ROOT / "verification"))
import check_statement_audit as check

legacy = {"__file__": str(ROOT / LEGACY_RECORDER), "__name__": "retained_axiom_parser"}
exec(compile((ROOT / LEGACY_RECORDER).read_bytes(), LEGACY_RECORDER, "exec"), legacy)


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def write_json(name, value):
    (ROOT / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def run(argv, log):
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    (ROOT / log).write_text(result.stdout + result.stderr, encoding="utf-8")
    check.require(result.returncode == 0, f"Command failed ({result.returncode}): {log}")
    return {"command": argv, "exit_code": result.returncode, "log": log}


def make_review(parent, sources):
    explanations = {
        "paper/nonadditivity.tex": "Exact published arXiv v2 source; labeled principal statement blocks retained. Scope and exploration-encoding qualifications reviewed separately.",
        "metadata/results.json": "Version-pinned manuscript provenance, F mapping for an existing declaration, expanded root inventory and explicitly selected successor evidence; historical release record retained.",
        "scripts/check_challenges.py": "Adds the explicit application of actual_small_large and seven-root inventory; existing applications and production proofs unchanged.",
        "ComparatorChallenges/F_TwoUseSeparation.lean": "New explicit expected type, importing ActualConsequences without the solution module; binds actual finite channels and absolute two-use information.",
        "ComparatorChallenges/F_TwoUseSeparation.json": "Selects existing public theorem actual_small_large with the three permitted standard axioms and separate Nanoda mode.",
        "lakefile.toml": "Only appends the isolated F challenge root, validated against the historical Lake configuration by the additive certificate.",
        "formalization.yaml": "Adds the existing F theorem and seven-placeholder scope, without changing any production theorem.",
        "paper/arxiv-v2.json": "Binds exact arXiv version, original source archive and verbatim manuscript member.",
        "verification/manuscript-v2-20261008/source.tar.gz": "Original downloaded arXiv v2 archive; its manuscript member must equal the repository manuscript byte for byte.",
        "scripts/source_certificate.py": "Explicit bounded additive-certificate validation; rejects changed production proofs, original challenges and non-additive Lake edits.",
        "verification/kernel_common.py": "Expanded current inventory and binding of manuscript provenance and certificate checker for the fresh portable run.",
        "verification/check_statement_audit.py": "Adds a versioned review successor with explicit historical preservation, exact arXiv provenance, unchanged production inputs, F coverage and C correction checks.",
    }
    changes, patch = [], []
    for name in sorted(sources):
        previous = parent["source_bindings"].get(name)
        if previous == sources[name]:
            continue
        check.require(name in explanations, "Unreviewed changed input: " + name)
        changes.append({"path": name, "before_sha256": previous, "after_sha256": sources[name],
                        "review": explanations[name]})
        current = (ROOT / name).read_bytes()
        before = subprocess.run(["git", "show", "HEAD:" + name], cwd=ROOT, capture_output=True)
        if name.endswith(".tar.gz"):
            patch.append(f"Binary input {name}: SHA-256 {sources[name]}\n")
        else:
            old_text = before.stdout.decode("utf-8") if before.returncode == 0 else ""
            patch.extend(difflib.unified_diff(old_text.splitlines(True), current.decode("utf-8").splitlines(True),
                                             fromfile="a/" + name if before.returncode == 0 else "/dev/null",
                                             tofile="b/" + name))
    patch_name = OUT + "/reviewed-input-delta.patch"
    (ROOT / patch_name).write_text("".join(patch), encoding="utf-8")
    review = {"schema_version": 1, "review_kind": "arxiv_v2_and_additive_root_source_review",
              "machine_equivalence_certified": False, "semantic_report": REPORT,
              "changed_proof_sources": [], "changed_sources": changes,
              "patch": {"path": patch_name, "sha256": digest(patch_name)},
              "scope": "AI review of published manuscript delta and one added expected statement; unchanged historical definitions and qualifications retained, with explicit C coverage correction."}
    write_json(OUT + "/delta-review.json", review)
    return review


def make_entries(parent, targets):
    entries = deepcopy(parent["entries"])
    declarations = {item["name"]: item for item in check.read_json(ROOT, "metadata/declarations.json")["declarations"]}
    context = ["Nonadditivity/ActualConsequences.lean", "Nonadditivity/Channels.lean",
               "Nonadditivity/QuantumHolevo.lean", "Nonadditivity/StateEnsembles.lean",
               "paper/nonadditivity.tex", "paper/arxiv-v2.json", "metadata/results.json", "metadata/declarations.json"]
    corrections = {}
    for entry in entries:
        entry["historical_report"] = entry["report"]
        entry["report"] = REPORT
        entry["reviewer"] = "arxiv-v2-source-delta-ai-review"
        entry["reviewed_files"] = sorted(set(context + entry["reviewed_files"]))
        entry["delta_finding"] = "The published v2 retains this root's mathematical source statement and the production definitions are unchanged. Historical endpoint qualifications are retained; the current report separately reviews v2 scope and proof-encoding wording."
        if entry["id"] == "separation":
            old = entry["qualifications"]
            entry["qualifications"] = [
                "Common-witness small positive one-use information, large operational gain and large two-use ratio, proved using the alternate deterministic construction.",
                "This root does not assert an arbitrarily large absolute chiTwo/2, prescribed dimensions, or sequence limits; the absolute existential separation is checked separately by F.",
            ]
            entry["source_labels"] = ["cor:capacity", "eq:capacity", "eq:def-chi", "eq:ratio"]
            entry["delta_finding"] = "The root type is unchanged. This review explicitly corrects the historical stronger-conjunction claim: C does not imply an absolute chiTwo/2 lower bound, which is now directly checked by F."
            corrections[entry["declaration"]] = {
                "historical_qualifications": old, "current_qualifications": entry["qualifications"],
                "reason": "The old stronger-conjunction wording overstated root C: a capacity lower bound and two-use ratio do not imply an absolute lower bound on chiTwo/2. F directly checks that endpoint."}
    name = check.ADDED_TARGET
    entries.append({
        "id": "absolute-two-use-separation", "declaration": name,
        "type_sha256": declarations[name]["type_sha256"], "config": targets[name],
        "report": REPORT, "reviewer": "arxiv-v2-source-first-ai-review",
        "result_ids": ["small-large-and-sequence"], "source_labels": ["cor:separation", "eq:small-large", "eq:def-chi"],
        "reviewed_files": sorted(set(context + [declarations[name]["file"], targets[name],
                                                   str(Path(targets[name]).with_suffix(".lean")),
                                                   "Nonadditivity/DeterministicQualitative.lean"])),
        "verdict": "qualified", "qualifications": [
            "The theorem strengthens the finite existential manuscript clause by supplying positive chi and permitting any real R; the source assumes R>0.",
            "The witness uses the alternate deterministic finite-moment/damped construction and does not supply prescribed Haar dimensions.",
            "The exported root does not include named sequence convergence or an operational-capacity conjunct; those remain separate proved endpoints."]})
    return entries, corrections


def main():
    try:
        check.require(not (ROOT / MANIFEST).exists() and not (ROOT / OUT / "checks.json").exists(),
                      "Successor records already exist; preserve them and choose a new version")
        parent = check.read_json(ROOT, PARENT)
        parent_sha = digest(PARENT)
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        sources = {name: digest(name) for name in sorted(set(parent["source_bindings"]) | check.REVISION_SOURCES)}
        targets = check.current_targets(ROOT, check.CURRENT_CONFIGS)
        review = make_review(parent, sources)
        declarations = {item["name"]: item for item in check.read_json(ROOT, "metadata/declarations.json")["declarations"]}
        imports = sorted({declarations[name]["module"] for name in targets})
        roots_source = "\n".join("import " + module for module in imports) + "\n\n"
        roots_source += "\n".join(f"#check {name}\n#print axioms {name}" for name in targets) + "\n"
        (ROOT / OUT / "Roots.lean").write_text(roots_source)
        extras = {REPORT, OUT + "/record_checks.py", OUT + "/Roots.lean", OUT + "/delta-review.json",
                  OUT + "/reviewed-input-delta.patch", CERTIFICATE, LEGACY_RECORDER}
        inputs = sources | {name: digest(name) for name in sorted(extras)}
        commands = [run([sys.executable, "scripts/check_challenges.py"], OUT + "/check-challenges.log")]
        challenge_report = check.read_json(ROOT, ".lake/challenge-checks.json")
        check.require(challenge_report.get("status") == "passed" and challenge_report.get("theorems_checked") == 7
                      and challenge_report.get("challenge_modules_checked") == 6,
                      "The current expected-statement applications did not all pass")
        (ROOT / OUT / "challenge-checks.json").write_bytes((ROOT / ".lake/challenge-checks.json").read_bytes())
        copied = {OUT + "/challenge-checks.json"}
        for item in challenge_report["checks"]:
            generated = item["generated_statement_check"]
            archived = OUT + "/" + Path(generated).name
            (ROOT / archived).write_bytes((ROOT / generated).read_bytes())
            copied.add(archived)
            for key in ("challenge_elaboration", "proof_against_expected_statement"):
                child = item[key]
                check.require(child.get("status") == "passed" and type(child.get("exit_code")) is int
                              and child["exit_code"] == 0, "A recorded statement command failed")
                archived = OUT + "/" + Path(child["log"]).name
                (ROOT / archived).write_bytes((ROOT / child["log"]).read_bytes())
                commands.append({"command": child["command"], "exit_code": 0, "log": archived})
        commands.append(run(["./lean.sh", OUT + "/Roots.lean"], OUT + "/roots.log"))
        axioms = legacy["parse_root_axioms"]((ROOT / OUT / "roots.log").read_text(), targets)
        check.require(all(digest(name) == sha for name, sha in inputs.items()), "Statement-check inputs changed during execution")
        check.require(digest(PARENT) == parent_sha, "Historical parent changed")
        logs = {item["log"]: digest(item["log"]) for item in commands}
        logs.update({name: digest(name) for name in copied})
        evidence = {"schema_version": 1, "status": "passed", "scope": check.SCOPE,
                    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "source_commit": actual,
                    "worktree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
                    "theorem_names": list(targets), "permitted_axioms": sorted(check.AXIOMS),
                    "root_axioms": axioms, "inputs": inputs, "logs": logs, "commands": commands,
                    "compiled_sources_from_scratch": False, "comparator_rerun": False, "nanoda_rerun": False,
                    "notes": ["Observed incremental exact-statement applications and seven root type/axiom closures.",
                              "The separately selected portable record establishes full rebuild and independent kernel executions.",
                              "Source hashes identify dirty-checkout inputs; the base commit alone does not identify this revision."]}
        write_json(OUT + "/checks.json", evidence)
        entries, corrections = make_entries(parent, targets)
        reports = dict(parent["report_bindings"])
        reports.update({name: digest(name) for name in (REPORT, OUT + "/delta-review.json", OUT + "/reviewed-input-delta.patch")})
        audit = {"schema_version": 3, "review_kind": "manuscript_revision_and_additive_root_ai_review",
                 "review_date": "2026-10-08", "machine_equivalence_certified": False,
                 "reviewed_commit": actual, "parent_audit": {"path": PARENT, "sha256": parent_sha},
                 "method": {"scope": "Published manuscript delta and F source-first review; historical qualified endpoints retained, with explicit root C coverage correction.",
                            "review_report": REPORT, "independent_human_certification": False},
                 "source_bindings": sources, "report_bindings": reports, "changed_sources": review["changed_sources"],
                 "source_delta_review": {"path": OUT + "/delta-review.json", "sha256": digest(OUT + "/delta-review.json")},
                 "source_certificate": {"path": CERTIFICATE, "sha256": digest(CERTIFICATE)},
                 "meaning_carrying_definition_changes": [], "correspondence_corrections": corrections,
                 "entries": entries, "mechanical_evidence": {"path": OUT + "/checks.json", "sha256": digest(OUT + "/checks.json")}}
        write_json(MANIFEST, audit)
        check.load_audit(ROOT, MANIFEST)
        write_json(check.CURRENT_AUDIT_PATH, {"schema_version": 1,
                   "audit": {"path": MANIFEST, "sha256": digest(MANIFEST)},
                   "scope": "Published arXiv v2 and additive F review, retaining qualified historical findings with explicit C coverage correction; not machine-certified semantic equivalence."})
        print("Recorded observed seven-root checks and arXiv v2 review: " + MANIFEST)
        return 0
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print("STATEMENT V2 CAPTURE FAILED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
