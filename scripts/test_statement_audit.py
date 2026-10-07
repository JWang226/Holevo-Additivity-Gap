#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Negative controls for statement-review freshness, using synthetic files only.

No Lean process runs, no actual review is restamped, and these tests make no
mathematical assertion about the six production theorems.
"""
from __future__ import annotations

from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

CHECKER = Path(__file__).resolve().parents[1] / "verification/check_statement_audit.py"
SPEC = importlib.util.spec_from_file_location("statement_audit", CHECKER)
check = importlib.util.module_from_spec(SPEC)
# Keep the tests from writing a bytecode cache into the repository.
exec(compile(CHECKER.read_bytes(), str(CHECKER), "exec"), check.__dict__)


class StatementAuditControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="statement-audit-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "repo"
        self.root.mkdir()
        for name in check.FIXED_SOURCES:
            self.write(name, "synthetic input: " + name + "\n")
        self.write("Nonadditivity/Fixture.lean", "-- Synthetic declaration source\n")
        self.write("Nonadditivity/Definitions.lean", "-- Synthetic definition source\n")
        self.write("paper/nonadditivity.tex", r"\label{thm:fixture}" + "\n")
        self.targets = []
        declarations, results, entries = [], [], []
        reports = {}
        for index, config_path in enumerate(check.CONFIGS):
            names = ["Fixture.target" + str(index)]
            if index == 4:
                names.append("Fixture.target5")
            self.targets.extend(names)
            config = {
                "challenge_module": config_path.removesuffix(".json").replace("/", "."),
                "solution_module": "Nonadditivity.Fixture", "theorem_names": names,
                "permitted_axioms": sorted(check.AXIOMS), "enable_nanoda": False,
            }
            self.write_json(config_path, config)
            report_path = "docs/AUDIT_" + str(index) + ".md"
            self.write(report_path, "Synthetic review; no mathematical claim.\n")
            reports[report_path] = check.digest(self.root / report_path)
            result_id = "result-" + str(index)
            results.append({
                "id": result_id, "comparator_config": config_path,
                "lean": [{"declaration": name, "file": "Nonadditivity/Fixture.lean"} for name in names],
            })
            for name in names:
                declarations.append({"name": name, "kind": "theorem",
                                     "file": "Nonadditivity/Fixture.lean", "type_readable": "True"})
                entries.append({
                    "id": "audit-" + name, "declaration": name, "config": config_path,
                    "report": report_path, "reviewer": "synthetic-reviewer-" + str(index),
                    "result_ids": [result_id], "source_labels": ["thm:fixture"],
                    "reviewed_files": ["Nonadditivity/Fixture.lean", "Nonadditivity/Definitions.lean"],
                    "verdict": "consistent", "qualifications": [],
                })
        self.write_json("metadata/declarations.json", {"declarations": declarations})
        self.write_json("metadata/results.json", {"results": results})
        sources = {name: check.digest(self.root / name) for name in check.required_sources(self.root)}
        self.log = "verification/statement-audit-20261006/exact-types.log"
        self.write(self.log, "Synthetic command log; Lean was not executed.\n")
        self.evidence_path = "verification/statement-audit-20261006/checks.json"
        self.evidence = {
            "status": "passed", "scope": check.SCOPE, "source_commit": "a" * 40,
            "theorem_names": self.targets.copy(), "permitted_axioms": sorted(check.AXIOMS),
            "root_axioms": {name: sorted(check.AXIOMS) for name in self.targets},
            "inputs": sources.copy(), "logs": {self.log: check.digest(self.root / self.log)},
            "commands": [{"command": ["synthetic-command", "--not-executed"],
                          "exit_code": 0, "log": self.log}],
            "compiled_sources_from_scratch": False, "comparator_rerun": False, "nanoda_rerun": False,
        }
        self.audit = {
            "schema_version": 1, "review_kind": "independent_ai_source_semantics_review",
            "machine_equivalence_certified": False, "reviewed_commit": "a" * 40,
            "source_bindings": sources, "report_bindings": reports, "entries": entries,
        }
        self.save_evidence()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def write_json(self, name, value):
        self.write(name, json.dumps(value, indent=2) + "\n")

    def save_audit(self):
        self.write_json(check.AUDIT_PATH, self.audit)

    def save_evidence(self):
        self.write_json(self.evidence_path, self.evidence)
        self.audit["mechanical_evidence"] = {
            "path": self.evidence_path, "sha256": check.digest(self.root / self.evidence_path)}
        self.save_audit()

    def reseal_fixture_source(self, name):
        """Update synthetic hashes to reach reference validation after a mutation."""
        sha = check.digest(self.root / name)
        self.audit["source_bindings"][name] = sha
        self.evidence["inputs"][name] = sha
        self.save_evidence()

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            check.load_audit(self.root)

    def test_fresh_synthetic_record_and_shared_e_result_are_accepted(self):
        loaded = check.load_audit(self.root)
        self.assertEqual(len(loaded["entries"]), 6)
        self.assertEqual(loaded["entries"][-1]["result_ids"], loaded["entries"][-2]["result_ids"])
        self.assertIs(loaded["machine_equivalence_certified"], False)

    def test_qualified_mismatch_and_unresolved_verdicts_are_preserved(self):
        for verdict in ("qualified", "mismatch", "unresolved"):
            with self.subTest(verdict=verdict):
                self.audit["entries"][0]["verdict"] = verdict
                self.audit["entries"][0]["qualifications"] = ["Synthetic review qualification."]
                self.save_audit()
                loaded = check.load_audit(self.root)
                self.assertEqual(loaded["entries"][0]["verdict"], verdict)
                self.assertIs(loaded["machine_equivalence_certified"], False)

    def test_changed_paper_definition_report_log_and_type_metadata_are_rejected(self):
        cases = {
            "paper/nonadditivity.tex": "Stale source bindings",
            "Nonadditivity/Definitions.lean": "Stale source bindings",
            "metadata/declarations.json": "Stale source bindings",
            "docs/AUDIT_0.md": "Stale report bindings",
            self.log: "Stale mechanical logs",
            self.evidence_path: "Stale mechanical evidence",
        }
        for name, message in cases.items():
            with self.subTest(file=name):
                path = self.root / name
                before = path.read_bytes()
                if name == "metadata/declarations.json":
                    metadata = json.loads(before)
                    metadata["declarations"][0]["type_readable"] = "False"
                    self.write_json(name, metadata)
                else:
                    path.write_bytes(before + b"changed\n")
                try:
                    self.reject(message)
                finally:
                    path.write_bytes(before)

    def test_new_nested_proof_source_requires_a_binding(self):
        self.write("Nonadditivity/New/NestedProof.lean", "-- New source\n")
        self.reject("Unbound current source files: Nonadditivity/New/NestedProof.lean")

    def test_omitting_existing_definition_source_is_rejected(self):
        self.audit["source_bindings"].pop("Nonadditivity/Definitions.lean")
        self.save_audit()
        self.reject("Unbound current source files")

    def test_wrong_or_duplicate_target_and_wrong_config_are_rejected(self):
        original = self.audit["entries"][0].copy()
        changes = (
            ({"declaration": "Fixture.unknown"}, "Wrong or duplicate audit target"),
            ({"declaration": self.targets[1]}, "Audit target/config mismatch"),
            ({"config": check.CONFIGS[1]}, "Audit target/config mismatch"),
        )
        for replacement, message in changes:
            with self.subTest(change=replacement):
                self.audit["entries"][0] = original | replacement
                self.save_audit()
                self.reject(message)
        self.audit["entries"][0] = original
        self.audit["entries"][1]["declaration"] = self.targets[0]
        self.save_audit()
        self.reject("Wrong or duplicate audit target")

    def test_duplicate_entry_id_is_rejected(self):
        self.audit["entries"][1]["id"] = self.audit["entries"][0]["id"]
        self.save_audit()
        self.reject("Duplicate statement-audit entry ID")

    def test_missing_target_or_non_theorem_metadata_is_rejected_after_rebinding(self):
        name = "metadata/declarations.json"
        metadata = json.loads((self.root / name).read_text())
        original = metadata["declarations"][0].copy()
        for change in ({"name": "Fixture.other"}, {"kind": "definition"}):
            with self.subTest(change=change):
                metadata["declarations"][0] = original | change
                self.write_json(name, metadata)
                self.reseal_fixture_source(name)
                self.reject("Audit target is not an exported theorem")

    def test_unknown_and_unrelated_result_ids_are_rejected(self):
        for result_ids, message in ((["unknown"], "Unknown cited result ID"),
                                    (["result-1"], "Cited results do not contain audit target")):
            with self.subTest(results=result_ids):
                self.audit["entries"][0]["result_ids"] = result_ids
                self.save_audit()
                self.reject(message)

    def test_result_config_mismatch_is_rejected_after_rebinding(self):
        name = "metadata/results.json"
        metadata = json.loads((self.root / name).read_text())
        metadata["results"][0]["comparator_config"] = check.CONFIGS[1]
        self.write_json(name, metadata)
        self.reseal_fixture_source(name)
        self.reject("Result/target Comparator configuration mismatch")

    def test_result_source_mismatch_is_rejected_after_rebinding(self):
        name = "metadata/results.json"
        metadata = json.loads((self.root / name).read_text())
        metadata["results"][0]["lean"][0]["file"] = "Nonadditivity/Definitions.lean"
        self.write_json(name, metadata)
        self.reseal_fixture_source(name)
        self.reject("Result/declaration source file mismatch")

    def test_unknown_or_only_commented_source_labels_are_rejected(self):
        self.write("paper/nonadditivity.tex", r"\label{thm:fixture}" + "\n% " + r"\label{thm:commented}" + "\n")
        self.reseal_fixture_source("paper/nonadditivity.tex")
        for label in ("thm:unknown", "thm:commented"):
            with self.subTest(label=label):
                self.audit["entries"][0]["source_labels"] = [label]
                self.save_audit()
                self.reject("Unknown manuscript source label")

    def test_unbound_report_and_reviewed_source_are_rejected(self):
        report = self.audit["entries"][0]["report"]
        sha = self.audit["report_bindings"].pop(report)
        self.save_audit()
        self.reject("Entry report is not hash-bound")
        self.audit["report_bindings"][report] = sha
        self.write("docs/unbound.txt", "Not a reviewed source\n")
        self.audit["entries"][0]["reviewed_files"].append("docs/unbound.txt")
        self.save_audit()
        self.reject("Reviewed file is not source-bound")

    def test_machine_certification_and_wrong_schema_flags_are_rejected(self):
        cases = (("machine_equivalence_certified", True, "must not claim machine-certified"),
                 ("schema_version", True, "Unsupported statement-audit schema"),
                 ("review_kind", "machine_equivalence", "Unexpected statement-review kind"),
                 ("reviewed_commit", "a" * 39, "Invalid reviewed source commit"))
        for field, value, message in cases:
            with self.subTest(field=field):
                before = self.audit[field]
                self.audit[field] = value
                self.save_audit()
                self.reject(message)
                self.audit[field] = before

    def test_mechanical_scope_cannot_be_promoted_to_a_clean_or_independent_run(self):
        for flag in ("compiled_sources_from_scratch", "comparator_rerun", "nanoda_rerun"):
            with self.subTest(flag=flag):
                self.evidence[flag] = True
                self.save_evidence()
                self.reject("Unexpected mechanical scope flag")
                self.evidence[flag] = False

    def test_wrong_mechanical_commit_roots_axioms_and_status_are_rejected(self):
        changes = (("source_commit", "b" * 40, "source commit differs"),
                   ("theorem_names", self.targets[:-1], "different theorem targets"),
                   ("permitted_axioms", sorted(check.AXIOMS) + ["sorryAx"], "Unexpected mechanical axiom policy"),
                   ("status", "failed", "Unexpected recorded mechanical status or scope"),
                   ("scope", "clean_rebuild", "Unexpected recorded mechanical status or scope"))
        for field, value, message in changes:
            with self.subTest(field=field):
                before = self.evidence[field]
                self.evidence[field] = value
                self.save_evidence()
                self.reject(message)
                self.evidence[field] = before

    def test_incomplete_or_stale_mechanical_inputs_are_rejected(self):
        name = "Nonadditivity/Definitions.lean"
        sha = self.evidence["inputs"].pop(name)
        self.save_evidence()
        self.reject("Mechanical inputs do not cover all reviewed source bindings")
        self.evidence["inputs"][name] = "0" * 64
        self.save_evidence()
        self.reject("Stale mechanical inputs")
        self.evidence["inputs"][name] = sha

    def test_failed_command_boolean_exit_and_unbound_log_are_rejected(self):
        for code in (1, False):
            with self.subTest(exit_code=code):
                self.evidence["commands"][0]["exit_code"] = code
                self.save_evidence()
                self.reject("Recorded mechanical command did not pass")
        self.evidence["commands"][0]["exit_code"] = 0
        self.write("verification/unbound.log", "Unbound\n")
        self.evidence["commands"][0]["log"] = "verification/unbound.log"
        self.save_evidence()
        self.reject("Mechanical command log is not hash-bound")

    def test_path_traversal_and_absolute_paths_are_rejected(self):
        for name in ("../outside", str(self.root / "lean.sh"), "paper/../lean.sh", "./lean.sh", "paper\\file"):
            with self.subTest(path=name):
                self.audit["source_bindings"][name] = "0" * 64
                self.save_audit()
                self.reject("Unsafe relative path")
                self.audit["source_bindings"].pop(name)

    def test_symlink_escape_is_rejected_even_with_matching_content_hash(self):
        outside = Path(self.temporary.name) / "outside.txt"
        outside.write_text("External bytes\n")
        link = self.root / "docs/escape.md"
        link.symlink_to(outside)
        self.audit["report_bindings"]["docs/escape.md"] = check.digest(outside)
        self.save_audit()
        self.reject("Path escapes repository")

    def test_symlink_directory_cannot_hide_unbound_external_proofs(self):
        outside = Path(self.temporary.name) / "external-proofs"
        outside.mkdir()
        (outside / "New.lean").write_text("-- external source\n")
        (self.root / "Nonadditivity/External").symlink_to(outside, target_is_directory=True)
        self.reject("Proof-source symlink escapes repository")

    def test_duplicate_json_keys_are_rejected(self):
        self.save_audit()
        path = self.root / check.AUDIT_PATH
        content = path.read_text().replace('"schema_version": 1,', '"schema_version": 1, "schema_version": 1,', 1)
        path.write_text(content)
        self.reject("Duplicate JSON key: schema_version")



class DeltaAuditControls(unittest.TestCase):
    """Exercise the new selector and bounded continuation using synthetic evidence."""
    delta_path = "verification/statement-audit-delta-fixture.json"
    review_path = "verification/statement-delta/delta-review.json"
    comparison_path = "verification/statement-delta/public-types.json"
    report_path = "docs/DELTA_FIXTURE.md"
    patch_path = "verification/statement-delta/proof.patch"
    write = StatementAuditControls.write
    write_json = StatementAuditControls.write_json

    def setUp(self):
        fixture = StatementAuditControls("runTest")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.root = fixture.root
        self.targets = fixture.targets
        metadata = json.loads((self.root / "metadata/declarations.json").read_text())
        for index, item in enumerate(metadata["declarations"]):
            item.update(type_sha256=f"{index + 1:064x}", is_private=False,
                        is_internal=False, is_internal_detail=False)
            fixture.audit["entries"][index]["type_sha256"] = item["type_sha256"]
            fixture.audit["entries"][index]["verdict"] = "qualified"
            fixture.audit["entries"][index]["qualifications"] = ["Synthetic retained limitation."]
        fixture.write_json("metadata/declarations.json", metadata)
        fixture.reseal_fixture_source("metadata/declarations.json")
        self.parent = deepcopy(fixture.audit)
        self.parent_bytes = (self.root / check.AUDIT_PATH).read_bytes()
        self.write("Nonadditivity/Fixture.lean", "-- Synthetic redundant local import cleanup\n")
        sources = {name: check.digest(self.root / name) for name in self.parent["source_bindings"]}
        proof_names = sorted(name for name in sources if name.endswith(".lean")
                             and (name.startswith("Nonadditivity/")
                                  or name in {"Nonadditivity.lean", "All.lean", "Audit.lean"}))
        changed = [{"path": "Nonadditivity/Fixture.lean",
                    "before_sha256": self.parent["source_bindings"]["Nonadditivity/Fixture.lean"],
                    "after_sha256": sources["Nonadditivity/Fixture.lean"],
                    "kind": "redundant_local_imports_and_comments",
                    "review": "Synthetic comment-only cleanup, no mathematical claim."}]
        self.write(self.report_path, "Synthetic delta review; no mathematical assertion.\n")
        self.write(self.patch_path, "Synthetic comment-only patch.\n")
        self.review = {
            "schema_version": 1, "review_kind": "bounded_cleanup_source_delta_review",
            "machine_equivalence_certified": False, "before_commit": "c" * 40,
            "proof_source_inventory": proof_names, "changed_proof_sources": deepcopy(changed),
            "patch": {"path": self.patch_path, "sha256": check.digest(self.root / self.patch_path)},
            "semantic_report": self.report_path,
        }
        self.write_json(self.review_path, self.review)
        self.write("scripts/compare_public_types.py", "# Synthetic checker identity\n")
        challenge_names = set(check.CONFIGS) | {
            str(Path(name).with_suffix(".lean")) for name in check.CONFIGS}
        self.comparison = {
            "schema_version": 1, "status": "passed",
            "scope": "exact_public_declaration_inventory_and_decoded_kernel_type_bytes",
            "before_commit": "c" * 40, "before_export_path": "metadata/declarations.json",
            "before_export_sha256": self.parent["source_bindings"]["metadata/declarations.json"],
            "after_export_path": "metadata/declarations.json",
            "after_export_sha256": sources["metadata/declarations.json"],
            "selection": {"all_false": ["is_private", "is_internal", "is_internal_detail"]},
            "identity_fields": ["name", "kind", "module", "file", "level_parameters"],
            "checker": {"path": "scripts/compare_public_types.py",
                        "sha256": check.digest(self.root / "scripts/compare_public_types.py")},
            "missing_public_declarations": [], "added_public_declarations": [], "differences": [],
            "expected_public_declarations": 6, "before_public_declarations": 6,
            "after_public_declarations": 6, "compared_public_declarations": 6,
            "after_source_sha256": {name: sources[name] for name in proof_names},
            "challenge_sha256": {name: sources[name] for name in challenge_names},
            "challenge_root_types": {
                entry["declaration"]: {"before_type_sha256": entry["type_sha256"],
                                       "after_type_sha256": entry["type_sha256"]}
                for entry in self.parent["entries"]},
        }
        self.write_json(self.comparison_path, self.comparison)
        self.evidence_path = "verification/statement-delta/checks.json"
        log = "verification/statement-delta/checks.log"
        self.write(log, "Synthetic current check log; no Lean execution.\n")
        self.evidence = deepcopy(fixture.evidence)
        self.evidence.update(source_commit="b" * 40, inputs=sources.copy(),
                             logs={log: check.digest(self.root / log)},
                             commands=[{"command": ["synthetic-check"], "exit_code": 0, "log": log}])
        self.write_json(self.evidence_path, self.evidence)
        entries = deepcopy(self.parent["entries"])
        for entry in entries:
            entry.update(historical_report=entry["report"], report=self.report_path,
                         delta_finding="Synthetic preserved endpoint with retained limitations.")
        reports = self.parent["report_bindings"] | {
            name: check.digest(self.root / name)
            for name in (self.report_path, self.review_path, self.patch_path)}
        self.audit = {
            "schema_version": 2, "review_kind": "incremental_ai_source_semantics_review",
            "machine_equivalence_certified": False, "reviewed_commit": "b" * 40,
            "parent_audit": {"path": check.AUDIT_PATH, "sha256": check.digest(self.root / check.AUDIT_PATH)},
            "source_bindings": sources, "report_bindings": reports, "entries": entries,
            "changed_sources": changed, "meaning_carrying_definition_changes": [],
            "source_delta_review": {"path": self.review_path, "sha256": check.digest(self.root / self.review_path)},
            "public_type_comparison": {"path": self.comparison_path,
                                       "sha256": check.digest(self.root / self.comparison_path)},
            "mechanical_evidence": {"path": self.evidence_path,
                                    "sha256": check.digest(self.root / self.evidence_path)},
        }
        self.save_audit()

    def save_audit(self):
        self.write_json(self.delta_path, self.audit)
        self.write_json(check.CURRENT_AUDIT_PATH, {
            "schema_version": 1, "audit": {"path": self.delta_path,
                                            "sha256": check.digest(self.root / self.delta_path)}})

    def save_comparison(self):
        self.write_json(self.comparison_path, self.comparison)
        self.audit["public_type_comparison"]["sha256"] = check.digest(self.root / self.comparison_path)
        self.save_audit()

    def save_review(self):
        self.write_json(self.review_path, self.review)
        sha = check.digest(self.root / self.review_path)
        self.audit["source_delta_review"]["sha256"] = sha
        self.audit["report_bindings"][self.review_path] = sha
        self.save_audit()

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            check.load_audit(self.root)

    def test_current_delta_is_accepted_without_restamping_parent(self):
        loaded = check.load_audit(self.root)
        self.assertEqual(loaded["schema_version"], 2)
        self.assertEqual((self.root / check.AUDIT_PATH).read_bytes(), self.parent_bytes)
        with self.assertRaisesRegex(ValueError, "Stale source bindings"):
            check.load_audit(self.root, check.AUDIT_PATH)

    def test_invalid_present_selector_does_not_fall_back(self):
        for selector in ({}, {"schema_version": True},
                         {"schema_version": 1, "audit": {"path": "../outside", "sha256": "1" * 64}},
                         {"schema_version": 1, "audit": {"path": self.delta_path, "sha256": "1" * 64}}):
            with self.subTest(selector=selector):
                self.write_json(check.CURRENT_AUDIT_PATH, selector)
                with self.assertRaises(ValueError):
                    check.load_audit(self.root)

    def test_broken_selector_symlink_cannot_trigger_historical_fallback(self):
        selector = self.root / check.CURRENT_AUDIT_PATH
        selector.unlink()
        selector.symlink_to(self.root / "missing-selector.json")
        with self.assertRaisesRegex(ValueError, "Missing bound file"):
            check.load_audit(self.root)

    def test_selected_manifest_mutation_is_rejected(self):
        path = self.root / self.delta_path
        path.write_bytes(path.read_bytes() + b" ")
        self.reject("Stale selected statement audit")

    def test_historical_manifest_reports_and_logs_are_preserved(self):
        names = {check.AUDIT_PATH: "Stale historical statement audit",
                 next(iter(self.parent["report_bindings"])): "Stale report bindings",
                 "verification/statement-audit-20261006/exact-types.log": "Stale historical mechanical logs"}
        for name, message in names.items():
            with self.subTest(file=name):
                path = self.root / name
                old = path.read_bytes()
                path.write_bytes(old + b"changed\n")
                try:
                    self.reject(message)
                finally:
                    path.write_bytes(old)

    def test_incomplete_or_mislabelled_source_delta_is_rejected(self):
        original = deepcopy(self.audit["changed_sources"])
        for changes, message in (([], "Missing reviewed source delta"),
                                 (original + deepcopy(original), "Wrong or duplicate reviewed source change"),
                                 ([original[0] | {"kind": "release_metadata_only"}], "kind does not match"),
                                 ([original[0] | {"before_sha256": "0" * 64}], "Incorrect reviewed delta hashes")):
            with self.subTest(changes=changes):
                self.audit["changed_sources"] = changes
                self.save_audit()
                self.reject(message)

    def test_meaning_carrying_changes_and_qualification_upgrades_are_rejected(self):
        self.audit["meaning_carrying_definition_changes"] = ["Synthetic changed formula"]
        self.save_audit()
        self.reject("does not admit meaning-carrying")
        self.audit["meaning_carrying_definition_changes"] = []
        self.audit["entries"][0]["qualifications"] = []
        self.save_audit()
        self.reject("changed historical qualifications")
        self.audit["entries"][0]["qualifications"] = self.parent["entries"][0]["qualifications"]
        self.audit["entries"][0]["verdict"] = "consistent"
        self.save_audit()
        self.reject("changed historical verdict")

    def test_proof_inventory_and_reviewed_delta_must_be_complete(self):
        original = deepcopy(self.review)
        for field, value, message in (("proof_source_inventory", self.review["proof_source_inventory"][:-1], "proof inventory differs"),
                                      ("changed_proof_sources", [], "Proof-source delta review is incomplete"),
                                      ("machine_equivalence_certified", True, "Unexpected source delta review")):
            with self.subTest(field=field):
                self.review = original | {field: value}
                self.save_review()
                self.reject(message)

    def test_public_count_challenge_bindings_and_root_types_must_match(self):
        original = deepcopy(self.comparison)
        for mutate, message in (
            (lambda value: value.update(expected_public_declarations=5, before_public_declarations=5,
                                         after_public_declarations=5, compared_public_declarations=5),
             "count differs from the current export"),
            (lambda value: value["challenge_sha256"].pop(check.CONFIGS[0]), "challenge coverage differs"),
            (lambda value: value["challenge_root_types"][self.targets[0]].update(after_type_sha256="0" * 64),
             "Delta root type changed"),
            (lambda value: value.update(selection={"all_false": ["is_private"]}), "public selection"),
        ):
            with self.subTest(message=message):
                self.comparison = deepcopy(original)
                mutate(self.comparison)
                self.save_comparison()
                self.reject(message)

    def test_public_comparison_checker_and_current_source_must_remain_fresh(self):
        for name, message in (("scripts/compare_public_types.py", "Stale public comparison checker"),
                              ("Nonadditivity/Fixture.lean", "Stale source bindings")):
            with self.subTest(file=name):
                path = self.root / name
                old = path.read_bytes()
                path.write_bytes(old + b"changed\n")
                try:
                    self.reject(message)
                finally:
                    path.write_bytes(old)

    def test_mechanical_root_axiom_coverage_and_closure_are_checked(self):
        original = deepcopy(self.evidence)
        for mutate, message in (
            (lambda value: value["root_axioms"].pop(self.targets[0]), "root axiom coverage differs"),
            (lambda value: value["root_axioms"][self.targets[0]].append("sorryAx"), "root axiom closure"),
        ):
            with self.subTest(message=message):
                self.evidence = deepcopy(original)
                mutate(self.evidence)
                self.write_json(self.evidence_path, self.evidence)
                self.audit["mechanical_evidence"]["sha256"] = check.digest(self.root / self.evidence_path)
                self.save_audit()
                self.reject(message)



class RootAxiomParserControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        recorder = CHECKER.parent / "statement-audit-20261007/record_checks.py"
        cls.recorder = {"__file__": str(recorder), "__name__": "statement_recorder_controls"}
        exec(compile(recorder.read_bytes(), str(recorder), "exec"), cls.recorder)
        cls.roots = {"Synthetic.root" + str(index): "synthetic config" for index in range(6)}

    def parse(self, text):
        return self.recorder["parse_root_axioms"](text, self.roots)

    def log(self, tokens="propext,\n Classical.choice.{u},\n Quot.sound.{u}"):
        return "\n".join("'" + name + "' depends on axioms: [" + tokens + "]"
                         for name in self.roots) + "\n"

    def test_actual_universe_printing_canonicalizes_all_six_closures(self):
        for tokens in ("propext,\n Classical.choice.{u},\n Quot.sound.{u}",
                       "propext, Classical.choice, Quot.sound",
                       "propext, Classical.choice.{u_1}, Quot.sound.{v'}"):
            with self.subTest(tokens=tokens):
                self.assertEqual(self.parse(self.log(tokens)),
                                 {name: sorted(check.AXIOMS) for name in self.roots})

    def test_unknown_and_malformed_axiom_tokens_are_rejected(self):
        for token in ("sorryAx", "Untrusted.choice.{u}", "Classical.choiceExtra.{u}",
                      "Classical.choice.{}", "Classical.choice.{u, v}",
                      "Classical.choice.{u + 1}", "Classical.choice.{0}",
                      "Classical.choice.{u}.suffix", "Classical.choice.{u", "propext.{u}"):
            with self.subTest(token=token):
                with self.assertRaisesRegex(ValueError, "Unknown or malformed root axiom token"):
                    self.parse(self.log("propext, " + token + ", Quot.sound.{u}"))
        with self.assertRaisesRegex(ValueError, "Unknown or malformed root axiom token"):
            self.parse(self.log("propext, Classical.choice.{u},, Quot.sound.{u}"))

    def test_decorated_and_undecorated_duplicates_are_rejected(self):
        for duplicate in ("Classical.choice", "Classical.choice.{v}"):
            with self.subTest(duplicate=duplicate):
                with self.assertRaisesRegex(ValueError, "Duplicate root axiom token"):
                    self.parse(self.log("propext, Classical.choice.{u}, " + duplicate + ", Quot.sound.{u}"))

    def test_root_coverage_and_exact_closure_are_preserved(self):
        lines = self.log().split("'Synthetic.root")
        # Remove an entire valid root record; roots themselves remain the configured six.
        missing = "'Synthetic.root".join(lines[:-1])
        with self.assertRaisesRegex(ValueError, "exactly the six permitted closures"):
            self.parse(missing)
        with self.assertRaisesRegex(ValueError, "exactly the six permitted closures"):
            self.parse(self.log("propext, Classical.choice.{u}"))
        with self.assertRaisesRegex(ValueError, "Wrong or duplicate root axiom record"):
            self.parse(self.log().replace("Synthetic.root0", "Synthetic.unknown", 1))
        with self.assertRaisesRegex(ValueError, "Wrong or duplicate root axiom record"):
            self.parse(self.log() + "'Synthetic.root0' depends on axioms: [propext, Classical.choice, Quot.sound]\n")

    def test_malformed_extra_axiom_record_is_not_silently_ignored(self):
        for malformed in ("'Synthetic.extra' depends on axioms: [propext\n",
                          "Synthetic.extra depends on axioms: [propext]\n",
                          "'Synthetic.extra' depends on axioms: [propext] trailing text\n"):
            with self.subTest(malformed=malformed):
                with self.assertRaisesRegex(ValueError, "Malformed root axiom record"):
                    self.parse(self.log() + malformed)


if __name__ == "__main__":
    unittest.main(verbosity=2)
