#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Negative controls for statement-review freshness, using synthetic files only.

No Lean process runs, no actual review is restamped, and these tests make no
mathematical assertion about the six production theorems.
"""
from __future__ import annotations

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


if __name__ == "__main__":
    unittest.main(verbosity=2)
