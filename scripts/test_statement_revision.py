#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Exercise the manuscript-revision envelope with synthetic, non-proof records.

The additive source-certificate verifier has separate controls. These tests mock
that boundary and check historical retention, exact archive bytes, allowed source
changes, root coverage, and correspondence-correction provenance. No Lean runs.
"""
from copy import deepcopy
import importlib.util
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
from types import ModuleType
import unittest
from unittest.mock import Mock, patch


CHECKER = Path(__file__).resolve().parents[1] / "verification/check_statement_audit.py"
SPEC = importlib.util.spec_from_file_location("statement_revision_checker", CHECKER)
check = importlib.util.module_from_spec(SPEC)
# Avoid writing a bytecode cache into the repository.
exec(compile(CHECKER.read_bytes(), str(CHECKER), "exec"), check.__dict__)


class StatementRevisionControls(unittest.TestCase):
    audit_path = "verification/statement-audit-revision-fixture.json"
    parent_path = "verification/statement-audit-delta-20261007.json"
    review_path = "verification/revision-fixture/review.json"
    report_path = "docs/REVISION_FIXTURE.md"
    patch_path = "verification/revision-fixture/source.patch"
    certificate_path = "verification/revision-fixture/source-certificate.json"
    evidence_path = "verification/revision-fixture/checks.json"
    archive_path = "verification/manuscript-v2-20261008/source.tar.gz"
    c_name = "Nonadditivity.OperationalConsequences.exists_small_chi_large_capacity_gain_and_two_use_ratio"

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="statement-revision-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        original_path = sys.path.copy()
        self.addCleanup(lambda: sys.path.__setitem__(slice(None), original_path))
        certificate_module = ModuleType("source_certificate")
        self.certificate_loader = Mock(return_value={"status": "passed"})
        certificate_module.load_source_certificate = self.certificate_loader
        module_patch = patch.dict(sys.modules, {"source_certificate": certificate_module})
        module_patch.start()
        self.addCleanup(module_patch.stop)

        baseline_names = check.FIXED_SOURCES | {"Nonadditivity/Fixture.lean"}
        for name in baseline_names:
            self.write(name, "Synthetic source input: " + name + "\n")
        self.write("paper/nonadditivity.tex", self.manuscript("historical version"))
        self.targets = ["Fixture.root0", "Fixture.root1", self.c_name,
                        "Fixture.root3", "Fixture.root4", "Fixture.root5", check.ADDED_TARGET]
        declarations = [{"name": name, "kind": "theorem", "file": "Nonadditivity/Fixture.lean",
                         "type_sha256": f"{index + 1:064x}"}
                        for index, name in enumerate(self.targets)]
        self.write_json("metadata/declarations.json", {"declarations": declarations})
        self.results = []
        old_entries = []
        index = 0
        for config in check.CONFIGS:
            names = self.targets[index:index + (2 if config == check.CONFIGS[-1] else 1)]
            self.write_config(config, names)
            result_id = "result-" + str(index)
            self.results.append({"id": result_id, "comparator_config": config,
                                 "lean": [{"declaration": name, "file": "Nonadditivity/Fixture.lean"}
                                          for name in names]})
            for name in names:
                old_entries.append(self.entry(name, config, result_id, declarations[self.targets.index(name)]))
            index += len(names)
        self.results.append({"id": "small-large-and-sequence", "lean": [
            {"declaration": check.ADDED_TARGET, "file": "Nonadditivity/Fixture.lean"}]})
        self.write_json("metadata/results.json", {"results": self.results})
        self.old_sources = {name: check.digest(self.root / name) for name in baseline_names}

        original_report = "docs/HISTORICAL_FIXTURE.md"
        parent_report = "docs/DELTA_FIXTURE.md"
        self.write(original_report, "Synthetic original semantic review; no mathematical claim.\n")
        self.write(parent_report, "Synthetic cleanup review; no mathematical claim.\n")
        self.old_log = "verification/historical-fixture/checks.log"
        self.write(self.old_log, "Synthetic historical command output; no Lean execution.\n")
        old_evidence_path = "verification/historical-fixture/checks.json"
        self.write_json(old_evidence_path, {"logs": {self.old_log: check.digest(self.root / self.old_log)}})
        original_entries = deepcopy(old_entries)
        for entry in original_entries:
            entry["report"] = original_report
        original = {"schema_version": 1, "machine_equivalence_certified": False,
                    "report_bindings": {original_report: check.digest(self.root / original_report)},
                    "mechanical_evidence": self.reference(old_evidence_path), "entries": original_entries}
        self.write_json(check.AUDIT_PATH, original)
        self.parent = {"schema_version": 2, "review_kind": "incremental_ai_source_semantics_review",
                       "machine_equivalence_certified": False, "source_bindings": self.old_sources,
                       "report_bindings": original["report_bindings"] | {
                           parent_report: check.digest(self.root / parent_report)},
                       "mechanical_evidence": self.reference(old_evidence_path),
                       "parent_audit": self.reference(check.AUDIT_PATH), "entries": old_entries}
        self.write_json(self.parent_path, self.parent)
        self.parent_bytes = (self.root / self.parent_path).read_bytes()
        self.original_bytes = (self.root / check.AUDIT_PATH).read_bytes()
        self.old_log_bytes = (self.root / self.old_log).read_bytes()

        for name in check.REVISION_SOURCES:
            self.write(name, "Synthetic revision input: " + name + "\n")
        self.write("paper/nonadditivity.tex", self.manuscript("exact upstream version two"))
        self.write_archive([("nonadditivity.tex", (self.root / "paper/nonadditivity.tex").read_bytes())])
        self.provenance = {
            "arxiv_id": "2609.18222", "version": "v2",
            "source_url": "https://arxiv.org/src/2609.18222v2", "exact_upstream_bytes": True,
            "archive_member": "nonadditivity.tex", "repository_file": "paper/nonadditivity.tex",
            "sha256": check.digest(self.root / "paper/nonadditivity.tex"),
            "source_archive": self.reference(self.archive_path),
        }
        self.write_json("paper/arxiv-v2.json", self.provenance)
        self.write_config(check.ADDED_CONFIG, [check.ADDED_TARGET])
        self.results[-1]["comparator_config"] = check.ADDED_CONFIG
        self.write_json("metadata/results.json", {"results": self.results})
        self.write("scripts/check_challenges.py", "# Synthetic additive-root application inventory\n")
        self.write(self.report_path, "Synthetic current semantic review; no mathematical claim.\n")
        self.write(self.patch_path, "Synthetic manuscript and additive configuration patch.\n")
        self.write_json(self.certificate_path, {"schema_version": 2, "status": "passed"})
        entries = deepcopy(old_entries)
        for entry in entries:
            entry.update(historical_report=entry["report"], report=self.report_path)
        current_c = next(entry for entry in entries if entry["declaration"] == self.c_name)
        current_c["source_labels"] = ["cor:capacity"]
        current_c["qualifications"] = ["Capacity gain does not imply arbitrarily large absolute two-use information."]
        entries.append(self.entry(check.ADDED_TARGET, check.ADDED_CONFIG, "small-large-and-sequence", declarations[-1]))
        entries[-1]["report"] = self.report_path
        self.review = {
            "review_kind": "arxiv_v2_and_additive_root_source_review", "machine_equivalence_certified": False,
            "semantic_report": self.report_path, "changed_proof_sources": [],
            "patch": self.reference(self.patch_path),
        }
        old_c = next(entry for entry in old_entries if entry["declaration"] == self.c_name)
        self.audit = {
            "schema_version": 3, "review_kind": "manuscript_revision_and_additive_root_ai_review",
            "machine_equivalence_certified": False, "reviewed_commit": "b" * 40,
            "parent_audit": self.reference(self.parent_path), "entries": entries,
            "meaning_carrying_definition_changes": [], "source_certificate": self.reference(self.certificate_path),
            "report_bindings": self.parent["report_bindings"] | {
                name: check.digest(self.root / name) for name in (self.report_path, self.patch_path)},
            "source_bindings": {name: check.digest(self.root / name)
                                for name in baseline_names | check.REVISION_SOURCES},
            "correspondence_corrections": {self.c_name: {
                "historical_qualifications": old_c["qualifications"],
                "current_qualifications": current_c["qualifications"],
                "reason": "A capacity lower bound gives no lower bound on absolute two-use information."}},
        }
        self.current_log = "verification/revision-fixture/checks.log"
        self.write(self.current_log, "Synthetic current command output; no Lean execution.\n")
        self.evidence = {
            "status": "passed", "scope": check.SCOPE, "source_commit": "b" * 40,
            "theorem_names": self.targets, "permitted_axioms": sorted(check.AXIOMS),
            "root_axioms": {name: sorted(check.AXIOMS) for name in self.targets},
            "logs": {self.current_log: check.digest(self.root / self.current_log)},
            "commands": [{"command": ["synthetic-check", "--not-executed"], "exit_code": 0,
                          "log": self.current_log}],
            "compiled_sources_from_scratch": False, "comparator_rerun": False, "nanoda_rerun": False,
        }
        self.reseal_sources()

    @staticmethod
    def manuscript(version):
        return "Synthetic " + version + "\n" + r"\label{thm:fixture}\label{cor:capacity}\label{cor:separation}" + "\n"

    def entry(self, name, config, result_id, declaration):
        return {"id": "audit-" + name, "declaration": name, "config": config,
                "report": "docs/DELTA_FIXTURE.md", "reviewer": "synthetic-reviewer",
                "result_ids": [result_id], "source_labels": ["thm:fixture"],
                "reviewed_files": ["Nonadditivity/Fixture.lean"], "verdict": "qualified",
                "qualifications": ["Synthetic retained limitation."],
                "type_sha256": declaration["type_sha256"]}

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def write_json(self, name, value):
        self.write(name, json.dumps(value, indent=2) + "\n")

    def reference(self, name):
        return {"path": name, "sha256": check.digest(self.root / name)}

    def write_config(self, name, targets):
        self.write_json(name, {"challenge_module": name.removesuffix(".json").replace("/", "."),
                               "solution_module": "Nonadditivity.Fixture", "theorem_names": targets,
                               "permitted_axioms": sorted(check.AXIOMS), "enable_nanoda": False})

    def write_archive(self, members):
        path = self.root / self.archive_path
        path.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(path, "w:gz") as archive:
            for name, data in members:
                member = tarfile.TarInfo(name)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))

    def save_audit(self):
        self.write_json(self.audit_path, self.audit)
        self.write_json(check.CURRENT_AUDIT_PATH, {"schema_version": 1, "audit": self.reference(self.audit_path)})

    def save_review(self):
        self.review["changed_sources"] = deepcopy(self.audit["changed_sources"])
        self.write_json(self.review_path, self.review)
        self.audit["source_delta_review"] = self.reference(self.review_path)
        self.audit["report_bindings"][self.review_path] = self.audit["source_delta_review"]["sha256"]
        self.save_audit()

    def reseal_sources(self):
        """Reseal synthetic current bytes to test invariants beyond freshness."""
        sources = self.audit["source_bindings"]
        for name in sources:
            sources[name] = check.digest(self.root / name)
        self.audit["changed_sources"] = [
            {"path": name, "before_sha256": self.old_sources.get(name), "after_sha256": sha,
             "review": "Synthetic reviewed change; no mathematical assertion."}
            for name, sha in sorted(sources.items()) if sha != self.old_sources.get(name)]
        self.evidence["inputs"] = sources.copy()
        self.write_json(self.evidence_path, self.evidence)
        self.audit["mechanical_evidence"] = self.reference(self.evidence_path)
        self.save_review()

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            check.load_audit(self.root)

    def test_complete_synthetic_revision_is_accepted_without_restamping_history(self):
        loaded = check.load_audit(self.root)
        self.assertEqual(len(loaded["entries"]), 7)
        self.assertEqual((self.root / self.parent_path).read_bytes(), self.parent_bytes)
        self.assertEqual((self.root / check.AUDIT_PATH).read_bytes(), self.original_bytes)
        self.assertEqual((self.root / self.old_log).read_bytes(), self.old_log_bytes)
        self.certificate_loader.assert_called_once()
        self.assertEqual(self.certificate_loader.call_args.args[2], {
            "Nonadditivity/Fixture.lean", "Nonadditivity.lean", "All.lean", "Audit.lean"})

    def test_archive_member_must_equal_repository_bytes_even_after_resealing(self):
        self.write_archive([("nonadditivity.tex", b"different upstream member\n")])
        self.provenance["source_archive"] = self.reference(self.archive_path)
        self.write_json("paper/arxiv-v2.json", self.provenance)
        self.reseal_sources()
        self.reject("Repository manuscript differs from the exact arXiv v2 source")

    def test_missing_or_duplicate_archive_member_is_rejected(self):
        data = (self.root / "paper/nonadditivity.tex").read_bytes()
        for members in ([("other.tex", data)], [("nonadditivity.tex", data)] * 2):
            with self.subTest(members=len(members)):
                self.write_archive(members)
                self.provenance["source_archive"] = self.reference(self.archive_path)
                self.write_json("paper/arxiv-v2.json", self.provenance)
                self.reseal_sources()
                self.reject("Missing or ambiguous arXiv manuscript member")

    def test_claimed_upstream_version_is_checked_after_resealing(self):
        self.provenance["version"] = "v1"
        self.write_json("paper/arxiv-v2.json", self.provenance)
        self.reseal_sources()
        self.reject("Unexpected arXiv v2 source provenance")

    def test_changed_production_source_is_rejected_after_resealing(self):
        self.write("Nonadditivity/Fixture.lean", "-- Changed synthetic production proof\n")
        self.reseal_sources()
        self.reject("Revision changed an existing proof or statement input")

    def test_changed_base_challenge_is_rejected_after_resealing(self):
        name = check.CONFIGS[0].removesuffix(".json") + ".lean"
        self.write(name, "-- Changed synthetic expected statement\n")
        self.reseal_sources()
        self.reject("Revision changed an existing proof or statement input")

    def test_incomplete_changed_source_inventory_is_rejected(self):
        self.audit["changed_sources"].pop()
        self.save_review()
        self.reject("Reviewed revision delta is incomplete")

    def test_missing_new_root_is_rejected(self):
        self.audit["entries"].pop()
        self.save_audit()
        self.reject("Unexpected statement-audit entry count")

    def test_wrong_new_root_is_rejected(self):
        self.audit["entries"][-1]["declaration"] = "Fixture.unreviewedAddedRoot"
        self.save_audit()
        self.reject("Wrong or duplicate audit target")

    def test_wrong_new_root_result_link_is_rejected(self):
        self.audit["entries"][-1]["result_ids"] = ["result-0"]
        self.save_audit()
        self.reject("Cited results do not contain audit target")

    def test_omitted_historical_report_is_rejected(self):
        self.audit["report_bindings"].pop("docs/HISTORICAL_FIXTURE.md")
        self.save_audit()
        self.reject("Revision review omitted a historical report binding")

    def test_changed_parent_or_ancestor_record_is_rejected(self):
        for name in (self.parent_path, check.AUDIT_PATH):
            with self.subTest(record=name):
                original = (self.root / name).read_bytes()
                self.write(name, "Changed historical JSON record\n")
                self.reject("Stale historical statement audit")
                (self.root / name).write_bytes(original)

    def test_changed_historical_log_is_rejected(self):
        self.write(self.old_log, "Changed historical log\n")
        self.reject("Stale historical mechanical logs")

    def test_root_c_correction_is_required(self):
        self.audit["correspondence_corrections"] = {}
        self.save_audit()
        self.reject("Expected the explicit root C coverage correction")

    def test_root_c_correction_must_bind_old_and_current_findings(self):
        original = deepcopy(self.audit["correspondence_corrections"][self.c_name])
        for field, value in (("historical_qualifications", ["Unrecorded old finding"]),
                             ("current_qualifications", ["Unrecorded new finding"]),
                             ("reason", "")):
            with self.subTest(field=field):
                self.audit["correspondence_corrections"][self.c_name] = original | {field: value}
                self.save_audit()
                self.reject("Incomplete root C correspondence correction")

    def test_entry_type_must_match_current_export(self):
        self.audit["entries"][-1]["type_sha256"] = "f" * 64
        self.save_audit()
        self.reject("Revision root type differs")


if __name__ == "__main__":
    unittest.main()
