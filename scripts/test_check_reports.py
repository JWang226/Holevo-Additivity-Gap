#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Exercise portable evidence selection and freshness with tiny synthetic records."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification"))
import check_reports
import kernel_common as common


class PortableSelectionTests(unittest.TestCase):
    current = "verification/portable-20261007"

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.root_patch = patch.object(common, "ROOT", self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.bindings_patch = patch.object(common, "bindings", self.bindings)
        self.bindings_patch.start()
        self.addCleanup(self.bindings_patch.stop)
        self.write_json("metadata/results.json", {})
        (self.root / "Proof.lean").write_text("synthetic proof input\n")
        self.pin = {"commit": "synthetic pinned kernel", "rust_commit": "synthetic compiler commit"}
        self.write_json("verification/nanoda/toolchain.json", self.pin)
        self.targets = {}
        for index, name in enumerate(common.DEFAULT_CONFIGS):
            names = ["Synthetic.root" + str(index)]
            if index == 0:
                names.append("Synthetic.sixthRoot")
            self.targets[name] = names
            self.write_json(name, {"theorem_names": names})
        self.write_evidence(check_reports.HISTORICAL_DIRECTORY)

    def write_json(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def read_json(self, name):
        return json.loads((self.root / name).read_text())

    def bindings(self):
        return {
            "proof_source_sha256": {"Proof.lean": common.digest(self.root / "Proof.lean")},
            "artifact_sha256": {"metadata/results.json": common.digest(self.root / "metadata/results.json")},
        }

    def select(self, directory=None):
        self.write_json("metadata/results.json", {
            "portable_verification_current": {"directory": directory or self.current},
        })

    def write_evidence(self, directory):
        cases = {name: {"status": "passed", "theorem_names": targets,
                        "config_sha256": common.digest(self.root / name)}
                 for name, targets in self.targets.items()}
        base = {"schema_version": 1, "status": "passed", "sandboxed": False,
                "upstream_sandboxed_comparator": "not_run",
                "comparator_commit": common.REVISION,
                "checker_dependencies": common.DEPENDENCIES,
                "permitted_axioms": sorted(common.AXIOMS), "cases": cases,
                **self.bindings()}
        comparator = copy.deepcopy(base)
        comparator["mode"] = "unsandboxed_comparator_lean_replay"
        self.write_json(directory + "/comparator-result.json", comparator)
        nanoda = copy.deepcopy(base)
        nanoda.update({
            "mode": "unsandboxed_independent_kernel", "nanoda": self.pin,
            "unpermitted_axiom_hard_error": True, "unknown_pp_declar_hard_error": True,
            "nanoda_binary_source": "built_from_recorded_source_and_rust_pins",
            "nanoda_binary_sha256": "1" * 64,
            "nanoda_build_receipt": {"pin": self.pin, "binary_sha256": "1" * 64,
                                     "rust_version": "commit-hash: " + self.pin["rust_commit"]},
        })
        for case in nanoda["cases"].values():
            case["exported_theorems_present"] = True
        self.write_json(directory + "/nanoda-result.json", nanoda)
        for name in check_reports.EVIDENCE_FILES - {"comparator-result.json", "nanoda-result.json"}:
            (self.root / directory / name).write_text("synthetic retained log\n")
        self.write_json(directory + "/nanoda-build.json", nanoda["nanoda_build_receipt"])
        self.write_json(directory + "/run-info.json", {
            "mode": "all", "sandboxed": False, "nanoda_binary_source": "build_from_recorded_pin",
            "supplied_nanoda_binary": None,
        })
        self.write_json(directory + "/nanoda-controls.log", {
            "status": "passed", "checks": list(check_reports.CONTROLS),
        })
        (self.root / directory / "result.txt").write_text("VERIFICATION PASSED: all\n")
        summary = {"schema_version": 1, "status": "passed", "mode": "all", "sandboxed": False,
                   "project_modules_rebuilt": 369, "audited_project_declarations": 9107,
                   "audited_theorem_constants": 7219, "control_status": "passed",
                   "controls": list(check_reports.CONTROLS),
                   "mapped_declarations_checked": 49, "permitted_axioms": sorted(common.AXIOMS),
                   "upstream_sandboxed_comparator": "not_run",
                   "challenge_configurations": 5, "theorem_roots": 6,
                   "evidence_sha256": {name: common.digest(self.root / directory / name)
                                       for name in check_reports.EVIDENCE_FILES}}
        self.write_json(directory + "/run-summary.json", summary)

    def test_absent_selector_keeps_historical_default(self):
        self.write_evidence(self.current)
        (self.root / self.current / "comparator-result.json").write_text("invalid current report")
        self.assertEqual(check_reports.portable_directory(), check_reports.HISTORICAL_DIRECTORY)
        self.assertEqual(set(check_reports.load_records()), {"comparator", "nanoda"})

    def test_explicit_current_accepts_fresh_bindings(self):
        self.select()
        self.write_evidence(self.current)
        (self.root / check_reports.HISTORICAL_DIRECTORY / "comparator-result.json").write_text("historical bytes untouched by selection")
        self.assertEqual(check_reports.portable_directory(), self.current)
        self.assertEqual(set(check_reports.load_records()), {"comparator", "nanoda"})

    def test_invalid_present_selector_never_falls_back(self):
        for selection in (None, {}, {"directory": self.current, "extra": True},
                          {"directory": "/verification/portable-20261007"},
                          {"directory": "verification/../portable-20261007"},
                          {"directory": "verification/portable-current"},
                          {"directory": 20261007}):
            with self.subTest(selection=selection):
                self.write_json("metadata/results.json", {"portable_verification_current": selection})
                with self.assertRaises(ValueError):
                    check_reports.load_records()

    def test_malformed_metadata_root_is_rejected(self):
        for metadata in ([], "historical", None, False, 1):
            with self.subTest(metadata=metadata):
                self.write_json("metadata/results.json", metadata)
                with self.assertRaisesRegex(ValueError, "Expected release metadata object"):
                    check_reports.load_records()

    def test_escaping_directory_symlink_is_rejected(self):
        self.select()
        with tempfile.TemporaryDirectory() as outside:
            (self.root / self.current).symlink_to(outside, target_is_directory=True)
            with self.assertRaises(ValueError):
                check_reports.portable_directory()

    def test_missing_selected_reports_never_fall_back(self):
        self.select()
        with self.assertRaises(FileNotFoundError):
            check_reports.load_records()

    def test_stale_proof_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        (self.root / "Proof.lean").write_text("changed synthetic input\n")
        with self.assertRaisesRegex(ValueError, "Portable evidence is stale"):
            check_reports.load_records()

    def test_stale_hash_bound_metadata_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        self.write_json("metadata/results.json", {
            "portable_verification_current": {"directory": self.current}, "changed": True,
        })
        with self.assertRaisesRegex(ValueError, "Portable evidence is stale"):
            check_reports.load_records()

    def test_altered_retained_log_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        (self.root / self.current / "nanoda.log").write_text("altered synthetic log\n")
        with self.assertRaisesRegex(ValueError, "Portable evidence log/report differs"):
            check_reports.load_records()

    def test_summary_count_and_control_policy_is_preserved(self):
        self.select()
        self.write_evidence(self.current)
        original = self.read_json(self.current + "/run-summary.json")
        for key, value in (("project_modules_rebuilt", 368),
                           ("audited_project_declarations", 9106),
                           ("audited_theorem_constants", 7218),
                           ("controls", original["controls"][:-1]),
                           ("control_status", "not_run"),
                           ("controls", ["unrelated control"] * 13),
                           ("permitted_axioms", sorted(common.AXIOMS) + ["sorryAx"]),
                           ("mapped_declarations_checked", 48),
                           ("upstream_sandboxed_comparator", "passed")):
            with self.subTest(field=key):
                changed = copy.deepcopy(original)
                changed[key] = value
                self.write_json(self.current + "/run-summary.json", changed)
                with self.assertRaisesRegex(ValueError, "Unexpected portable full-run summary"):
                    check_reports.load_records()

    def reseal_evidence(self, filename):
        summary = self.read_json(self.current + "/run-summary.json")
        summary["evidence_sha256"][filename] = common.digest(self.root / self.current / filename)
        self.write_json(self.current + "/run-summary.json", summary)

    def test_incomplete_or_escaping_evidence_inventory_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        original = self.read_json(self.current + "/run-summary.json")
        for filename in ("nanoda-controls.log", "comparator-result.json", "lean.log"):
            with self.subTest(omitted=filename):
                changed = copy.deepcopy(original)
                changed["evidence_sha256"].pop(filename)
                self.write_json(self.current + "/run-summary.json", changed)
                with self.assertRaisesRegex(ValueError, "Incomplete portable retained-evidence inventory"):
                    check_reports.load_records()
        changed = copy.deepcopy(original)
        changed["evidence_sha256"]["../outside.log"] = "1" * 64
        self.write_json(self.current + "/run-summary.json", changed)
        with self.assertRaisesRegex(ValueError, "Incomplete portable retained-evidence inventory"):
            check_reports.load_records()

    def test_retained_file_symlink_escape_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        with tempfile.TemporaryDirectory() as outside:
            external = Path(outside) / "lean.log"
            external.write_text("synthetic retained log\n")
            local = self.root / self.current / "lean.log"
            local.unlink()
            local.symlink_to(external)
            with self.assertRaisesRegex(ValueError, "path escapes repository"):
                check_reports.load_records()

    def test_altered_controls_fail_even_after_fixture_hash_update(self):
        self.select()
        self.write_evidence(self.current)
        self.write_json(self.current + "/nanoda-controls.log", {
            "status": "passed", "checks": list(check_reports.CONTROLS)[:-1],
        })
        self.reseal_evidence("nanoda-controls.log")
        with self.assertRaisesRegex(ValueError, "Retained kernel controls do not match"):
            check_reports.load_records()

    def test_partial_or_supplied_binary_invocation_is_rejected(self):
        self.select()
        self.write_evidence(self.current)
        original = self.read_json(self.current + "/run-info.json")
        for field, value in (("mode", "nanoda"), ("sandboxed", True),
                             ("nanoda_binary_source", "caller_supplied"),
                             ("supplied_nanoda_binary", "/tmp/binary")):
            with self.subTest(field=field):
                changed = original | {field: value}
                self.write_json(self.current + "/run-info.json", changed)
                self.reseal_evidence("run-info.json")
                with self.assertRaisesRegex(ValueError, "Unexpected portable all-run invocation"):
                    check_reports.load_records()

    def test_truthy_nonboolean_kernel_flags_are_rejected(self):
        self.select()
        self.write_evidence(self.current)
        original = self.read_json(self.current + "/nanoda-result.json")
        for flag in ("unpermitted_axiom_hard_error", "unknown_pp_declar_hard_error"):
            with self.subTest(flag=flag):
                changed = copy.deepcopy(original)
                changed[flag] = "true"
                self.write_json(self.current + "/nanoda-result.json", changed)
                with self.assertRaisesRegex(ValueError, "Unexpected Nanoda options"):
                    check_reports.load_records()

    def test_record_and_retained_build_receipt_must_match(self):
        self.select()
        self.write_evidence(self.current)
        receipt = self.read_json(self.current + "/nanoda-build.json")
        receipt["binary_sha256"] = "2" * 64
        self.write_json(self.current + "/nanoda-build.json", receipt)
        self.reseal_evidence("nanoda-build.json")
        with self.assertRaisesRegex(ValueError, "Unexpected Nanoda options or build provenance"):
            check_reports.load_records()

    def test_duplicate_json_selector_is_rejected(self):
        (self.root / "metadata/results.json").write_text(
            '{"portable_verification_current": null, "portable_verification_current": {}}')
        with self.assertRaisesRegex(ValueError, "Duplicate portable JSON key"):
            check_reports.load_records()


if __name__ == "__main__":
    unittest.main()
