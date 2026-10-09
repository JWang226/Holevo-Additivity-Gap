#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Exercise source-gate artifact binding with small isolated evidence chains."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification"))
import kernel_common as common


class CertificateArtifactTests(unittest.TestCase):
    selected = "verification/additive/source-certificate.json"
    base = "verification/base/source-certificate.json"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        root_patch = patch.object(common, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        self.write("lakefile.toml", "current Lake file\n")
        self.write("verification/additive/base-lakefile.toml", "historical Lake file\n")
        self.write("scripts/elaboration_test.py", "measured driver\n")
        self.write("scripts/compare_public_types.py", "comparison checker\n")
        self.write("metadata/declarations.json", "unchanged declarations\n")
        self.write("Nonadditivity/Proof.lean", "unchanged proof\n")
        self.write("verification/base/build.log", "retained audit\n")
        self.summary = {"source_hashes_before": {
            "lakefile.toml": self.sha("verification/additive/base-lakefile.toml"),
            "scripts/elaboration_test.py": self.sha("scripts/elaboration_test.py"),
            "Nonadditivity/Proof.lean": self.sha("Nonadditivity/Proof.lean"),
        }}
        self.comparison = {
            "checker": self.reference("scripts/compare_public_types.py"),
            "after_export_path": "metadata/declarations.json",
            "after_export_sha256": self.sha("metadata/declarations.json"),
        }
        self.write_json("verification/base/summary.json", self.summary)
        self.write_json("verification/base/public-types.json", self.comparison)
        self.base_record = {
            "schema_version": 1,
            "build_summary": self.reference("verification/base/summary.json"),
            "audit_log": self.reference("verification/base/build.log"),
            "public_type_comparison": self.reference("verification/base/public-types.json"),
        }
        self.write_json(self.base, self.base_record)
        self.extension = {
            "schema_version": 2,
            "base_certificate": self.reference(self.base),
            "historical_lakefile": self.reference("verification/additive/base-lakefile.toml"),
        }
        self.write_json(self.selected, self.extension)
        self.select(self.selected)

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def write_json(self, name, value):
        self.write(name, json.dumps(value))

    def sha(self, name):
        return common.digest(self.root / name)

    def reference(self, name):
        return {"path": name, "sha256": self.sha(name)}

    def select(self, name):
        self.write_json("metadata/results.json", {"verification_current": {"source_certificate": name}})

    def rebind_base(self):
        self.write_json(self.base, self.base_record)
        self.extension["base_certificate"] = self.reference(self.base)
        self.write_json(self.selected, self.extension)

    def test_additive_chain_and_gate_dependencies_are_complete(self):
        files = common.certificate_artifacts()
        expected = {
            "metadata/results.json", self.selected, self.base,
            "verification/additive/base-lakefile.toml", "verification/base/summary.json",
            "verification/base/build.log", "verification/base/public-types.json",
            "scripts/compare_public_types.py", "metadata/declarations.json",
            "scripts/elaboration_test.py",
        }
        self.assertEqual(set(files), expected)
        self.assertTrue(all(files[name] == self.sha(name) for name in expected))

    def test_schema1_selection_remains_supported(self):
        self.summary["source_hashes_before"]["lakefile.toml"] = self.sha("lakefile.toml")
        self.write_json("verification/base/summary.json", self.summary)
        self.base_record["build_summary"] = self.reference("verification/base/summary.json")
        self.rebind_base()
        self.select(self.base)
        files = common.certificate_artifacts()
        self.assertIn("lakefile.toml", files)
        self.assertNotIn(self.selected, files)
        self.assertNotIn("verification/additive/base-lakefile.toml", files)

    def test_absent_selector_binds_only_metadata(self):
        for value in ({}, {"verification_current": {"record": "historical"}}):
            self.write_json("metadata/results.json", value)
            self.assertEqual(common.certificate_artifacts(), {"metadata/results.json": self.sha("metadata/results.json")})

    def test_invalid_present_selector_never_falls_back(self):
        for value in (None, [], False, 1, "historical"):
            with self.subTest(value=value):
                self.write_json("metadata/results.json", {"verification_current": value})
                with self.assertRaises(ValueError):
                    common.certificate_artifacts()
        for name in (None, "", "/outside.json", "../outside.json", "verification//base.json",
                     "verification/./base.json", "verification\\base.json", "C:base.json",
                     "verification/base.toml"):
            with self.subTest(name=name):
                self.select(name)
                with self.assertRaises(ValueError):
                    common.certificate_artifacts()

    def test_missing_selected_certificate_rejects(self):
        self.select("verification/missing.json")
        with self.assertRaises(ValueError):
            common.certificate_artifacts()

    def test_stale_referenced_evidence_rejects(self):
        for name in (self.base, "verification/additive/base-lakefile.toml", "verification/base/summary.json",
                     "verification/base/build.log", "verification/base/public-types.json",
                     "scripts/compare_public_types.py", "metadata/declarations.json",
                     "scripts/elaboration_test.py"):
            with self.subTest(name=name):
                path = self.root / name
                old = path.read_bytes()
                path.write_bytes(old + b"changed\n")
                with self.assertRaisesRegex(ValueError, "Stale or invalid"):
                    common.certificate_artifacts()
                path.write_bytes(old)

    def test_escaping_selected_symlink_rejects(self):
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / "certificate.json"
            target.write_text(json.dumps(self.extension))
            (self.root / self.selected).unlink()
            (self.root / self.selected).symlink_to(target)
            with self.assertRaisesRegex(ValueError, "escaping"):
                common.certificate_artifacts()

    def test_escaping_reference_symlink_rejects(self):
        with tempfile.TemporaryDirectory() as outside:
            name = "verification/base/build.log"
            target = Path(outside) / "build.log"
            target.write_bytes((self.root / name).read_bytes())
            (self.root / name).unlink()
            (self.root / name).symlink_to(target)
            with self.assertRaisesRegex(ValueError, "escaping"):
                common.certificate_artifacts()

    def test_reference_path_and_hash_formats_reject(self):
        for value in ({}, {"path": self.base}, {"path": self.base, "sha256": None},
                      {"path": self.base, "sha256": "A" * 64},
                      {"path": "../base.json", "sha256": "0" * 64},
                      {"path": self.base, "sha256": self.sha(self.base), "extra": True}):
            with self.subTest(value=value):
                changed = copy.deepcopy(self.extension)
                changed["base_certificate"] = value
                self.write_json(self.selected, changed)
                with self.assertRaises(ValueError):
                    common.certificate_artifacts()

    def test_nested_extension_or_cycle_rejects(self):
        self.base_record = copy.deepcopy(self.extension)
        self.base_record["base_certificate"] = self.reference(self.selected)
        self.rebind_base()
        with self.assertRaisesRegex(ValueError, "Unsupported"):
            common.certificate_artifacts()

    def test_unknown_and_boolean_schema_reject(self):
        for schema in (True, False, 0, 3, "2", None):
            with self.subTest(schema=schema):
                self.extension["schema_version"] = schema
                self.write_json(self.selected, self.extension)
                with self.assertRaisesRegex(ValueError, "Unsupported"):
                    common.certificate_artifacts()

    def test_duplicate_json_keys_reject(self):
        self.write(self.selected, '{"schema_version": 1, "schema_version": 2}')
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            common.certificate_artifacts()

    def test_measured_historical_lake_binding_rejects(self):
        self.summary["source_hashes_before"]["lakefile.toml"] = self.sha("lakefile.toml")
        self.write_json("verification/base/summary.json", self.summary)
        self.base_record["build_summary"] = self.reference("verification/base/summary.json")
        self.rebind_base()
        with self.assertRaisesRegex(ValueError, "Historical Lake file differs"):
            common.certificate_artifacts()

    def test_missing_or_escaping_measured_driver_rejects(self):
        for name in ("scripts/missing.py", "../outside.py"):
            with self.subTest(name=name):
                self.summary["source_hashes_before"] = {name: "0" * 64}
                self.write_json("verification/base/summary.json", self.summary)
                self.base_record["build_summary"] = self.reference("verification/base/summary.json")
                self.rebind_base()
                with self.assertRaises(ValueError):
                    common.certificate_artifacts()

    def test_missing_export_hash_rejects(self):
        self.comparison.pop("after_export_sha256")
        self.write_json("verification/base/public-types.json", self.comparison)
        self.base_record["public_type_comparison"] = self.reference("verification/base/public-types.json")
        self.rebind_base()
        with self.assertRaisesRegex(ValueError, "export hash"):
            common.certificate_artifacts()


if __name__ == "__main__":
    unittest.main()
