#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Synthetic controls for the recorded cleanup certificate's integrity gate.

Only tiny temporary Git repositories and fabricated metadata/logs are used.
These fixtures are not Lean proofs and do not claim a real successful audit,
public-type comparison, Comparator/Nanoda run, or statement review. No compiler,
Lake, release validator, kernel, or real project input is executed or modified.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import types
import unittest

HERE = Path(__file__).resolve().parent
HELPER = HERE / "source_certificate.py"
check = types.ModuleType("synthetic_source_certificate")
check.__file__ = str(HELPER)
# Load functions without writing __pycache__ into the repository.
exec(compile(HELPER.read_bytes(), str(HELPER), "exec"), check.__dict__)


class SourceCertificateControls(unittest.TestCase):
    CERTIFICATE = "verification/synthetic/source-certificate.json"
    SUMMARY = "verification/synthetic/after/summary.json"
    LOG = "verification/synthetic/after/build.log"
    COMPARISON = "verification/synthetic/public-types.json"

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="synthetic-certificate-", dir=HERE)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.proof_paths = {"Nonadditivity/Fixture.lean", "Nonadditivity.lean", "Audit.lean", "All.lean"}
        drivers = set(check.DRIVER_FILES)
        for name in self.proof_paths | drivers:
            self.write(name, "synthetic input only: " + name + "\n")
        self.write("lean-toolchain", "leanprover/lean4:v4.29.0-rc6\n")
        self.git("init", "--quiet")
        self.git("add", "--all")
        self.git("commit", "--quiet", "-m", "Synthetic source snapshot; no proof execution")
        self.commit = self.git("rev-parse", "HEAD").strip()
        self.sources = {name: check.digest(self.root / name) for name in sorted(self.proof_paths)}
        self.measured_inputs = {name: check.digest(self.root / name)
                                for name in sorted(self.proof_paths | drivers)}
        self.original_log = str(self.root / "original-after/build.log")
        self.summary = {
            "valid": True, "invalid_reasons": [],
            "build": {"returncode": 0, "log": self.original_log},
            "provenance": {"commit": self.commit, "pin": "leanprover/lean4:v4.29.0-rc6"},
            "modules": {name.removesuffix(".lean").replace("/", "."): name for name in self.proof_paths},
            "coverage": {"complete": True, "order_matches": True,
                         "expected": 4, "measured": 4, "missing": [], "unexpected": [],
                         "duplicates": [], "failed": []},
            "source_hashes_before": self.measured_inputs.copy(),
            "source_hashes_after": self.measured_inputs.copy(),
            "source_changes": [], "dependency_artifact_changes": [],
            "health": {"error_count": 0, "sorry_warning_count": 0,
                       "unauthorized_sorry_tokens": 0, "allowed_sorry_modules": []},
        }
        self.write("metadata/declarations.json", '{"synthetic_fixture_only":true}\n')
        self.write("scripts/compare_public_types.py", "# Synthetic checker identity; never executed\n")
        self.targets, challenge_hashes = [], {}
        for index, filename in enumerate(check.CONFIGS):
            names = ["Fixture.root" + str(index)]
            if index == 4:
                names.append("Fixture.root5")
            self.targets.extend(names)
            self.write_json(filename, {"theorem_names": names})
            source_path = filename.removesuffix(".json") + ".lean"
            self.write(source_path, "-- Synthetic expected-statement fixture only\n")
            for name in (filename, source_path):
                challenge_hashes[name] = check.digest(self.root / name)
        self.comparison = {
            "schema_version": 1, "status": "passed",
            "scope": "exact_public_declaration_inventory_and_decoded_kernel_type_bytes",
            "before_commit": check.BEFORE_COMMIT,
            "before_export_path": "metadata/declarations.json",
            "after_export_path": "metadata/declarations.json",
            "selection": {"all_false": check.PUBLIC_FLAGS.copy()},
            "identity_fields": check.IDENTITY_FIELDS.copy(), "lean_or_kernel_executed": False,
            "expected_public_declarations": 5323, "before_public_declarations": 5323,
            "after_public_declarations": 5323, "compared_public_declarations": 5323,
            "missing_public_declarations": [], "added_public_declarations": [], "differences": [],
            "checker": self.reference("scripts/compare_public_types.py"),
            "after_export_sha256": check.digest(self.root / "metadata/declarations.json"),
            "after_source_sha256": self.sources.copy(), "challenge_sha256": challenge_hashes,
            "challenge_root_types": {name: {"before_type_sha256": "a" * 64,
                                             "after_type_sha256": "a" * 64} for name in self.targets},
            "after_export_declarations": 5323, "after_export_theorems": 7,
        }
        self.log = self.valid_log()
        self.write_json(self.SUMMARY, self.summary)
        self.write_json(self.COMPARISON, self.comparison)
        self.write(self.LOG, self.log)
        self.certificate = {
            "schema_version": 1, "status": "passed", "scope": "source_rebuild_with_exact_public_types",
            "source_commit": self.commit, "proof_source_sha256": self.sources.copy(),
            "permitted_transitive_axioms": sorted(check.AXIOMS),
            "external_comparator_execution": "not_run", "independent_kernel_execution": "not_run",
            "build_summary": self.reference(self.SUMMARY), "audit_log": self.reference(self.LOG),
            "audit_log_archive_receipt": {"original_path": self.original_log,
                                          "sha256": check.digest(self.root / self.LOG)},
            "public_type_comparison": self.reference(self.COMPARISON),
            "audited_project_declarations": 5323, "audited_theorem_constants": 7,
        }
        self.save_certificate()

    def git(self, *arguments):
        command = ["git", "-c", "user.name=Synthetic fixture", "-c", "user.email=fixture@example.invalid",
                   "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null",
                   "-c", "core.excludesFile=/dev/null", "-c", "init.defaultBranch=synthetic", *arguments]
        return subprocess.check_output(command, cwd=self.root, text=True, stderr=subprocess.DEVNULL)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def write_json(self, name, value):
        self.write(name, json.dumps(value, indent=2) + "\n")

    def reference(self, name):
        return {"path": name, "sha256": check.digest(self.root / name)}

    def valid_log(self):
        # This is fabricated text exercising the parser, not compiler output.
        return ("".join("Checking " + name + "\n" for name in sorted(self.proof_paths))
                + "AUDIT PASSED: 5323 project declarations, 7 theorems; "
                  "transitive axioms [propext, Quot.sound, Classical.choice].\n"
                + "BUILD PASSED: 4 project modules.\n")

    def save_certificate(self):
        self.write_json(self.CERTIFICATE, self.certificate)

    def save_summary(self):
        self.write_json(self.SUMMARY, self.summary)
        self.certificate["build_summary"] = self.reference(self.SUMMARY)
        self.save_certificate()

    def save_comparison(self):
        self.write_json(self.COMPARISON, self.comparison)
        self.certificate["public_type_comparison"] = self.reference(self.COMPARISON)
        self.save_certificate()

    def save_log(self):
        self.write(self.LOG, self.log)
        self.certificate["audit_log"] = self.reference(self.LOG)
        self.certificate["audit_log_archive_receipt"]["sha256"] = check.digest(self.root / self.LOG)
        self.save_certificate()

    def load(self):
        return check.load_source_certificate(self.root, self.CERTIFICATE, self.proof_paths)

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            self.load()

    def test_complete_synthetic_bindings_are_accepted(self):
        loaded = self.load()
        self.assertEqual(loaded["method"], "full_rebuild_and_exact_public_types")
        self.assertEqual(loaded["source_commit"], self.commit)
        self.assertEqual(loaded["proof_source_sha256"], self.sources)

    def test_boolean_or_float_certificate_schema_version_is_rejected(self):
        for version in (True, 1.0):
            with self.subTest(version=version):
                self.certificate["schema_version"] = version
                self.save_certificate()
                self.reject("Unsupported or incomplete current-source certificate")

    def test_stale_source_and_stale_driver_are_rejected(self):
        for name, message in (("Nonadditivity/Fixture.lean", "Stale certificate proof sources"),
                              ("scripts/compiler.py", "Stale measured source/driver inputs")):
            with self.subTest(file=name):
                original = (self.root / name).read_text()
                self.write(name, original + "changed after synthetic snapshot\n")
                try:
                    self.reject(message)
                finally:
                    self.write(name, original)

    def test_each_measured_driver_binding_is_required(self):
        before = self.summary["source_hashes_before"].copy()
        after = self.summary["source_hashes_after"].copy()
        for name in check.DRIVER_FILES:
            with self.subTest(driver=name):
                self.summary["source_hashes_before"] = {key: value for key, value in before.items() if key != name}
                self.summary["source_hashes_after"] = {key: value for key, value in after.items() if key != name}
                self.save_summary()
                self.reject("Measured source/driver inventory differs")

    def test_unexpected_measured_driver_binding_is_rejected(self):
        name = "scripts/unmeasured.py"
        self.write(name, "# Synthetic unmeasured input\n")
        sha = check.digest(self.root / name)
        self.summary["source_hashes_before"][name] = sha
        self.summary["source_hashes_after"][name] = sha
        self.save_summary()
        self.reject("Measured source/driver inventory differs")

    def test_proof_inventory_omission_is_rejected(self):
        self.certificate["proof_source_sha256"].pop("Audit.lean")
        self.save_certificate()
        self.reject("Certificate proof-source inventory differs")

    def test_certificate_summary_commit_mismatch_is_rejected(self):
        self.certificate["source_commit"] = "f" * 40
        self.save_certificate()
        self.reject("Build source commit or Lean pin differs")

    def test_nonexistent_recorded_commit_is_rejected(self):
        self.certificate["source_commit"] = "f" * 40
        self.summary["provenance"]["commit"] = "f" * 40
        self.save_summary()
        self.reject("Recorded rebuild source commit is unavailable")

    def test_resealed_source_still_must_match_committed_snapshot(self):
        name = "Nonadditivity/Fixture.lean"
        self.write(name, "Changed synthetic source; never committed or compiled\n")
        sha = check.digest(self.root / name)
        self.certificate["proof_source_sha256"][name] = sha
        for field in ("source_hashes_before", "source_hashes_after"):
            self.summary[field][name] = sha
        self.comparison["after_source_sha256"][name] = sha
        self.save_comparison()
        self.save_summary()
        self.reject("Source/driver hashes differ from recorded committed snapshot")

    def test_incomplete_failed_or_duplicate_module_coverage_is_rejected(self):
        original = copy.deepcopy(self.summary["coverage"])
        for change in ({"complete": False}, {"measured": 3}, {"failed": ["Audit"]},
                       {"duplicates": ["Audit"]}, {"order_matches": False}):
            with self.subTest(change=change):
                self.summary["coverage"] = original | change
                self.save_summary()
                self.reject("Measured rebuild lacks complete successful module coverage")

    def test_source_or_dependency_mutation_guards_are_required(self):
        for field in ("source_changes", "dependency_artifact_changes"):
            with self.subTest(field=field):
                self.summary[field] = ["synthetic mutation"]
                self.save_summary()
                try:
                    self.reject("Measured source/dependency guards")
                finally:
                    self.summary[field] = []

    def test_errors_proof_holes_or_authorized_sorries_are_rejected(self):
        original = copy.deepcopy(self.summary["health"])
        for change in ({"error_count": 1}, {"sorry_warning_count": 1},
                       {"unauthorized_sorry_tokens": 1}, {"allowed_sorry_modules": ["Audit"]}):
            with self.subTest(change=change):
                self.summary["health"] = original | change
                self.save_summary()
                self.reject("Recorded rebuild contains errors or authorized proof holes")

    def test_failed_wrong_scope_or_wrong_reference_api_report_is_rejected(self):
        original = copy.deepcopy(self.comparison)
        for change in ({"status": "failed"}, {"scope": "portable_all"},
                       {"schema_version": 99}, {"schema_version": True}, {"schema_version": 1.0},
                       {"before_commit": "f" * 40},
                       {"lean_or_kernel_executed": True},
                       {"selection": {"all_false": ["is_private"]}}):
            with self.subTest(change=change):
                self.comparison = original | change
                self.save_comparison()
                self.reject("Unexpected public-type comparison source, format, or scope")

    def test_incomplete_or_changed_public_type_api_report_is_rejected(self):
        original = copy.deepcopy(self.comparison)
        for change in ({"compared_public_declarations": 5322},
                       {"compared_public_declarations": 5323.0},
                       {"added_public_declarations": ["Fixture.extra"]},
                       {"differences": [{"declaration": "Fixture.root0", "changed_fields": ["level_parameters"]}]}):
            with self.subTest(change=change):
                self.comparison = original | change
                self.save_comparison()
                self.reject("Public declaration inventory or exact types changed")

    def test_missing_or_changed_root_type_api_report_is_rejected(self):
        name = self.targets[0]
        original = copy.deepcopy(self.comparison["challenge_root_types"])
        self.comparison["challenge_root_types"].pop(name)
        self.save_comparison()
        self.reject("Public-type comparison does not cover all six roots")
        self.comparison["challenge_root_types"] = original
        self.comparison["challenge_root_types"][name]["after_type_sha256"] = "b" * 64
        self.save_comparison()
        self.reject("Challenge root type changed")

    def test_stale_export_checker_or_challenge_is_rejected(self):
        cases = (("metadata/declarations.json", "Stale compared declaration export"),
                 ("scripts/compare_public_types.py", "Stale public-type comparison script"),
                 (check.CONFIGS[0], "Stale unchanged challenge inputs"))
        for name, message in cases:
            with self.subTest(file=name):
                original = (self.root / name).read_text()
                self.write(name, original + "changed\n")
                try:
                    self.reject(message)
                finally:
                    self.write(name, original)

    def test_stale_api_report_or_audit_log_hash_is_rejected(self):
        for name, message in ((self.COMPARISON, "Stale public-type comparison"),
                              (self.LOG, "Stale full rebuild/audit log")):
            with self.subTest(file=name):
                original = (self.root / name).read_text()
                self.write(name, original + "changed without rehash\n")
                try:
                    self.reject(message)
                finally:
                    self.write(name, original)

    def test_other_run_archive_receipt_is_rejected(self):
        self.certificate["audit_log_archive_receipt"]["original_path"] = str(self.root / "other-run/build.log")
        self.save_certificate()
        self.reject("exact-copy receipt")

    def test_incomplete_build_log_is_rejected_even_after_rehashing(self):
        self.log = self.log.replace("Checking Audit.lean\n", "")
        self.save_log()
        self.reject("Retained audit is not the complete measured project rebuild log")

    def test_missing_or_duplicate_audit_completion_is_rejected(self):
        original = self.log
        audit = next(line for line in original.splitlines() if line.startswith("AUDIT PASSED:"))
        for altered in (original.replace(audit + "\n", ""), original + audit + "\n"):
            with self.subTest(log=altered):
                self.log = altered
                self.save_log()
                self.reject("Expected one retained full rebuild audit completion")

    def test_extra_axiom_and_disagreeing_audit_counts_are_rejected(self):
        original = self.log
        cases = ((original.replace("Quot.sound, Classical.choice", "Quot.sound, Classical.choice, sorryAx"),
                  "Recorded full audit has unexpected transitive axioms"),
                 (original.replace("5323 project declarations", "5322 project declarations"),
                  "Fresh audit and compared export counts disagree"))
        for altered, message in cases:
            with self.subTest(message=message):
                self.log = altered
                self.save_log()
                self.reject(message)

    def test_unsafe_extra_field_reference_and_overclaimed_scope_are_rejected(self):
        original = copy.deepcopy(self.certificate)
        for reference in ({"path": "../outside.json", "sha256": "a" * 64},
                          self.certificate["public_type_comparison"] | {"status": "passed"}):
            with self.subTest(reference=reference):
                self.certificate = copy.deepcopy(original)
                self.certificate["public_type_comparison"] = reference
                self.save_certificate()
                self.reject("Unsafe certificate path|Invalid public-type comparison reference")
        self.certificate = original
        self.certificate["independent_kernel_execution"] = "passed"
        self.save_certificate()
        self.reject("must retain its Lean-only scope")


class AdditiveCertificateControls(unittest.TestCase):
    """Synthetic controls for the single-challenge extension; no proof tools run."""
    EXTENSION = "verification/synthetic/additive/source-certificate.json"
    OLD_LAKEFILE = "verification/synthetic/additive/base-lakefile.toml"

    def setUp(self):
        self.fixture = SourceCertificateControls()
        self.fixture.setUp()
        self.addCleanup(self.fixture.temporary.cleanup)
        self.root = self.fixture.root
        f = self.fixture
        # The extra root must already be a public theorem in a measured module.
        old_proof = "Nonadditivity/Fixture.lean"
        new_proof = "Nonadditivity/DeterministicConsequences.lean"
        (self.root / old_proof).rename(self.root / new_proof)
        f.proof_paths = (f.proof_paths - {old_proof}) | {new_proof}
        roots = [name.removesuffix(".json").replace("/", ".") for name in check.CONFIGS]
        self.old_lakefile = ('name = "synthetic"\n\n[[lean_lib]]\nname = "Nonadditivity"\n\n'
                            '[[lean_lib]]\nname = "ComparatorChallenges"\nroots = '
                            + json.dumps(roots) + '\n')
        self.new_lakefile = self.old_lakefile.replace(json.dumps(roots), json.dumps(roots + [check.ADDITIONAL_MODULE]))
        f.write("lakefile.toml", self.old_lakefile)
        self.root_entry = {"name": check.ADDITIONAL_ROOT, "kind": "theorem",
                           "module": check.ADDITIONAL_SOLUTION, "file": new_proof,
                           "type_sha256": "c" * 64, **{flag: False for flag in check.PUBLIC_FLAGS}}
        f.write_json("metadata/declarations.json", {"declarations": [self.root_entry]})
        f.git("add", "--all")
        f.git("commit", "--quiet", "-m", "Synthetic additive predecessor; no proof execution")
        f.commit = f.git("rev-parse", "HEAD").strip()
        f.sources = {name: check.digest(self.root / name) for name in sorted(f.proof_paths)}
        f.measured_inputs = {name: check.digest(self.root / name)
                             for name in sorted(f.proof_paths | set(check.DRIVER_FILES))}
        f.summary["provenance"]["commit"] = f.commit
        f.summary["modules"] = {name.removesuffix(".lean").replace("/", "."): name for name in f.proof_paths}
        f.summary["source_hashes_before"] = f.measured_inputs.copy()
        f.summary["source_hashes_after"] = f.measured_inputs.copy()
        f.certificate["source_commit"] = f.commit
        f.certificate["proof_source_sha256"] = f.sources.copy()
        f.comparison["after_source_sha256"] = f.sources | {"lakefile.toml": f.measured_inputs["lakefile.toml"]}
        f.comparison["after_export_sha256"] = check.digest(self.root / "metadata/declarations.json")
        f.log = f.valid_log()
        f.save_comparison()
        f.save_summary()
        f.save_log()
        f.write(self.OLD_LAKEFILE, self.old_lakefile)
        f.write("lakefile.toml", self.new_lakefile)
        self.extra_config = {"challenge_module": check.ADDITIONAL_MODULE,
                             "solution_module": check.ADDITIONAL_SOLUTION,
                             "theorem_names": [check.ADDITIONAL_ROOT],
                             "permitted_axioms": sorted(check.AXIOMS), "enable_nanoda": False}
        f.write_json(check.ADDITIONAL_CONFIG, self.extra_config)
        f.write(check.ADDITIONAL_CONFIG.removesuffix(".json") + ".lean", "-- Synthetic expected statement only\n")
        self.extension = {
            "schema_version": 2, "status": "passed", "scope": check.ADDITIVE_SCOPE,
            "base_certificate": f.reference(f.CERTIFICATE), "historical_lakefile": f.reference(self.OLD_LAKEFILE),
            "current_lakefile_sha256": check.digest(self.root / "lakefile.toml"),
            "additional_challenge_sha256": {name: check.digest(self.root / name) for name in
                (check.ADDITIONAL_CONFIG, check.ADDITIONAL_CONFIG.removesuffix(".json") + ".lean")},
            "additional_root": {key: self.root_entry[key] for key in ("name", "kind", "module", "file", "type_sha256")},
            "permitted_transitive_axioms": sorted(check.AXIOMS),
            "new_source_rebuild": "not_run", "additional_expected_statement_check": "not_run",
            "external_comparator_execution": "not_run", "independent_kernel_execution": "not_run",
        }
        self.save()

    def save(self):
        self.fixture.write_json(self.EXTENSION, self.extension)

    def load(self):
        return check.load_source_certificate(self.root, self.EXTENSION, self.fixture.proof_paths)

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            self.load()

    def rebind_extra(self):
        self.fixture.write_json(check.ADDITIONAL_CONFIG, self.extra_config)
        self.extension["additional_challenge_sha256"][check.ADDITIONAL_CONFIG] = check.digest(self.root / check.ADDITIONAL_CONFIG)
        self.save()

    def test_explicit_extension_accepts_only_historical_proof_evidence_scope(self):
        result = self.load()
        self.assertEqual(result["method"], "recorded_rebuild_and_exact_public_types_with_additive_challenge")
        self.assertEqual(result["source_commit"], self.fixture.commit)
        self.assertEqual(result["proof_source_sha256"], self.fixture.sources)
        self.assertEqual(result["additional_root"], check.ADDITIONAL_ROOT)
        self.assertEqual(result["new_source_rebuild"], "not_run")
        self.assertEqual(result["additional_expected_statement_check"], "not_run")

    def test_schema1_still_rejects_the_changed_current_driver(self):
        self.fixture.reject("Stale measured source/driver inputs: lakefile.toml")

    def test_no_proof_other_driver_or_base_challenge_exception_is_allowed(self):
        cases = (("Nonadditivity/DeterministicConsequences.lean", "Stale certificate proof sources"),
                 ("scripts/compiler.py", "Stale measured source/driver inputs"),
                 (check.CONFIGS[0], "Stale unchanged challenge inputs"))
        for name, message in cases:
            with self.subTest(name=name):
                original = (self.root / name).read_text()
                self.fixture.write(name, original + "changed\n")
                try:
                    self.reject(message)
                finally:
                    self.fixture.write(name, original)

    def test_rebound_lakefile_still_cannot_change_build_configuration(self):
        alternatives = (self.new_lakefile.replace('name = "synthetic"', 'name = "changed"'),
                        self.new_lakefile.replace(check.ADDITIONAL_MODULE, "ComparatorChallenges.Other"),
                        self.new_lakefile + '\n[[require]]\nname = "unmeasured"\n',
                        self.new_lakefile.replace(check.ADDITIONAL_MODULE, check.ADDITIONAL_MODULE + '", "' + check.ADDITIONAL_MODULE))
        for value in alternatives:
            with self.subTest(value=value):
                self.fixture.write("lakefile.toml", value)
                self.extension["current_lakefile_sha256"] = check.digest(self.root / "lakefile.toml")
                self.save()
                self.reject("Lake configuration changed beyond appending")

    def test_historical_driver_cannot_be_resealed_to_different_bytes(self):
        self.fixture.write(self.OLD_LAKEFILE, self.old_lakefile + "# Changed historical bytes\n")
        self.extension["historical_lakefile"] = self.fixture.reference(self.OLD_LAKEFILE)
        self.save()
        self.reject("Stale measured source/driver inputs: lakefile.toml")

    def test_missing_extra_inputs_and_stale_challenge_bytes_are_rejected(self):
        source = check.ADDITIONAL_CONFIG.removesuffix(".json") + ".lean"
        self.fixture.write(source, "changed without binding\n")
        self.reject("Stale additional challenge inputs")
        self.extension["additional_challenge_sha256"].pop(source)
        self.save()
        self.reject("Unexpected additive challenge input inventory")

    def test_rebound_wrong_target_solution_or_axiom_policy_is_rejected(self):
        original = copy.deepcopy(self.extra_config)
        for fields in ({"theorem_names": ["Nonadditivity.Other"]}, {"solution_module": "Nonadditivity.Other"},
                       {"permitted_axioms": sorted(check.AXIOMS) + ["sorryAx"]}, {"enable_nanoda": True},
                       {"unrecorded_option": True}):
            with self.subTest(fields=fields):
                self.extra_config = original | fields
                self.rebind_extra()
                self.reject("Unexpected additive challenge target, modules, or axiom policy")

    def test_unrecorded_additional_configuration_is_rejected(self):
        self.fixture.write_json("ComparatorChallenges/G_Unrecorded.json", self.extra_config)
        self.reject("Unexpected additive Comparator configuration inventory")

    def test_additional_root_type_claim_must_match_unchanged_export(self):
        self.extension["additional_root"]["type_sha256"] = "d" * 64
        self.save()
        self.reject("Additional root identity or type differs")

    def test_additional_root_must_be_previously_public_and_a_theorem(self):
        for fields in ({"kind": "definition"}, {"is_private": True}, {"is_internal": True},
                       {"file": "Nonadditivity/Other.lean"}):
            with self.subTest(fields=fields):
                self.fixture.write_json("metadata/declarations.json", {"declarations": [self.root_entry | fields]})
                self.fixture.comparison["after_export_sha256"] = check.digest(self.root / "metadata/declarations.json")
                self.fixture.save_comparison()
                self.extension["base_certificate"] = self.fixture.reference(self.fixture.CERTIFICATE)
                self.save()
                self.reject("Additional root is not a previously compared public theorem")

    def test_extension_cannot_claim_any_fresh_proof_execution(self):
        for flag in ("new_source_rebuild", "additional_expected_statement_check",
                     "external_comparator_execution", "independent_kernel_execution"):
            with self.subTest(flag=flag):
                self.extension[flag] = "passed"
                self.save()
                try:
                    self.reject("must not claim new proof execution")
                finally:
                    self.extension[flag] = "not_run"

    def test_base_certificate_hash_and_schema_remain_required(self):
        self.extension["base_certificate"]["sha256"] = "e" * 64
        self.save()
        self.reject("Stale base source certificate")
        self.fixture.certificate["schema_version"] = 2
        self.fixture.save_certificate()
        self.extension["base_certificate"] = self.fixture.reference(self.fixture.CERTIFICATE)
        self.save()
        self.reject("must reference an immutable schema-1 rebuild certificate")


if __name__ == "__main__":
    unittest.main()
