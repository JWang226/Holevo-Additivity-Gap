#!/usr/bin/env python3
"""Small deterministic fixtures for report parsing, scope and comparison math."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("comparison", Path(__file__).with_name("compare_elaboration.py"))
comparison = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(comparison)


def timing(wall=10., cpu=8.):
    return {"wall_s": wall, "cpu_s": cpu, "user_s": cpu - 1, "sys_s": 1.,
            "max_rss_raw": 1000, "percent_cpu": 80}


def snapshot(walls, *, lines=100):
    records = {}
    for i, wall in enumerate(walls):
        name = "Project.File" + str(i)
        records[name] = {"module": name, "source": "Project/File" + str(i) + ".lean",
                         "source_sha256": "a" * 64, "timing": timing(wall, wall * .8)}
    provenance = {key: "same" for key in comparison.MATCH_KEYS}
    return {"summary": {"provenance": provenance, "build": {"timing": timing(sum(walls), sum(walls) * .8)},
                        "size": {"git_build_scope": {"code_lines": lines}}},
            "builds": records, "profiles": {}}


class MathAndScopeTests(unittest.TestCase):
    def test_full_join_keeps_prior_value_for_new_heavy_module(self):
        before = snapshot(list(range(1, 33)))
        after = snapshot([50] + list(range(2, 33)))
        result = comparison.compare_builds(before, after)
        first = result["top_30_after"][0]
        self.assertEqual(first["module"], "Project.File0")
        self.assertEqual(first["wall_s"]["before"], 1)
        self.assertEqual(first["wall_s"]["delta"], 49)
        self.assertEqual(len(result["per_module"]), 32)

    def test_zero_growth_does_not_invent_prediction_ratio(self):
        result = comparison.compare_builds(snapshot([10]), snapshot([12]))
        self.assertEqual(result["size_prediction"]["predicted_cpu_delta_s"], 0)
        self.assertIsNone(result["size_prediction"]["absolute_actual_predicted_ratio"])

    def test_size_prediction_uses_cpu_not_wall(self):
        result = comparison.compare_builds(snapshot([10], lines=100), snapshot([10], lines=110))
        self.assertAlmostEqual(result["size_prediction"]["predicted_cpu_delta_s"], .8)
        self.assertAlmostEqual(result["sums"]["before"]["observed_cpu_parallelism"], .8)

    def test_unmatched_tools_or_module_scope_rejected(self):
        before, after = snapshot([10]), snapshot([10])
        after["summary"]["provenance"]["time_sha256"] = "different"
        with self.assertRaisesRegex(ValueError, "Timing setup differs"):
            comparison.compare_builds(before, after)
        with self.assertRaisesRegex(ValueError, "Module inventories differ"):
            comparison.compare_builds(snapshot([10]), snapshot([10, 11]))

    def test_zero_baseline_percent_is_unknown(self):
        self.assertIsNone(comparison.delta(0, 10)["percent"])


class LexicalAndProfileTests(unittest.TestCase):
    def test_census_masks_nested_comments_strings_and_preserves_line_numbers(self):
        text = '/- set_option maxHeartbeats 9 /- nlinarith -/ -/\n' + \
               'def s := "simp set_option maxRecDepth 8"\n' + \
               'set_option maxHeartbeats 200 in\n' + \
               'example : True := by\n  simp\n'
        summary = {"provenance": {"commit": "x"}, "size": {"git_build_scope": {"per_file": {
                   "Project/A.lean": {"total_lines": 5, "code_lines": 4, "module_header": False}}}},
                   "source_hashes_before": {"Project/A.lean": hashlib.sha256(text.encode()).hexdigest()}}
        result = comparison.source_census(summary, {"Project/A.lean": text})
        self.assertEqual(result["override_counts"], {"maxHeartbeats": 1})
        self.assertEqual(result["overrides"][0]["line"], 3)
        self.assertEqual(result["tactic_token_counts"]["nlinarith"], 0)
        self.assertEqual(result["tactic_token_counts"]["simp"], 1)

    def test_missing_phase_is_not_zero_and_unmatched_profile_is_explicit(self):
        record = {"returncode": 0, "guard_errors": [], "timing": timing(),
                  "profile": {"phases_s": {"import": 2}, "events_over_100ms": []}}
        before, after = snapshot([10]), snapshot([10])
        before["profiles"] = {"A": copy.deepcopy(record), "B": copy.deepcopy(record)}
        after["profiles"] = {"A": copy.deepcopy(record)}
        after["profiles"]["A"]["profile"]["phases_s"]["simp"] = .1
        result = comparison.compare_profiles(before, after)
        phase = result["modules"][0]["phases"]["simp"]
        self.assertIsNone(phase["before"])
        self.assertIsNone(phase["delta"])
        self.assertEqual(result["modules"][1]["available_side"], "before")

    def test_duplicate_json_key_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            path.write_text('{"valid":true,"valid":false}')
            with self.assertRaisesRegex(ValueError, "Duplicate"):
                comparison.load(path)


class InterventionTests(unittest.TestCase):
    def fixture(self, basis="phase"):
        return {"schema_version": 1, "status": "completed", "module": "A", "intervention": "narrow imports",
                "basis": basis, "relevant_phase": "import" if basis == "phase" else None,
                "before_runs": [{"wall_s": 10, "phases_s": {"import": 10}}],
                "after_runs": [{"wall_s": 8, "phases_s": {"import": 8}}],
                "matched_setup": True, "other_phases_regressed": False, "statements_changed": False, "kept": True}

    def test_phase_threshold_accepts_two_seconds_or_ten_percent(self):
        self.assertTrue(comparison.assess_ab(self.fixture())["supports_retaining_edit"])
        data = self.fixture()
        data["before_runs"][0]["phases_s"]["import"] = 1
        data["after_runs"][0]["phases_s"]["import"] = .9
        self.assertTrue(comparison.assess_ab(data)["supports_retaining_edit"])

    def test_wall_basis_requires_three_runs_per_side(self):
        data = self.fixture("wall")
        self.assertFalse(comparison.assess_ab(data)["supports_retaining_edit"])
        data["before_runs"] *= 3
        data["after_runs"] *= 3
        self.assertTrue(comparison.assess_ab(data)["supports_retaining_edit"])

    def test_no_retention_support_for_transferred_regression_or_statement_changes(self):
        for key in ("other_phases_regressed", "statements_changed"):
            data = self.fixture()
            data[key] = True
            self.assertFalse(comparison.assess_ab(data)["supports_retaining_edit"])

    def test_below_threshold_and_nan_are_not_wins(self):
        data = self.fixture()
        data["after_runs"][0]["phases_s"]["import"] = 9.5
        self.assertFalse(comparison.assess_ab(data)["supports_retaining_edit"])
        data["after_runs"][0]["phases_s"]["import"] = float("nan")
        with self.assertRaises(ValueError):
            comparison.assess_ab(data)


class ReportTests(unittest.TestCase):
    def report_fixture(self):
        before, after = snapshot([10]), snapshot([9])
        for item in (before, after):
            summary = item["summary"]
            summary["provenance"].update({"commit": "a" * 40, "started_utc": "2026-10-06T00:00:00Z",
                "finished_utc": "2026-10-06T00:00:10Z", "platform": "fixture", "compiler_version": "fixture Lean",
                "time_version": "GNU time fixture", "invocation": ["python3", "measure.py"]})
            summary["health"] = {key: 0 for key in ("error_count", "warning_count", "sorry_warning_count", "unauthorized_sorry_tokens")}
            summary["health"]["warning_kinds"] = {}
            summary["coverage"] = {"measured": 1}
            summary["build"]["returncode"] = 0
            size = {"counted_files": 1, "total_lines": 100, "code_lines": 100}
            for scope in ("git_tree", "git_build_scope", "working_build_scope"):
                summary["size"][scope] = dict(size)
            item["dependencies"] = {"packages": []}
        census = {"maximum_physical_lines": 100, "legacy_nonmodule_count": 1,
                  "files_over_1000_lines": [], "files_over_1500_lines": [],
                  "override_counts": {}, "tactic_token_counts": {}, "caveat": "fixture census"}
        data = {"snapshots": {"before": before, "after": after},
                "comparison": comparison.compare_builds(before, after), "source_census": {"before": census, "after": census},
                "profiles": comparison.compare_profiles(before, after), "dead_code": None, "ab": [],
                "api_check": None, "invocation": ["python3", "compare_elaboration.py"]}
        return data

    def test_rendering_keeps_missing_api_and_ab_claims_explicit(self):
        rendered = comparison.report(self.report_fixture())
        self.assertIn("No validated public-type comparison record", rendered)
        self.assertIn("No per-intervention A/B record", rendered)
        self.assertIn("pre-elaboration baseline", rendered)
        self.assertIn("Every compiler invocation is timed", rendered)

    def test_failed_intervention_renders_diagnostics_with_medians_excluded(self):
        data = self.report_fixture()
        failure = {"schema_version": 1, "status": "failed_intervention", "decision": "reverted", "kept": False,
                   "module": "Project.File0", "intervention": "Private helper experiment", "basis": "phase",
                   "relevant_phase": "elaboration", "performance_comparison_excluded": True,
                   "failure_reason": "All three candidates reached deterministic heartbeat timeouts.",
                   "before_runs": [{"valid": True, "returncode": 0, "wall_s": 55} for _ in range(3)],
                   "after_runs": [{"valid": False, "returncode": 1, "wall_s": 150} for _ in range(3)],
                   "diagnostic_failed_attempts": [{"repetition": i, "record": {"returncode": 1,
                      "guard_errors": [], "artifact_changes": [], "timing": {"wall_s": 150., "cpu_s": 148.},
                      "diagnostics": {"error_count": 2, "errors": ["whnf timeout", "tactic timeout"]}}} for i in (1, 2, 3)]}
        data["ab"] = [comparison.assess_ab(failure)]
        rendered = comparison.report(data)
        self.assertIn("FAILED; performance comparison excluded", rendered)
        self.assertIn("neither a valid speed regression nor a valid null result", rendered)
        self.assertIn("150.00", rendered)
        self.assertIn("CPU s (diagnostic)", rendered)


class SnapshotEvidenceTests(unittest.TestCase):
    def write_fixture(self, directory):
        root = Path(directory)
        fixture = snapshot([10])
        summary = fixture["summary"]
        summary.update({"valid": True, "invalid_reasons": [], "coverage": {"complete": True, "measured": 1},
            "modules": {"Project.File0": "Project/File0.lean"},
            "source_hashes_before": {"Project/File0.lean": "a" * 64},
            "source_hashes_after": {"Project/File0.lean": "a" * 64},
            "source_changes": [], "dependency_artifact_changes": [], "dependency_olean_count": 1,
            "dependency_manifests": {side: "/old-host/dependencies-" + side + ".json" for side in ("before", "after")},
            "profiles": []})
        summary["build"]["returncode"] = 0
        summary["provenance"]["time_version"] = "GNU time 1.9"
        record = fixture["builds"]["Project.File0"]
        record.update({"phase": "build", "returncode": 0, "guard_errors": []})
        (root / "summary.json").write_text(json.dumps(summary))
        (root / "measurements.jsonl").write_text(json.dumps(record) + "\n")
        dep = {"olean_count": 1, "artifacts": {"/old-cache/A.olean": {"size": 12, "mtime_ns": 5, "inode": 8}}, "packages": []}
        for side in ("before", "after"):
            (root / ("dependencies-" + side + ".json")).write_text(json.dumps(dep))
        return root / "summary.json"

    def test_moved_evidence_uses_sibling_manifests(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_fixture(directory)
            result = comparison.read_snapshot(path, None)
            self.assertEqual(len(result["builds"]), 1)
            self.assertEqual(result["dependencies"]["olean_count"], 1)

    def test_invalid_snapshot_or_mutated_cache_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_fixture(directory)
            summary = json.loads(path.read_text())
            summary["valid"] = False
            path.write_text(json.dumps(summary))
            with self.assertRaisesRegex(ValueError, "Snapshot is invalid"):
                comparison.read_snapshot(path, None)
            path = self.write_fixture(directory)
            dep_path = path.parent / "dependencies-after.json"
            dep = json.loads(dep_path.read_text())
            dep["artifacts"]["/old-cache/A.olean"]["mtime_ns"] = 6
            dep_path.write_text(json.dumps(dep))
            with self.assertRaisesRegex(ValueError, "Cached dependency artifacts changed"):
                comparison.read_snapshot(path, None)


class SupplementalProfileTests(unittest.TestCase):
    def fixture(self):
        before, after = snapshot([10, 9]), snapshot([9, 8])
        sources = {name: item["source"] for name, item in after["builds"].items()}
        for side, item in (("before", before), ("after", after)):
            item["summary"]["modules"] = dict(sources)
            item["summary"]["source_hashes_before"] = {path: "a" * 64 for path in sources.values()}
            item["summary"]["source_hashes_after"] = {path: "a" * 64 for path in sources.values()}
            item["summary"]["provenance"].update({"commit": ("a" if side == "before" else "b") * 40,
                "time_bin": "/usr/bin/time", "compiler": "/toolchain/bin/lean"})
        def record(name):
            return {"module": name, "source": sources[name], "source_sha256": "a" * 64,
                    "phase": "profile", "valid": True, "returncode": 0,
                    "guard_errors": [], "artifact_changes": [], "timing": timing(),
                    "profile": {"phases_s": {"import": 2}, "events_over_100ms": []},
                    "command": ["/usr/bin/time", "-v", "-o", "/raw/time.txt", "/toolchain/bin/lean", "--profile", sources[name]]}
        first, second = "Project.File0", "Project.File1"
        before["profiles"] = {first: record(first)}
        after["profiles"] = {second: record(second)}
        before["summary"]["profiles"] = list(before["profiles"].values())
        after["summary"]["profiles"] = list(after["profiles"].values())
        summary = {"valid": True, "after_sha": "b" * 40,
                   "compiler_sha256": "same", "time_sha256": "same", "host": "same",
                   "requested_modules": [first], "baseline_top8_modules": [first], "after_top8_modules": [second],
                   "edited_modules": [], "profiles": [record(first)]}
        return before, after, summary

    def write_summary(self, root, summary, raw=False):
        path = Path(root) / "summary.json"
        path.write_text(json.dumps(summary))
        if raw:
            record = summary["profiles"][0]
            leaf = path.parent / record["module"].replace(".", "_")
            leaf.mkdir()
            (leaf / "result.json").write_text(json.dumps(record))
            raw_record = {key: value for key, value in record.items() if key != "valid"}
            (leaf / "measurements.jsonl").write_text(json.dumps(raw_record) + "\n")
        return path

    def test_merge_preserves_original_after_summary_and_labels_supplement(self):
        before, after, summary = self.fixture()
        original = copy.deepcopy(after)
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_summary(directory, summary, raw=True)
            supplement = comparison.supplemental_profiles(path, before, after)
            joined = comparison.compare_profiles(before, after, supplement)
        self.assertEqual(after, original)
        self.assertEqual(joined["matched_count"], 1)
        self.assertEqual(joined["modules"][0]["after_provenance"], "supplemental after warm profile")
        self.assertEqual(len(supplement["input_sha256"]), 3)

    def test_commit_tools_host_and_source_tampering_are_rejected(self):
        for key in ("after_sha", "compiler_sha256", "time_sha256", "host", "source_sha256"):
            before, after, summary = self.fixture()
            if key == "source_sha256":
                summary["profiles"][0][key] = "f" * 64
            else:
                summary[key] = "different"
            with tempfile.TemporaryDirectory() as directory:
                path = self.write_summary(directory, summary)
                with self.assertRaises(ValueError):
                    comparison.supplemental_profiles(path, before, after)

    def test_failed_guarded_record_and_incomplete_baseline_matching_are_rejected(self):
        for mutate in (lambda data: data["profiles"][0].update({"guard_errors": ["changed"]}),
                       lambda data: data["profiles"][0].update({"valid": False}),
                       lambda data: data.update({"requested_modules": [], "profiles": []})):
            before, after, summary = self.fixture()
            mutate(summary)
            with tempfile.TemporaryDirectory() as directory:
                with self.assertRaises(ValueError):
                    comparison.supplemental_profiles(self.write_summary(directory, summary), before, after)

    def test_adjacent_raw_measurement_disagreement_is_rejected(self):
        before, after, summary = self.fixture()
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_summary(directory, summary, raw=True)
            raw_path = path.parent / "Project_File0/measurements.jsonl"
            raw = json.loads(raw_path.read_text())
            raw["timing"]["wall_s"] += 1
            raw_path.write_text(json.dumps(raw) + "\n")
            with self.assertRaisesRegex(ValueError, "raw measurement differs"):
                comparison.supplemental_profiles(path, before, after)

    def test_duplicate_agreement_is_preserved_but_disagreement_rejected(self):
        before, after, summary = self.fixture()
        after["profiles"] = copy.deepcopy(before["profiles"])
        after["summary"]["profiles"] = list(after["profiles"].values())
        summary["after_top8_modules"] = list(after["profiles"])
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_summary(directory, summary)
            result = comparison.supplemental_profiles(path, before, after)
            self.assertEqual(result["identical_duplicates"], ["Project.File0"])
            summary["profiles"][0]["timing"]["wall_s"] += 1
            path = self.write_summary(directory, summary)
            with self.assertRaisesRegex(ValueError, "duplicate disagrees"):
                comparison.supplemental_profiles(path, before, after)


if __name__ == "__main__":
    unittest.main()
