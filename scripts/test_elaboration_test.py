#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Focused tests of measurement parsing and complete own-build coverage.

These tests invoke no Lean, Lake, cache restoration or project build.
"""
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch
import subprocess

import elaboration_test as measurement


def time_output(elapsed="1:02.50", cpu="237%"):
    return f"""Command being timed: \"/path/with spaces/lean A.lean\"
\tUser time (seconds): 2.40
\tSystem time (seconds): 0.60
\tPercent of CPU this job got: {cpu}
\tElapsed (wall clock) time (h:mm:ss or m:ss): {elapsed}
\tMaximum resident set size (kbytes): 2048
\tExit status: 0
"""


class TimingParserTests(unittest.TestCase):
    def test_fractional_minutes_hours_and_cpu_above_one_core(self):
        result = measurement.parse_gnu_time(time_output())
        self.assertEqual(result["wall_s"], 62.5)
        self.assertEqual(result["percent_cpu"], 237)
        self.assertEqual(result["cpu_s"], 3)
        self.assertEqual(measurement.parse_gnu_time(time_output("1:02:03.25"))["wall_s"], 3723.25)
        self.assertEqual(measurement.parse_gnu_time(time_output("0:00.00", "0%"))["wall_s"], 0)

    def test_missing_fields_are_not_silently_zero(self):
        output = time_output().replace("\tMaximum resident set size (kbytes): 2048\n", "")
        with self.assertRaisesRegex(ValueError, "max_rss_raw"):
            measurement.parse_gnu_time(output)

    def test_signal_survives_misleading_printed_exit_status(self):
        result = measurement.parse_gnu_time("Command terminated by signal 9\n" + time_output())
        self.assertEqual(result["reported_exit_status"], 0)
        self.assertIn("signal 9", result["signal"])


class ProfileParserTests(unittest.TestCase):
    def test_colon_categories_and_events_are_not_double_counted(self):
        result = measurement.parse_profile("""typeclass inference of foo took 125ms
interpretation: Tactic.nlinarith took 2.1s of foo
cumulative profiling times:
  typeclass inference: 250ms
  interpretation: Tactic.nlinarith: 7.5s
  import: 1s
  type checking  0.5s
""")
        self.assertEqual(result["phases_s"]["interpretation: Tactic.nlinarith"], 7.5)
        self.assertEqual(result["categorized_s"], 9.25)
        self.assertEqual(len(result["events_over_100ms"]), 2)
        self.assertTrue(result["dominant_above_action_floor"])

    def test_events_without_totals_do_not_invent_attribution(self):
        result = measurement.parse_profile("elaboration took 6s\n")
        self.assertEqual(result["phases_s"], {})
        self.assertIsNone(result["dominant_phase"])
        self.assertFalse(result["dominant_above_action_floor"])


class CoverageTests(unittest.TestCase):
    @staticmethod
    def record(name, phase="build", returncode=0):
        return {"module": name, "phase": phase, "returncode": returncode}

    def test_missing_duplicate_wrong_order_and_failed_jobs_are_invalid(self):
        expected = ["A", "B", "All"]
        self.assertTrue(measurement.coverage_check(expected, [self.record(name) for name in expected])["complete"])
        for actual in ([self.record("A"), self.record("All")],
                       [self.record("A"), self.record("A"), self.record("B"), self.record("All")],
                       [self.record("B"), self.record("A"), self.record("All")],
                       [self.record("A"), self.record("B", returncode=1), self.record("All")]):
            self.assertFalse(measurement.coverage_check(expected, actual)["complete"])

    def test_warm_profiles_are_not_build_coverage(self):
        result = measurement.coverage_check(["A", "All"], [self.record("A"), self.record("All"), self.record("A", "profile")])
        self.assertTrue(result["complete"])
        self.assertEqual(result["measured"], 2)

    def test_longest_import_path_keeps_dependency_order(self):
        graph = {"A": [], "B": [], "C": ["A", "B"], "All": ["C"]}
        result = measurement.longest_weighted_path(graph, {"A": 2, "B": 3, "C": 5, "All": 1})
        self.assertEqual(result, {"seconds": 9, "modules": ["B", "C", "All"]})


class SourceProvenanceTests(unittest.TestCase):
    def test_unavailable_process_inventory_is_informational(self):
        with patch.object(measurement.subprocess, "run", side_effect=PermissionError("restricted")):
            inventory = measurement.process_inventory()
        self.assertFalse(inventory["available"])
        self.assertIn("restricted", inventory["error"])
        self.assertEqual(measurement.process_inventory_description(inventory), "unavailable")
        with patch.object(measurement.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "", "denied")):
            self.assertEqual(measurement.process_inventory()["error"], "denied")
        with patch.object(measurement.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "123 00:02 /bin/lean A.lean\n124 00:02 ps\n", "")):
            inventory = measurement.process_inventory()
        self.assertEqual(measurement.process_inventory_description(inventory), "1")

    def test_comments_strings_and_legacy_headers(self):
        snapshot = measurement.size_snapshot({
            "OnlyComment.lean": "/- nested /- comment -/ -/\n-- more\n",
            "Legacy.lean": 'def text := "-- not a comment /-"\n',
            "Modern.lean": "-- header\nmodule\nimport Init\n",
        })
        self.assertEqual(snapshot["counted_files"], 2)
        self.assertEqual(snapshot["code_lines"], 3)
        self.assertEqual(snapshot["comment_only_files"], ["OnlyComment.lean"])
        self.assertIn("Legacy.lean", snapshot["legacy_nonmodule_files"])
        self.assertNotIn("Modern.lean", snapshot["legacy_nonmodule_files"])
        self.assertFalse(measurement.module_header("/-! module documentation -/\nmodule\n"))

    def test_source_guard_detects_addition_edit_and_deletion(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Nonadditivity").mkdir()
            source = root / "Nonadditivity/A.lean"
            source.write_text("def a := 1\n")
            before = measurement.source_stat_manifest(root)
            self.assertEqual(measurement.manifest_changes(before, measurement.source_stat_manifest(root)), [])
            source.write_text("def a := 1234\n")
            self.assertEqual(measurement.manifest_changes(before, measurement.source_stat_manifest(root)), ["Nonadditivity/A.lean"])
            (root / "Nonadditivity/B.lean").write_text("def b := 2\n")
            self.assertIn("Nonadditivity/B.lean", measurement.manifest_changes(before, measurement.source_stat_manifest(root)))
            source.unlink()
            self.assertIn("Nonadditivity/A.lean", measurement.manifest_changes(before, measurement.source_stat_manifest(root)))


if __name__ == "__main__":
    unittest.main()
