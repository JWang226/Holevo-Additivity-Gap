#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Focused tests of continuation request and source-boundary checks; no Lean."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("continuation", Path(__file__).with_name("elaboration_continue.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ContinuationTests(unittest.TestCase):
    def setUp(self):
        self.state = {"baseline_sha": "a" * 40, "next_sequence": 1,
                      "modules": {"Nonadditivity.Example": "Nonadditivity/Example.lean"}}
        self.request = {"schema_version": 1, "sequence": 1, "mode": "profile",
                        "baseline_sha": "a" * 40, "candidate_sha": "b" * 40,
                        "modules": ["Nonadditivity.Example"], "repetitions": 3}

    def test_valid_profile(self):
        module.request_schema(self.request, self.state)

    def test_valid_final_with_baseline_sha(self):
        module.request_schema({"schema_version": 1, "sequence": 1, "mode": "final",
                               "baseline_sha": "a" * 40, "after_sha": "a" * 40}, self.state)

    def test_arbitrary_commands_rejected(self):
        self.request["command"] = "echo unexpected"
        with self.assertRaises(ValueError):
            module.request_schema(self.request, self.state)

    def test_sequence_and_boolean_rejected(self):
        for value in (2, True):
            self.request["sequence"] = value
            with self.assertRaises(ValueError):
                module.request_schema(self.request, self.state)

    def test_unknown_module_rejected(self):
        self.request["modules"] = ["Mathlib.Data.Nat.Basic"]
        with self.assertRaises(ValueError):
            module.request_schema(self.request, self.state)

    def test_abbreviated_sha_rejected(self):
        self.request["candidate_sha"] = "abc123"
        with self.assertRaises(ValueError):
            module.request_schema(self.request, self.state)

    def test_shell_ref_rejected(self):
        for ref in ("-bad", "a..b", "refs/heads/a;echo x", "$(command)", "a@{b}"):
            with self.assertRaises(ValueError):
                module.safe_ref(ref)

    def test_source_diff_allowed(self):
        raw = ":100644 100644 " + "a" * 40 + " " + "b" * 40 + " M\tNonadditivity/Example.lean"
        with patch.object(module, "git", return_value=raw):
            self.assertEqual(module.changed_sources(Path("."), "a", "b", self.state["modules"]),
                             {"Nonadditivity.Example"})

    def test_driver_and_symlink_diffs_rejected(self):
        for mode, path in (("100644", "scripts/compiler.py"), ("120000", "Nonadditivity/Example.lean")):
            raw = ":100644 " + mode + " " + "a" * 40 + " " + "b" * 40 + " M\t" + path
            with patch.object(module, "git", return_value=raw), self.assertRaises(ValueError):
                module.changed_sources(Path("."), "a", "b", self.state["modules"])

    def test_zero_net_final_change_allowed_but_trial_rejected(self):
        with patch.object(module, "git", return_value=""):
            self.assertEqual(module.changed_sources(Path("."), "a", "a", self.state["modules"],
                                                    require_change=False), set())
            with self.assertRaises(ValueError):
                module.changed_sources(Path("."), "a", "a", self.state["modules"])


if __name__ == "__main__":
    unittest.main()
