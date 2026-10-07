#!/usr/bin/env python3
"""Deterministic fixtures only: no Lean/builds, Git writes, network or kernels."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import compare_elaboration as comp
import convert_ab_trial as converter


MODULE = "Project.File0"
SOURCE = "Project/File0.lean"
BASELINE, CANDIDATE = "a" * 40, "b" * 40


def fixture():
    prov = {key: "same" for key in comp.MATCH_KEYS}
    prov.update({"commit": BASELINE, "compiler": "/pinned/bin/lean", "time_bin": "/usr/bin/time"})
    before = {"summary": {"provenance": dict(prov), "modules": {MODULE: SOURCE},
                          "source_hashes_before": {SOURCE: "a" * 64}}}
    after = copy.deepcopy(before)
    after["summary"]["provenance"]["commit"] = "c" * 40
    state = dict(prov)
    state.update({"baseline_sha": BASELINE, "modules": {MODULE: SOURCE}})
    rows = []
    for repetition in (1, 2, 3):
        for variant in ("baseline", "candidate"):
            before_variant = variant == "baseline"
            phases = {"elaboration": 4. if before_variant else 2., "import": 1.}
            cpu = 8. if before_variant else 5.
            record = {"phase": "profile", "module": MODULE, "source": SOURCE,
                      "source_sha256": ("a" if before_variant else "b") * 64,
                      "valid": True, "returncode": 0, "guard_errors": [], "artifact_changes": [],
                      "timing": {"wall_s": 10. if before_variant else 7., "cpu_s": cpu,
                                 "user_s": cpu - 1, "sys_s": 1., "percent_cpu": 80.,
                                 "max_rss_raw": 2048, "reported_exit_status": 0},
                      "profile": {"phases_s": phases, "events_over_100ms": []},
                      "command": ["/usr/bin/time", "-v", "-o", "/raw/time.txt", "/pinned/bin/lean", "--profile", SOURCE]}
            rows.append({"variant": variant, "module": MODULE, "repetition": repetition,
                         "sha": BASELINE if before_variant else CANDIDATE, "record": record})
    trial = {"valid": True, "baseline_sha": BASELINE, "same_host": "same", "helper_sha256": "d" * 64,
             "request": {"schema_version": 1, "mode": "profile", "sequence": 1,
                         "repetitions": 3, "baseline_sha": BASELINE, "candidate_sha": CANDIDATE,
                         "modules": [MODULE]}, "records": rows}
    refresh_comparison(trial)
    hashes = {"baseline": {SOURCE: "a" * 64}, "candidate": {SOURCE: "b" * 64}}
    review = {"schema_version": 1, "module": MODULE, "baseline_sha": BASELINE,
              "candidate_sha": CANDIDATE, "trial_result_sha256": "e" * 64,
              "decision": "kept", "relevant_phase": "elaboration", "intervention": "Measured proof closer",
              "rationale": "Reviewed all phases, CPU and proof statements; no transferred regression observed.",
              "statements_changed": False, "other_phases_regressed": False}
    return trial, state, before, after, hashes, review


def refresh_comparison(trial):
    computed = converter.metrics(trial["records"], trial["request"]["modules"])
    trial["comparison"] = {module: {"all_runs_valid": True, "metrics": value}
                           for module, value in computed.items()}


def convert(values, **kwargs):
    defaults = {"module": MODULE, "decision": "kept", "relevant_phase": "elaboration",
                "intervention": "Measured proof closer"}
    defaults.update(kwargs)
    return converter.canonical(*values, **defaults)


class TrialValidationTests(unittest.TestCase):
    def test_actual_schema_recomputes_six_runs_and_keeps_provenance(self):
        values = fixture()
        result = convert(values)
        self.assertEqual(len(result["before_runs"]), 3)
        self.assertEqual(len(result["after_runs"]), 3)
        self.assertEqual(result["criterion"]["saving_s"], 2)
        self.assertTrue(result["criterion"]["supports_retaining_edit"])
        self.assertEqual(result["after_runs"][0]["sha"], CANDIDATE)
        self.assertEqual(result["raw_trial"], values[0])
        self.assertIn("Explicit supplied review", result["review_flag_basis"])

    def test_invalid_wrong_variant_source_host_and_hash_are_rejected(self):
        mutations = [lambda v: v[0].update({"valid": False}),
                     lambda v: v[0]["records"][1].update({"sha": BASELINE}),
                     lambda v: v[0]["records"][1]["record"].update({"source_sha256": "f" * 64}),
                     lambda v: v[0].update({"same_host": "other-host"}),
                     lambda v: v[1].update({"compiler_sha256": "other-hash"}),
                     lambda v: v[0]["records"][0]["record"].update({"guard_errors": ["mutation"]})]
        for mutation in mutations:
            values = fixture()
            mutation(values)
            with self.assertRaises(ValueError):
                convert(values)

    def test_exact_three_runs_and_gnu_totals_are_required(self):
        for mutation in (lambda v: v[0]["records"].pop(),
                         lambda v: v[0]["records"][0]["record"]["timing"].update({"cpu_s": 9}),
                         lambda v: v[0]["records"][0]["record"]["timing"].update({"reported_exit_status": 1}),
                         lambda v: v[0]["records"][0]["record"].update({"command": []})):
            values = fixture()
            mutation(values)
            with self.assertRaises(ValueError):
                convert(values)

    def test_helper_summary_median_tampering_is_rejected(self):
        values = fixture()
        values[0]["comparison"][MODULE]["metrics"]["elaboration"]["candidate"]["median"] = 1
        with self.assertRaisesRegex(ValueError, "numeric disagreement"):
            convert(values)

    def test_missing_phase_is_not_substituted_with_zero(self):
        values = fixture()
        values[0]["records"][1]["record"]["profile"]["phases_s"].pop("elaboration")
        refresh_comparison(values[0])
        with self.assertRaisesRegex(ValueError, "unreported"):
            convert(values)


class ReviewAndDecisionTests(unittest.TestCase):
    def test_explicit_review_flags_and_rationale_are_required(self):
        for key in ("statements_changed", "other_phases_regressed", "rationale"):
            values = fixture()
            values[-1].pop(key)
            with self.assertRaises(ValueError):
                convert(values)

    def test_decision_is_not_inferred_from_improvement(self):
        values = fixture()
        values[-1]["decision"] = "reverted"
        result = convert(values, decision="reverted")
        self.assertFalse(result["kept"])
        self.assertTrue(result["criterion"]["meets_2s_or_10percent_threshold"])

    def test_kept_null_or_reviewed_regression_is_rejected(self):
        values = fixture()
        for row in values[0]["records"]:
            if row["variant"] == "candidate":
                row["record"]["profile"]["phases_s"]["elaboration"] = 3.9
        refresh_comparison(values[0])
        with self.assertRaisesRegex(ValueError, "Kept decision"):
            convert(values)
        values = fixture()
        values[-1]["other_phases_regressed"] = True
        with self.assertRaisesRegex(ValueError, "Kept decision"):
            convert(values)

    def test_wall_basis_uses_all_three_runs_and_manual_decision(self):
        values = fixture()
        values[-1]["relevant_phase"] = "wall_s"
        result = convert(values, basis="wall", relevant_phase="wall_s")
        self.assertEqual(result["criterion"]["saving_s"], 3)
        self.assertTrue(result["criterion"]["has_required_repetitions"])


class FailedInterventionTests(unittest.TestCase):
    def fixture(self):
        values = fixture()
        trial, _state, _before, _after, _hashes, review = values
        trial["valid"] = False
        for row in trial["records"]:
            if row["variant"] == "candidate":
                record = row["record"]
                record.update({"valid": False, "returncode": 1,
                               "diagnostics": {"error_count": 2,
                                               "errors": ["deterministic timeout at whnf; maximum heartbeats 1000000", "tactic execution timeout"]}})
                record["timing"].update({"wall_s": 150., "cpu_s": 148., "user_s": 147., "reported_exit_status": 1})
        refresh_comparison(trial)
        trial["comparison"][MODULE]["all_runs_valid"] = False
        review.update({"decision": "reverted", "other_phases_regressed": None,
                       "failure_reason": "All three candidate elaborations hit deterministic heartbeat timeouts."})
        return values

    def test_explicit_reverted_failure_allowed_with_no_performance_medians(self):
        result = convert(self.fixture(), decision="reverted", failed_intervention=True)
        self.assertEqual(result["status"], "failed_intervention")
        self.assertIsNone(result["all_trial_metrics"])
        self.assertTrue(result["performance_comparison_excluded"])
        self.assertIsNone(result["criterion"]["after_median_s"])
        self.assertIsNone(result["criterion"]["saving_s"])
        self.assertFalse(result["criterion"]["supports_retaining_edit"])
        self.assertEqual([x["record"]["timing"]["wall_s"] for x in result["diagnostic_failed_attempts"]], [150., 150., 150.])
        self.assertTrue(result["baseline_control_metrics"][MODULE]["cpu_s"]["median"] > 0)

    def test_failed_candidate_cannot_be_kept_or_silently_treated_as_null(self):
        values = self.fixture()
        values[-1]["decision"] = "kept"
        with self.assertRaisesRegex(ValueError, "cannot be kept"):
            convert(values, decision="kept", failed_intervention=True)
        with self.assertRaisesRegex(ValueError, "Helper trial is invalid"):
            convert(self.fixture(), decision="reverted")

    def test_source_artifact_guard_failure_is_not_ordinary_compiler_failure(self):
        values = self.fixture()
        values[0]["records"][1]["record"]["guard_errors"] = ["source mutated"]
        with self.assertRaisesRegex(ValueError, "not an ordinary failed intervention"):
            convert(values, decision="reverted", failed_intervention=True)

    def test_comparative_assessment_rejects_tampered_retention_and_excludes_partial_phase(self):
        result = convert(self.fixture(), decision="reverted", failed_intervention=True)
        assessment = comp.assess_ab(result)
        self.assertEqual(assessment["status"], "failed_intervention")
        self.assertEqual(assessment["after_runs"], [150., 150., 150.])
        self.assertIsNone(assessment["saving_percent"])
        result["kept"] = True
        with self.assertRaisesRegex(ValueError, "cannot be retained"):
            comp.assess_ab(result)


class RawEvidenceTests(unittest.TestCase):
    def test_adjacent_raw_records_are_bound_and_tampering_rejected(self):
        trial = fixture()[0]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.json"
            path.write_text(json.dumps(trial))
            row = trial["records"][0]
            leaf = path.parent / "run-1-baseline/Project_File0"
            leaf.mkdir(parents=True)
            (leaf / "result.json").write_text(json.dumps(row["record"]))
            raw = copy.deepcopy({key: value for key, value in row["record"].items() if key != "valid"})
            raw_path = leaf / "measurements.jsonl"
            raw_path.write_text(json.dumps(raw) + "\n")
            self.assertEqual(len(converter.bind_raw_trial(path, trial)), 3)
            raw["timing"]["wall_s"] = 20
            raw_path.write_text(json.dumps(raw) + "\n")
            with self.assertRaisesRegex(ValueError, "measurement disagrees"):
                converter.bind_raw_trial(path, trial)

    def test_gnu_elapsed_parser_and_signal_rejection(self):
        self.assertEqual(converter.elapsed("1:02:03.50"), 3723.5)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "time.txt"
            path.write_text("Command terminated by signal 9\n")
            with self.assertRaisesRegex(ValueError, "signal"):
                converter.raw_gnu_time(path)


if __name__ == "__main__":
    unittest.main()
