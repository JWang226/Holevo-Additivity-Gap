#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Read a fixed-helper trial and explicit review; emit canonical A/B evidence.

No Lean, Lake, checker, build, or network operation is invoked. The converter
validates source/tool/host bindings and recomputes timing metrics. Statement and
non-regression flags come only from the explicit review, never from timings or
the optional final-state API record.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys

import compare_elaboration as comp


VARIANTS = ("baseline", "candidate")
TIMING_KEYS = ("wall_s", "cpu_s", "user_s", "sys_s", "percent_cpu", "max_rss_raw")


def same_number(actual, expected, label):
    comp.require(type(actual) in (int, float) and abs(actual - expected) < 1e-7,
                 "Raw/summary numeric disagreement: " + label)


def metrics(records, modules):
    """Recompute all available metrics; absent phase categories stay missing."""
    output = {}
    for module in modules:
        grouped = {variant: [row["record"] for row in records if row["variant"] == variant
                            and row["module"] == module] for variant in VARIANTS}
        phases = sorted({phase for rows in grouped.values() for record in rows
                         for phase in record["profile"]["phases_s"]})
        result = {}
        for key in ("wall_s", "cpu_s", "user_s", "sys_s", *phases):
            values = {}
            for variant, rows in grouped.items():
                raw = [record["timing"].get(key) if key in TIMING_KEYS else
                       record["profile"]["phases_s"].get(key) for record in rows]
                reported = [value for value in raw if value is not None]
                values[variant] = {"runs": reported, "missing_runs": len(raw) - len(reported),
                                   "median": statistics.median(reported) if reported else None,
                                   "mean": statistics.mean(reported) if reported else None}
            b, a = values["baseline"]["median"], values["candidate"]["median"]
            values["median_delta_s"] = a - b if a is not None and b is not None else None
            values["median_change_percent"] = 100 * (a / b - 1) if b and a is not None else None
            result[key] = values
        output[module] = result
    return output


def validate_trial(trial, state, before, after, committed_hashes, *, allow_failed=False):
    """Pure evidence validation; hashes are supplied from verified Git blobs."""
    comp.require(trial.get("valid") is (False if allow_failed else True) and not trial.get("error"),
                 "Expected complete failed intervention" if allow_failed else "Helper trial is invalid")
    request = trial.get("request", {})
    comp.require(request.get("schema_version") == 1 and request.get("mode") == "profile"
                 and request.get("repetitions") == 3, "Expected completed three-repeat profile request")
    bprov, aprov = before["summary"]["provenance"], after["summary"]["provenance"]
    for key in comp.MATCH_KEYS:
        comp.require(bprov.get(key) == aprov.get(key), "Full-snapshot timing setup differs: " + key)
    for key in ("compiler_sha256", "time_sha256", "host", "compiler", "time_bin"):
        comp.require(state.get(key) == bprov.get(key), "Continuation state differs from baseline: " + key)
    baseline, candidate = request.get("baseline_sha"), request.get("candidate_sha")
    comp.require(baseline == bprov.get("commit") == state.get("baseline_sha") == trial.get("baseline_sha"),
                 "Trial baseline SHA differs from measured baseline")
    comp.require(all(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{40}", sha)
                     for sha in (baseline, candidate)), "Expected full variant commit SHAs")
    comp.require(candidate != baseline, "Candidate and baseline commits are identical")
    comp.require(trial.get("same_host") == bprov.get("host"), "Trial ran on a different host")
    modules = request.get("modules")
    comp.require(isinstance(modules, list) and 1 <= len(modules) <= 10
                 and all(isinstance(x, str) for x in modules) and len(modules) == len(set(modules)),
                 "Invalid trial module inventory")
    comp.require(state.get("modules") == before["summary"]["modules"] == after["summary"]["modules"],
                 "Continuation module scope differs from full snapshots")
    comp.require(set(modules) <= state["modules"].keys(), "Trial contains an unexpected module")
    records, seen = trial.get("records"), set()
    comp.require(isinstance(records, list), "Trial has no structured records")
    for row in records:
        variant, module, repetition = row.get("variant"), row.get("module"), row.get("repetition")
        comp.require(variant in VARIANTS and module in modules and type(repetition) is int
                     and repetition in (1, 2, 3), "Unexpected trial variant/module/repetition")
        key = (module, variant, repetition)
        comp.require(key not in seen, "Duplicate trial run: " + str(key))
        seen.add(key)
        sha = baseline if variant == "baseline" else candidate
        comp.require(row.get("sha") == sha, "Wrong exact SHA for trial variant")
        record = row.get("record", {})
        failed_candidate = allow_failed and variant == "candidate"
        if failed_candidate:
            comp.require(record.get("valid") is False and type(record.get("returncode")) is int
                         and record["returncode"] != 0 and record.get("diagnostics", {}).get("error_count", 0) > 0,
                         "Failed-intervention mode requires all three candidate elaborations to fail with diagnostic errors")
        else:
            comp.require(record.get("valid") is True and record.get("returncode") == 0,
                         "Failed profile in valid baseline/candidate scope")
        comp.require(record.get("guard_errors") == [] and record.get("artifact_changes") == [],
                     "Observed artifact/source mutation is not an ordinary failed intervention")
        source = state["modules"][module]
        comp.require(record.get("module") == module and record.get("phase") == "profile"
                     and record.get("source") == source, "Wrong trial profile source/phase")
        expected = committed_hashes[variant][source]
        comp.require(record.get("source_sha256") == expected,
                     "Trial source SHA differs from committed variant: " + module + " " + variant)
        if variant == "baseline":
            comp.require(expected == before["summary"]["source_hashes_before"].get(source),
                         "Trial baseline source differs from full baseline")
        timing = record.get("timing", {})
        for key in TIMING_KEYS:
            comp.number(timing.get(key), "Trial timing " + key)
        comp.require(type(timing.get("reported_exit_status")) is int
                     and (timing["reported_exit_status"] != 0 if failed_candidate
                          else timing["reported_exit_status"] == 0),
                     "GNU time exit disagrees with valid/failed profile classification")
        same_number(timing["cpu_s"], timing["user_s"] + timing["sys_s"], "trial CPU")
        phases = record.get("profile", {}).get("phases_s")
        comp.require(isinstance(phases, dict) and bool(phases), "Trial cumulative phases are missing")
        for phase, value in phases.items():
            comp.number(value, "Trial phase " + phase)
        command = record.get("command")
        comp.require(isinstance(command, list) and bool(command) and all(isinstance(x, str) for x in command)
                     and command[0] == state["time_bin"] and state["compiler"] in command
                     and "--profile" in command and "-v" in command,
                     "Trial GNU-time/compiler profile command differs")
        compiler_index = command.index(state["compiler"])
        compiler_args = command[compiler_index + 1:]
        comp.require(not any(arg in {"-o", "-i", "-c", "-b"}
                              or arg.startswith(("--o=", "--i=", "--c=", "--bc="))
                              for arg in compiler_args), "Trial compiler command writes artifacts")
        comp.require([arg for arg in compiler_args if arg.endswith(".lean")] == [source],
                     "Trial command source differs from structured source")
    expected_runs = {(module, variant, repetition) for module in modules for variant in VARIANTS
                     for repetition in (1, 2, 3)}
    comp.require(seen == expected_runs, "Need exactly three runs of each variant for every requested module")
    recalculated = metrics(records, modules)
    helper_comparison = trial.get("comparison", {})
    comp.require(set(helper_comparison) == set(modules), "Helper comparison inventory differs")
    for module in modules:
        comp.require(helper_comparison[module].get("all_runs_valid") is (not allow_failed),
                     "Helper validity summary disagrees with trial classification")
        reported = helper_comparison[module].get("metrics", {})
        comp.require(set(reported) == set(recalculated[module]), "Helper metric categories differ from raw records")
        for metric, result in recalculated[module].items():
            for variant in VARIANTS:
                comp.require(reported[metric][variant].get("runs") == result[variant]["runs"],
                             "Helper metric run list differs from raw records")
                expected_median = result[variant]["median"]
                actual_median = reported[metric][variant].get("median")
                if expected_median is None:
                    comp.require(actual_median is None, "Helper invented a missing median")
                else:
                    same_number(actual_median, expected_median, module + " " + metric)
    return recalculated


def canonical(trial, state, before, after, committed_hashes, review, *, module,
              decision, relevant_phase, intervention, basis="phase", failed_intervention=False):
    comp.require(not failed_intervention or decision == "reverted", "A failed intervention cannot be kept")
    all_metrics = validate_trial(trial, state, before, after, committed_hashes, allow_failed=failed_intervention)
    request = trial["request"]
    comp.require(module in request["modules"], "Selected module is not in the trial")
    comp.require(review.get("schema_version") == 1 and review.get("module") == module
                 and review.get("baseline_sha") == request["baseline_sha"]
                 and review.get("candidate_sha") == request["candidate_sha"],
                 "Review is not bound to this module and variant pair")
    comp.require(review.get("decision") == decision and decision in {"kept", "reverted"},
                 "Explicit decision and reviewed decision disagree")
    comp.require(review.get("relevant_phase") == relevant_phase and review.get("intervention") == intervention,
                 "Review phase/intervention differs from explicit CLI decision")
    comp.require(isinstance(review.get("rationale"), str) and bool(review["rationale"].strip()),
                 "A reviewed decision rationale is required")
    for flag in ("statements_changed", "other_phases_regressed"):
        comp.require(flag in review and (type(review[flag]) is bool or failed_intervention and review[flag] is None),
                     "Explicit reviewed Boolean required (null allowed for unassessed failed intervention): " + flag)
    if failed_intervention:
        comp.require(isinstance(review.get("failure_reason"), str) and bool(review["failure_reason"].strip()),
                     "An explicit reviewed failure reason is required")
    comp.require(basis in {"phase", "wall"}, "Basis must be phase or wall")
    comp.require(basis != "wall" or relevant_phase == "wall_s", "Wall basis requires relevant-phase wall_s")
    output = {"schema_version": 1, "status": "failed_intervention" if failed_intervention else "completed", "module": module,
              "intervention": intervention, "basis": basis,
              "relevant_phase": relevant_phase if basis == "phase" else None,
              "matched_setup": True, "statements_changed": review["statements_changed"],
              "other_phases_regressed": review["other_phases_regressed"], "kept": decision == "kept",
              "decision": decision, "review": copy.deepcopy(review),
              "review_flag_basis": "Explicit supplied review; not inferred from timings or the final-state API record",
              "all_trial_metrics": None if failed_intervention else all_metrics, "raw_trial": copy.deepcopy(trial),
              "variant_source_sha256": copy.deepcopy(committed_hashes),
              "runner_provenance": {key: state[key] for key in
                                    ("baseline_sha", "host", "compiler_sha256", "time_sha256", "compiler", "time_bin")},
              "artifact_guard_scope": "Passed fixed-helper result, frozen helper hash, bound baseline artifact/dependency state, and zero observed source/artifact guard failures. Guard calls are not independent kernel or type-preservation checks."}
    for variant, side in (("baseline", "before"), ("candidate", "after")):
        rows = sorted((row for row in trial["records"] if row["module"] == module and row["variant"] == variant),
                      key=lambda row: row["repetition"])
        runs = []
        for row in rows:
            record = row["record"]
            comp.require(failed_intervention or basis != "phase" or relevant_phase in record["profile"]["phases_s"],
                         "Relevant phase is unreported in a run; do not substitute zero")
            runs.append({"wall_s": record["timing"]["wall_s"],
                         "phases_s": dict(record["profile"]["phases_s"]),
                         "timing": dict(record["timing"]), "variant": variant,
                         "sha": row["sha"], "repetition": row["repetition"],
                         "valid": record["valid"], "returncode": record["returncode"],
                         "command": record["command"], "source_sha256": record["source_sha256"],
                         "record": copy.deepcopy(record)})
        output[side + "_runs"] = runs
    if failed_intervention:
        output["failure_reason"] = review["failure_reason"]
        output["performance_comparison_excluded"] = True
        output["exclusion_reason"] = "All three candidate elaborations failed. Their elapsed/CPU/partial phase times measure aborted attempts, so candidate medians, savings and speed-regression/null classifications are excluded."
        output["baseline_control_metrics"] = {name: {metric: item["baseline"] for metric, item in values.items()}
                                               for name, values in all_metrics.items()}
        output["diagnostic_failed_attempts"] = [{"sha": row["sha"], "module": row["module"],
                                                "repetition": row["repetition"], "record": copy.deepcopy(row["record"])}
                                               for row in trial["records"] if row["variant"] == "candidate"]
        output["raw_helper_aggregate_caveat"] = "Helper aggregates over aborted candidates are retained only inside raw_trial as historical diagnostic output, not valid performance comparisons."
    assessment = comp.assess_ab(output)
    comp.require(decision != "kept" or assessment["supports_retaining_edit"],
                 "Kept decision does not meet measured threshold/repetition/non-regression/statement requirements")
    output["criterion"] = {key: value for key, value in assessment.items() if key not in {"evidence", "caveat"}}
    return output


def elapsed(value):
    total = 0.
    for part in value.split(":"):
        total = total * 60 + float(part)
    return total


def raw_gnu_time(path):
    labels = {"User time (seconds)": "user_s", "System time (seconds)": "sys_s",
              "Percent of CPU this job got": "percent_cpu",
              "Elapsed (wall clock) time (h:mm:ss or m:ss)": "wall_s",
              "Maximum resident set size (kbytes)": "max_rss_raw", "Exit status": "reported_exit_status"}
    result = {}
    for line in path.read_text().splitlines():
        stripped = line.strip()
        comp.require(not stripped.startswith("Command terminated by signal"), "Adjacent GNU time log reports a signal")
        for label, key in labels.items():
            if stripped.startswith(label + ":"):
                value = stripped[len(label) + 1:].strip()
                result[key] = elapsed(value) if key == "wall_s" else float(value.removesuffix("%"))
    comp.require(set(result) == set(labels.values()), "Incomplete adjacent GNU time log")
    return result


def bind_raw_trial(path, trial):
    bindings = {str(path.resolve()): comp.file_hash(path)}
    for row in trial["records"]:
        record = row["record"]
        leaf = path.parent / ("run-" + str(row["repetition"]) + "-" + row["variant"]) / row["module"].replace(".", "_")
        result_path, measurements_path = leaf / "result.json", leaf / "measurements.jsonl"
        if result_path.is_file():
            comp.require(comp.load(result_path) == record, "Adjacent trial result disagrees with summary")
            bindings[str(result_path.resolve())] = comp.file_hash(result_path)
        if measurements_path.is_file():
            records = [json.loads(line, object_pairs_hook=comp.unique_object)
                       for line in measurements_path.read_text().splitlines() if line.strip()]
            comp.require(len(records) == 1 and comp.comparable_profile(records[0]) == comp.comparable_profile(record)
                         and records[0].get("command") == record.get("command"),
                         "Adjacent trial measurement disagrees with summary")
            bindings[str(measurements_path.resolve())] = comp.file_hash(measurements_path)
        paths = [leaf / "wrapper-config.json", leaf / "driver.log"]
        config_path = leaf / "wrapper-config.json"
        if config_path.is_file():
            config = comp.load(config_path)
            comp.require(config.get("phase") == "profile" and config.get("source_hashes", {}).get(record["source"])
                         == record["source_sha256"], "Adjacent wrapper configuration source/phase differs")
        for field, directory in (("log", "logs"), ("time_log", "timings")):
            if isinstance(record.get(field), str):
                raw = leaf / directory / Path(record[field]).name
                if raw.is_file() and field == "time_log":
                    for key, value in raw_gnu_time(raw).items():
                        same_number(record["timing"][key], value, "adjacent GNU time " + key)
                paths.append(raw)
        for raw in paths:
            if raw.is_file():
                bindings[str(raw.resolve())] = comp.file_hash(raw)
    return bindings


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--trial", type=Path, required=True, help="trials/N/result.json")
    parser.add_argument("--state", type=Path, required=True, help="continuation-initial.json")
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--review", type=Path, required=True, help="Explicit manual review; schema in README")
    parser.add_argument("--module", required=True)
    parser.add_argument("--decision", choices=("kept", "reverted"), required=True)
    parser.add_argument("--relevant-phase", required=True)
    parser.add_argument("--intervention", required=True)
    parser.add_argument("--basis", choices=("phase", "wall"), default="phase")
    parser.add_argument("--failed-intervention", action="store_true",
                        help="Explicit reverted mode: three valid baselines and three failed candidate elaborations; excludes candidate medians")
    parser.add_argument("--helper", type=Path, help="Frozen executed helper; default repo/scripts/elaboration_continue.py")
    parser.add_argument("--api-check", type=Path, help="Optional observed, source-bound final-state API comparison")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        trial, state, review = comp.load(args.trial), comp.load(args.state), comp.load(args.review)
        before, after = comp.read_snapshot(args.before, None), comp.read_snapshot(args.after, None)
        repo = args.repo.resolve()
        helper = args.helper or repo / "scripts/elaboration_continue.py"
        comp.require(comp.file_hash(helper) == trial.get("helper_sha256"), "Frozen executed helper hash differs")
        comp.require(review.get("trial_result_sha256") == comp.file_hash(args.trial), "Review does not bind this raw trial result")
        comp.require(state.get("dependency_artifacts") == before["dependencies"]["artifacts"],
                     "Initial continuation dependency guard state differs from baseline")
        artifact_path = args.before.resolve().parent / "artifacts-after.json"
        comp.require(artifact_path.is_file() and state.get("own_artifacts") == comp.load(artifact_path),
                     "Initial continuation own-artifact guard state differs from completed baseline")
        modules = trial["request"]["modules"]
        paths = [state["modules"][module] for module in modules]
        hashes = {}
        for variant, field in (("baseline", "baseline_sha"), ("candidate", "candidate_sha")):
            blobs = comp.git_blobs(repo, trial["request"][field], paths)
            hashes[variant] = {name: hashlib.sha256(text.encode()).hexdigest() for name, text in blobs.items()}
        data = canonical(trial, state, before, after, hashes, review, module=args.module,
                         decision=args.decision, relevant_phase=args.relevant_phase,
                         intervention=args.intervention, basis=args.basis, failed_intervention=args.failed_intervention)
        bindings = {**before["input_sha256"], **after["input_sha256"], **bind_raw_trial(args.trial, trial)}
        for path in (args.state, args.review, helper, artifact_path):
            bindings[str(path.resolve())] = comp.file_hash(path)
        data["final_state_api_context"] = None
        if args.api_check:
            api_record = comp.load(args.api_check)
            data["final_state_api_context"] = comp.check_api(api_record, after, None, repo)
            data["final_state_api_context"]["candidate_limitation"] = "This record compares the final measured sources; it is not an independent statement check at the intermediate candidate commit. Review flags remain explicit manual findings."
            bindings[str(args.api_check.resolve())] = comp.file_hash(args.api_check)
            export = repo / comp.relative(api_record["after_export_path"])
            bindings[str(export.resolve())] = comp.file_hash(export)
        data["input_sha256"] = bindings
        data["invocation"] = [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]]
        for name, expected in bindings.items():
            comp.require(comp.file_hash(Path(name)) == expected, "Evidence changed while converting: " + name)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        print(args.output)
        return 0
    except (KeyError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("A/B conversion rejected: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
