#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Join two valid elaboration snapshots without running Lean or modifying sources.

Only the supplied evidence and committed Git blobs are read. Output is original
Markdown and JSON; a missing profile or missing API/A-B evidence is never a pass.
See README.md beside this script for the evidence schema and reproduction CLI.
"""
from __future__ import annotations

import argparse
import copy
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import shlex
import statistics
import subprocess
import sys
from typing import Any


MATCH_KEYS = ("compiler_sha256", "time_sha256", "cores", "host",
              "driver_parallelism", "lean_internal_threads")
TACTICS = ("nlinarith", "linarith", "simp", "simpa", "congr", "norm_num",
           "positivity", "omega", "aesop")
OVERRIDES = ("maxHeartbeats", "synthInstance.maxHeartbeats", "maxRecDepth")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique_object(pairs: list[tuple[str, Any]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def load(path: Path) -> Any:
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(value: Any, label: str) -> float:
    require(type(value) in (int, float) and value >= 0,
            "Expected nonnegative finite number: " + label)
    result = float(value)
    require(result < float("inf"), "Non-finite number: " + label)
    return result


def delta(before: float, after: float) -> dict:
    return {"before": before, "after": after, "delta": after - before,
            "percent": 100 * (after - before) / before if before else None}


def relative(name: str) -> str:
    require(isinstance(name, str) and name and "\\" not in name and ":" not in name,
            "Invalid source path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and all(p not in {"", ".", ".."}
            for p in name.split("/")), "Unsafe source path: " + name)
    return name


def masked_code(text: str) -> str:
    """Mask comments and strings, retaining positions for a lexical census."""
    output = list(text)
    index, depth, line, string = 0, 0, False, False
    while index < len(text):
        char, pair = text[index], text[index:index + 2]
        if char == "\n":
            line = False
            index += 1
        elif line:
            output[index] = " "
            index += 1
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                output[index:index + 2] = "  "
                index += 2
            else:
                output[index] = " "
                index += 1
        elif string:
            output[index] = " "
            if char == "\\" and index + 1 < len(text):
                output[index + 1] = " "
                index += 2
            else:
                string = char != '"'
                index += 1
        elif pair in ("--", "/-"):
            line, depth = pair == "--", int(pair == "/-")
            output[index:index + 2] = "  "
            index += 2
        elif text.startswith(("'\"'", "'\\\"'"), index):
            index += 3 if text[index + 1] == '"' else 4
        else:
            if char == '"':
                string = True
                output[index] = " "
            index += 1
    return "".join(output)


def git_blobs(repo: Path, commit: str, names: list[str]) -> dict[str, str]:
    require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None, "Use full Git commit SHA")
    resolved = subprocess.check_output(["git", "rev-parse", commit + "^{commit}"],
                                       cwd=repo, text=True).strip()
    require(resolved == commit, "Commit did not resolve exactly")
    specs = [commit + ":" + relative(name) for name in names]
    process = subprocess.run(["git", "cat-file", "--batch"], cwd=repo, check=True,
                             input="".join(spec + "\n" for spec in specs).encode(),
                             stdout=subprocess.PIPE)
    data, cursor, result = process.stdout, 0, {}
    for name in names:
        end = data.index(b"\n", cursor)
        header = data[cursor:end].split()
        require(len(header) == 3 and header[1] == b"blob", "Missing committed blob: " + name)
        size = int(header[2])
        result[name] = data[end + 1:end + 1 + size].decode("utf-8")
        cursor = end + 2 + size
    return result


def source_census(summary: dict, texts: dict[str, str]) -> dict:
    sizes = summary["size"]["git_build_scope"]["per_file"]
    require(set(texts) == set(sizes), "Source census scope differs from committed snapshot")
    overrides, tactic_counts = [], Counter()
    for name, text in sorted(texts.items()):
        expected = summary["source_hashes_before"].get(name)
        require(hashlib.sha256(text.encode()).hexdigest() == expected,
                "Git source does not match measured content: " + name)
        code = masked_code(text)
        for tactic in TACTICS:
            tactic_counts[tactic] += len(re.findall(r"\b" + tactic + r"\b", code))
        for match in re.finditer(r"\bset_option\s+(" + "|".join(re.escape(x) for x in OVERRIDES)
                                 + r")\s+([^\s]+)", code):
            overrides.append({"file": name, "line": code.count("\n", 0, match.start()) + 1,
                              "option": match.group(1), "value_token": match.group(2)})
    ordered = sorted(({"file": name, **item} for name, item in sizes.items()),
                     key=lambda item: item["total_lines"], reverse=True)
    return {"source_commit": summary["provenance"]["commit"],
            "largest_files": ordered[:30], "maximum_physical_lines": ordered[0]["total_lines"] if ordered else 0,
            "files_over_1000_lines": [x["file"] for x in ordered if x["total_lines"] > 1000],
            "files_over_1500_lines": [x["file"] for x in ordered if x["total_lines"] > 1500],
            "legacy_nonmodule_count": sum(not x["module_header"] for x in ordered),
            "tactic_token_counts": dict(tactic_counts), "overrides": overrides,
            "override_counts": dict(Counter(item["option"] for item in overrides)),
            "caveat": "Lexical tactic tokens and set_option occurrences, excluding comments/strings; not executed tactic counts or option lifetime analysis."}


def evidence_path(summary_path: Path, recorded: str, name: str) -> Path:
    local = summary_path.parent / name
    if local.is_file():
        return local.resolve()
    original = Path(recorded)
    require(original.is_file(), "Missing evidence file beside summary: " + name)
    return original.resolve()


def read_snapshot(path: Path, measurements_path: Path | None) -> dict:
    path = path.resolve()
    summary = load(path)
    require(summary.get("valid") is True and not summary.get("invalid_reasons"),
            "Snapshot is invalid: " + str(path))
    require(summary.get("coverage", {}).get("complete") is True
            and summary.get("build", {}).get("returncode") == 0,
            "Incomplete/failed own build: " + str(path))
    provenance = summary["provenance"]
    require("GNU" in provenance.get("time_version", ""), "Timing tool is not identified as GNU time")
    for key in MATCH_KEYS:
        require(key in provenance and provenance[key] is not None, "Missing timing provenance: " + key)
    records_path = (measurements_path or path.parent / "measurements.jsonl").resolve()
    records = [json.loads(line, object_pairs_hook=unique_object)
               for line in records_path.read_text().splitlines() if line.strip()]
    builds = [record for record in records if record["phase"] == "build"]
    indexed = {}
    for record in builds:
        name = record["module"]
        require(name not in indexed, "Duplicate module measurement: " + name)
        require(record["returncode"] == 0 and not record.get("guard_errors"), "Failed/unguarded build: " + name)
        require(summary["modules"].get(name) == record["source"], "Unexpected measured source: " + name)
        require(summary["source_hashes_before"][record["source"]] == record["source_sha256"],
                "Module timing source binding differs: " + name)
        timing = record["timing"]
        for key in ("wall_s", "user_s", "sys_s"):
            number(timing[key], name + " " + key)
        require(abs(timing["cpu_s"] - timing["user_s"] - timing["sys_s"]) < 1e-7,
                "Module CPU total is not user + system: " + name)
        indexed[name] = record
    require(set(indexed) == set(summary["modules"]) and len(builds) == summary["coverage"]["measured"],
            "Measurement inventory differs from complete summary")
    profiles = {}
    for record in (x for x in records if x["phase"] == "profile"):
        name = record["module"]
        require(name not in profiles, "Duplicate warm module profile: " + name)
        require(record["returncode"] == 0 and not record.get("guard_errors"), "Failed warm profile: " + name)
        require(summary["modules"].get(name) == record["source"]
                and summary["source_hashes_before"].get(record["source"]) == record["source_sha256"],
                "Warm profile source binding differs: " + name)
        require(bool(record["profile"]["phases_s"]), "Missing cumulative phase totals: " + name)
        for category, value in record["profile"]["phases_s"].items():
            number(value, name + " " + category)
        profiles[name] = record
    require(list(profiles.values()) == summary.get("profiles"), "Warm profile records differ from valid summary")
    require(not summary.get("source_changes") and not summary.get("dependency_artifact_changes"),
            "Snapshot reports mutated sources/dependency inputs")
    hashes = {str(path): file_hash(path), str(records_path): file_hash(records_path)}
    dependencies = []
    for stage in ("before", "after"):
        name = "dependencies-" + stage + ".json"
        dep_path = evidence_path(path, summary["dependency_manifests"][stage], name)
        dep = load(dep_path)
        require(dep["olean_count"] == summary["dependency_olean_count"], "Dependency artifact count differs")
        dependencies.append(dep)
        hashes[str(dep_path)] = file_hash(dep_path)
    require(dependencies[0]["artifacts"] == dependencies[1]["artifacts"],
            "Cached dependency artifacts changed during valid snapshot")
    return {"summary": summary, "builds": indexed,
            "profiles": profiles,
            "dependencies": dependencies[0], "input_sha256": hashes,
            "paths": {"summary": str(path), "measurements": str(records_path)}}


def family(name: str) -> str:
    parts = name.split(".")
    match = re.match(r"[A-Z][a-z0-9]*", parts[-1])
    return parts[0] + "." + match.group() if len(parts) > 1 and match else parts[0]


def compare_builds(before: dict, after: dict) -> dict:
    old, new = before["summary"], after["summary"]
    mismatch = [key for key in MATCH_KEYS if old["provenance"][key] != new["provenance"][key]]
    require(not mismatch, "Timing setup differs; no matched comparison: " + ", ".join(mismatch))
    require(set(before["builds"]) == set(after["builds"]), "Module inventories differ; cannot attribute cleanup to matched scope")
    rows = []
    families = {}
    for name in before["builds"]:
        b, a = before["builds"][name], after["builds"][name]
        row = {"module": name, "source": a["source"],
               "source_changed": b["source_sha256"] != a["source_sha256"]}
        for key in ("wall_s", "cpu_s", "user_s", "sys_s", "max_rss_raw"):
            row[key] = delta(b["timing"][key], a["timing"][key])
        rows.append(row)
        group = families.setdefault(family(name), {"files": 0, "before_cpu_s": 0., "after_cpu_s": 0.,
                                                    "before_wall_s": 0., "after_wall_s": 0.})
        group["files"] += 1
        for side, record in (("before", b), ("after", a)):
            for key in ("cpu_s", "wall_s"):
                group[side + "_" + key] += record["timing"][key]
    rows.sort(key=lambda item: item["wall_s"]["after"], reverse=True)
    sums = {}
    for side, snapshot in (("before", before), ("after", after)):
        records = list(snapshot["builds"].values())
        sums[side] = {key: sum(x["timing"][key] for x in records)
                      for key in ("wall_s", "cpu_s", "user_s", "sys_s")}
        wall = number(snapshot["summary"]["build"]["timing"]["wall_s"], "build wall")
        require(wall > 0, "Full build wall time must be positive")
        sums[side]["observed_cpu_parallelism"] = sums[side]["cpu_s"] / wall
    old_code = old["size"]["git_build_scope"]["code_lines"]
    new_code = new["size"]["git_build_scope"]["code_lines"]
    per_line = sums["before"]["cpu_s"] / old_code if old_code else None
    predicted = (new_code - old_code) * per_line if per_line is not None else None
    actual = sums["after"]["cpu_s"] - sums["before"]["cpu_s"]
    opposite = [x["module"] for x in rows if x["wall_s"]["percent"] is not None
                and x["cpu_s"]["percent"] is not None
                and abs(x["wall_s"]["percent"]) >= 10 and abs(x["cpu_s"]["percent"]) >= 10
                and x["wall_s"]["delta"] * x["cpu_s"]["delta"] < 0]
    parallel = delta(sums["before"]["observed_cpu_parallelism"], sums["after"]["observed_cpu_parallelism"])
    signals = {
        "outer_user_cpu_down_while_summed_module_wall_up": new["build"]["timing"]["user_s"] < old["build"]["timing"]["user_s"] and sums["after"]["wall_s"] > sums["before"]["wall_s"],
        "observed_cpu_parallelism_increased_over_10_percent": bool(parallel["percent"] is not None and parallel["percent"] > 10),
        "matched_modules_with_opposite_wall_cpu_changes_over_10_percent": bool(opposite)}
    return {"matched_timing_setup": True, "matched_keys": list(MATCH_KEYS),
            "per_module": rows, "top_30_after": rows[:30], "families": families, "sums": sums,
            "heavy_tail": {str(t): {side: sum(x["timing"]["wall_s"] >= t for x in snapshot["builds"].values())
                                   for side, snapshot in (("before", before), ("after", after))}
                           for t in (10, 20, 30, 40)},
            "size_prediction": {"before_code_lines": old_code, "after_code_lines": new_code,
                                "delta_code_lines": new_code - old_code,
                                "baseline_cpu_ms_per_code_line": per_line * 1000 if per_line is not None else None,
                                "predicted_cpu_delta_s": predicted, "actual_cpu_delta_s": actual,
                                "absolute_actual_predicted_ratio": abs(actual / predicted) if predicted else None},
            "contention": {"heuristic_signals": signals, "opposite_direction_modules": opposite,
                           "multiple_signals": sum(signals.values()) >= 2,
                           "limitation": "Conservative screening heuristics adapted to actual GNU CPU and module wall measurements. Signals do not prove contention; their absence does not prove a quiet machine. Process invisibility is not a zero-load observation."}}


def comparable_profile(record: dict) -> dict:
    """Semantic measurement fields; raw paths/commands remain separately bound."""
    fields = ("phase", "module", "source", "source_sha256", "returncode", "timing",
              "profile", "guard_errors", "artifact_changes")
    return {field: record.get(field) for field in fields}


def supplemental_profiles(path: Path, before: dict, after: dict) -> dict:
    """Validate the fixed continuation helper's serial after-profile supplement.

    Do not edit either snapshot or rewrite its top-eight evidence. Supplementary
    measurements are a separately bound input to the profile comparison only.
    """
    path = path.resolve()
    data = load(path)
    require(data.get("valid") is True, "Supplemental profile summary is invalid")
    prov = after["summary"]["provenance"]
    require(data.get("after_sha") == prov["commit"], "Supplemental after SHA differs from measured after commit")
    for key in ("compiler_sha256", "time_sha256", "host"):
        require(data.get(key) == prov[key], "Supplemental timing provenance differs: " + key)
    require(set(data.get("baseline_top8_modules", [])) == set(before["profiles"]),
            "Supplemental baseline top8 inventory differs")
    require(set(data.get("after_top8_modules", [])) == set(after["profiles"]),
            "Supplemental after top8 inventory differs")
    requested = data.get("requested_modules")
    require(isinstance(requested, list) and all(isinstance(x, str) for x in requested)
            and len(requested) == len(set(requested)), "Invalid supplemental requested module inventory")
    records = data.get("profiles")
    require(isinstance(records, list), "Supplemental summary has no profile records")
    hashes = {str(path): file_hash(path)}
    indexed, duplicates, bound_raw = {}, [], []
    for record in records:
        require(isinstance(record, dict), "Invalid supplemental record")
        name = record.get("module")
        require(name in after["summary"]["modules"] and name not in indexed,
                "Unexpected or duplicate supplemental module: " + str(name))
        require(record.get("valid") is True and record.get("returncode") == 0
                and record.get("guard_errors") == [], "Failed/unguarded supplemental profile: " + name)
        require(record.get("phase") == "profile" and record.get("artifact_changes") == [],
                "Supplemental profile has wrong phase or wrote artifacts: " + name)
        source = after["summary"]["modules"][name]
        require(record.get("source") == source and record.get("source_sha256") ==
                after["summary"]["source_hashes_after"].get(source),
                "Supplemental source differs from measured after source: " + name)
        require(bool(record.get("profile", {}).get("phases_s")),
                "Supplemental cumulative phases are missing: " + name)
        for category, value in record["profile"]["phases_s"].items():
            number(value, "Supplemental " + name + " " + category)
        timing = record.get("timing", {})
        for key in ("wall_s", "user_s", "sys_s", "cpu_s"):
            number(timing.get(key), "Supplemental " + name + " " + key)
        require(abs(timing["cpu_s"] - timing["user_s"] - timing["sys_s"]) < 1e-7,
                "Supplemental CPU is not user + system: " + name)
        command = record.get("command")
        require(isinstance(command, list) and all(isinstance(arg, str) for arg in command)
                and "--profile" in command and "-v" in command,
                "Supplemental record has no GNU-time profile command: " + name)
        require(command[0] == prov["time_bin"] and prov["compiler"] in command,
                "Supplemental compiler/time command differs from full snapshot: " + name)
        compiler_index = command.index(prov["compiler"])
        require(not any(arg in {"-o", "-i", "-c", "-b"}
                        or arg.startswith(("--o=", "--i=", "--c=", "--bc="))
                        for arg in command[compiler_index + 1:]),
                "Supplemental compiler command writes artifacts: " + name)
        if name in after["profiles"]:
            require(comparable_profile(record) == comparable_profile(after["profiles"][name]),
                    "Supplemental duplicate disagrees with original after profile: " + name)
            duplicates.append(name)
        leaf = path.parent / name.replace(".", "_")
        raw_result = leaf / "result.json"
        if raw_result.is_file():
            require(load(raw_result) == record, "Adjacent supplemental raw result differs: " + name)
            hashes[str(raw_result.resolve())] = file_hash(raw_result)
            bound_raw.append(str(raw_result.resolve()))
        raw_records = leaf / "measurements.jsonl"
        if raw_records.is_file():
            raw = [json.loads(line, object_pairs_hook=unique_object) for line in raw_records.read_text().splitlines() if line.strip()]
            require(len(raw) == 1 and comparable_profile(raw[0]) == comparable_profile(record),
                    "Adjacent supplemental raw measurement differs: " + name)
            hashes[str(raw_records.resolve())] = file_hash(raw_records)
            bound_raw.append(str(raw_records.resolve()))
        candidates = [leaf / "wrapper-config.json", leaf / "driver.log"]
        for field, directory in (("log", "logs"), ("time_log", "timings")):
            if isinstance(record.get(field), str):
                candidates.append(leaf / directory / Path(record[field]).name)
        for raw_path in candidates:
            if raw_path.is_file():
                hashes[str(raw_path.resolve())] = file_hash(raw_path)
                bound_raw.append(str(raw_path.resolve()))
        indexed[name] = copy.deepcopy(record)
    require(set(indexed) == set(requested), "Supplemental requested modules differ from profile records")
    edited = {name for name in after["summary"]["modules"]
              if before["summary"]["source_hashes_before"].get(before["summary"]["modules"][name])
              != after["summary"]["source_hashes_after"].get(after["summary"]["modules"][name])}
    require(set(data.get("edited_modules", [])) == edited, "Supplemental edited-module inventory differs")
    require((set(before["profiles"]) | edited) <= (set(after["profiles"]) | set(indexed)),
            "Supplemental evidence leaves baseline top8 or edited modules unprofiled")
    return {"provenance_label": "supplemental after warm profile", "profiles": indexed,
            "summary": data, "path": str(path), "input_sha256": hashes,
            "bound_adjacent_raw_files": bound_raw, "identical_duplicates": duplicates,
            "scope": "Additional profiles used only in comparison; original after summary and its independently selected top8 are unchanged"}


def compare_profiles(before: dict, after: dict, supplement: dict | None = None) -> dict:
    old, new = before["profiles"], dict(after["profiles"])
    labels = {name: "full after snapshot" for name in new}
    if supplement:
        for name, record in supplement["profiles"].items():
            if name not in new:
                new[name] = record
                labels[name] = supplement["provenance_label"]
    rows, events = [], []
    for name in sorted(set(old) | set(new)):
        if name not in old or name not in new:
            rows.append({"module": name, "matched": False, "available_side": "before" if name in old else "after",
                         "after_provenance": labels.get(name)})
            continue
        b, a = old[name], new[name]
        require(b["returncode"] == a["returncode"] == 0 and not b.get("guard_errors") and not a.get("guard_errors"),
                "Failed warm profile: " + name)
        phases = {}
        for phase in sorted(set(b["profile"]["phases_s"]) | set(a["profile"]["phases_s"])):
            bv, av = b["profile"]["phases_s"].get(phase), a["profile"]["phases_s"].get(phase)
            phases[phase] = delta(bv, av) if bv is not None and av is not None else {"before": bv, "after": av, "delta": None, "percent": None}
        rows.append({"module": name, "matched": True, "after_provenance": labels[name],
                     "wall_s": delta(b["timing"]["wall_s"], a["timing"]["wall_s"]), "phases": phases})
    for side, indexed in (("before", old), ("after", new)):
        for name, record in sorted(indexed.items()):
            for event in sorted(record["profile"]["events_over_100ms"], key=lambda item: item["seconds"], reverse=True)[:10]:
                events.append({"side": side, "module": name,
                               "provenance": "full before snapshot" if side == "before" else labels[name], **event})
    return {"modules": rows, "events": events,
            "matched_count": sum(x["matched"] for x in rows),
            "caveat": "Serial, warm, own-file profiles omit olean output. Exclusive profiler phases are not a complete wall-time partition. Missing categories are not substituted with zero; unmatched modules do not establish phase changes."}


def assess_ab(data: dict) -> dict:
    if data.get("schema_version") == 1 and data.get("status") == "failed_intervention":
        require(data.get("decision") == "reverted" and data.get("kept") is False,
                "Failed intervention cannot be retained")
        require(data.get("performance_comparison_excluded") is True
                and isinstance(data.get("failure_reason"), str) and bool(data["failure_reason"].strip()),
                "Failed intervention needs explicit exclusion and failure reason")
        require(data.get("basis") in {"phase", "wall"}, "Failed intervention has invalid intended measurement basis")
        old, new = data.get("before_runs"), data.get("after_runs")
        require(isinstance(old, list) and isinstance(new, list) and len(old) == len(new) == 3,
                "Failed intervention requires three attempts of each variant")
        require(all(run.get("valid") is True and run.get("returncode") == 0 for run in old)
                and all(run.get("valid") is False and type(run.get("returncode")) is int
                        and run["returncode"] != 0 for run in new),
                "Failed intervention does not establish valid controls and failed candidates")
        diagnostics = data.get("diagnostic_failed_attempts")
        require(isinstance(diagnostics, list) and len(diagnostics) == 3
                and all(x.get("record", {}).get("guard_errors") == []
                        and x["record"].get("artifact_changes") == []
                        and x["record"].get("diagnostics", {}).get("error_count", 0) > 0
                        for x in diagnostics), "Failed intervention needs guarded raw compiler failures")
        return {"status": "failed_intervention", "module": data["module"], "intervention": data["intervention"],
                "basis": data.get("basis"), "relevant_phase": data.get("relevant_phase"),
                "before_runs": [number(run["wall_s"], "baseline diagnostic wall") for run in old],
                "after_runs": [number(run["wall_s"], "failed-attempt diagnostic wall") for run in new],
                "before_median_s": None, "after_median_s": None, "saving_s": None, "saving_percent": None,
                "has_required_repetitions": True, "meets_2s_or_10percent_threshold": False,
                "supports_retaining_edit": False, "reported_kept": False,
                "failure_reason": data["failure_reason"], "performance_comparison_excluded": True,
                "diagnostic_failed_attempts": data.get("diagnostic_failed_attempts", []),
                "evidence": data,
                "caveat": "Failed candidate times are diagnostic only. No candidate median, speed savings, speed-regression or null result is inferred from aborted elaborations."}
    require(data.get("schema_version") == 1 and data.get("status") == "completed", "Invalid A/B schema/status")
    require(data.get("basis") in {"phase", "wall"}, "A/B basis must be phase or wall")
    basis, phase = data["basis"], data.get("relevant_phase")
    require(basis != "phase" or isinstance(phase, str) and bool(phase), "A/B phase is required")
    values = {}
    for side in ("before", "after"):
        runs = data.get(side + "_runs")
        require(isinstance(runs, list) and bool(runs), "Missing A/B runs: " + side)
        values[side] = [number(run["wall_s"] if basis == "wall" else run["phases_s"][phase], "A/B " + side) for run in runs]
    old, new = statistics.median(values["before"]), statistics.median(values["after"])
    saving, percent = old - new, 100 * (old - new) / old if old else None
    enough = basis == "phase" or min(len(values["before"]), len(values["after"])) >= 3
    threshold = (saving >= 2 or math.isclose(saving, 2, rel_tol=0, abs_tol=1e-9)
                 or percent is not None and (percent >= 10 or math.isclose(percent, 10, rel_tol=0, abs_tol=1e-9)))
    qualified = enough and threshold and data.get("matched_setup") is True and data.get("other_phases_regressed") is False and data.get("statements_changed") is False
    return {"status": "completed", "module": data["module"], "intervention": data["intervention"], "basis": basis,
            "relevant_phase": phase, "before_runs": values["before"], "after_runs": values["after"],
            "before_median_s": old, "after_median_s": new, "saving_s": saving, "saving_percent": percent,
            "has_required_repetitions": enough, "meets_2s_or_10percent_threshold": threshold,
            "supports_retaining_edit": qualified, "reported_kept": data.get("kept"),
            "evidence": data,
            "caveat": "Assessment uses supplied A/B records; source/setup and non-regression claims require their retained raw logs. One full-build snapshot on each side is descriptive and does not replace per-intervention A/B."}


def check_api(data: dict, after: dict, initial_commit: str | None, repo: Path) -> dict:
    require(data.get("status") == "passed" and data.get("scope") == "exact_public_declaration_inventory_and_decoded_kernel_type_bytes",
            "API record does not report the required passed full-type comparison")
    count = data.get("expected_public_declarations")
    require(type(count) is int and count > 0 and all(data.get(key) == count for key in
            ("before_public_declarations", "after_public_declarations", "compared_public_declarations")), "API inventory counts differ")
    require(all(data.get(key) == [] for key in ("missing_public_declarations", "added_public_declarations", "differences")), "API record contains differences")
    require(initial_commit is None or data.get("before_commit") == initial_commit, "API baseline differs from initial sweep commit")
    require(len(data.get("challenge_root_types", {})) == 6 and all(x["before_type_sha256"] == x["after_type_sha256"] for x in data["challenge_root_types"].values()), "API root types differ")
    bound = data.get("after_source_sha256", {})
    for path in after["summary"]["modules"].values():
        require(bound.get(path) == after["summary"]["source_hashes_after"].get(path), "API record does not bind measured after source: " + path)
    export = repo / relative(data["after_export_path"])
    require(export.is_file() and file_hash(export) == data["after_export_sha256"], "API compared export is missing or has changed")
    return {"status": "passed", "compared_public_declarations": count,
            "challenge_roots": 6, "source_binding": "All measured after-build Lean sources match the comparison record",
            "scope": data["scope"], "limitations": data.get("limitations"),
            "lean_or_kernel_executed_by_comparison": data.get("lean_or_kernel_executed")}


def fmt(value: Any, digits: int = 2) -> str:
    return "—" if value is None else f"{value:.{digits}f}" if type(value) in (float, int) else str(value)


def cell(value: Any) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def table(headers: list[str], rows: list[list[Any]]) -> list[str]:
    return ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |",
            *["| " + " | ".join(cell(x) for x in row) + " |" for row in rows]]


def report(data: dict) -> str:
    before, after = data["snapshots"]["before"], data["snapshots"]["after"]
    b, a, comparison = before["summary"], after["summary"], data["comparison"]
    lines = ["# Elaboration cleanup: before and after", "", "## Scope and sequence", "",
             "The sequence was an initial dead-code sweep, a complete pre-elaboration baseline, measured elaboration interventions, and a second complete elaboration test. The timing comparison starts after the dead-code sweep; it does not measure that sweep's speed effect.", ""]
    dead = data.get("dead_code")
    if dead:
        lines += [f"Initial source commit: `{dead['source_commit_before_sweep']}`. Safe user-written private/helper deletions: **{dead['private_declaration_sweep']['safe_deletions']}**. Redundant direct local imports removed: **{len(dead['removed_redundant_local_imports'])}** across **{len({x['file'] for x in dead['removed_redundant_local_imports']})}** files. Whole modules removed: **{len(dead['module_sweep']['safe_whole_module_removals'])}**.",
                  f"All local import closures preserved: `{dead.get('local_module_closures_preserved')}`. Sweep record's own status: `{dead.get('status')}`; the subsequent valid builds are separate evidence.", ""]
    else:
        lines += ["No dead-code record was supplied; its findings are not inferred from timing data.", ""]
    lines += ["The verified build scope and six principal challenge roots do not establish full manuscript coverage or English-to-Lean equivalence. Existing attainment and representation qualifications remain separate mathematical scope limitations.", "", "## Setup and provenance", ""]
    setup_rows = []
    for key in ("commit", "started_utc", "finished_utc", "host", "platform", "compiler_version", "time_version", "cores", "driver_parallelism", "lean_internal_threads"):
        values = [summary["provenance"].get(key) for summary in (b, a)]
        if key == "time_version":
            values = [value.split("\n", 1)[0] if isinstance(value, str) else value for value in values]
        setup_rows.append([key, *values])
    lines += table(["Field", "Before", "After"], setup_rows)
    lines += ["", "Compiler and GNU time hashes, host, core count, driver parallelism and Lean internal-thread policy match. The retained provenance reports the exact RSS interpretation and process-visibility availability. An unavailable process inventory is not evidence of an idle host.", "", "## Size snapshot", ""]
    lines += table(["Scope", "Before files", "After files", "Before physical lines", "After physical lines", "Before code lines", "After code lines"],
                   [[scope, b["size"][scope]["counted_files"], a["size"][scope]["counted_files"], b["size"][scope]["total_lines"], a["size"][scope]["total_lines"], b["size"][scope]["code_lines"], a["size"][scope]["code_lines"]]
                    for scope in ("git_tree", "git_build_scope", "working_build_scope")])
    lines += ["", "The full Git tree includes Lean files outside the production build. Cost per line uses the committed own build scope; comment-only files are excluded according to the measured snapshot.", "", "## Headline timing and build health", ""]
    timing_rows = []
    for key in ("wall_s", "cpu_s", "user_s", "sys_s", "percent_cpu", "max_rss_raw"):
        d = delta(b["build"]["timing"][key], a["build"]["timing"][key])
        timing_rows.append([key, fmt(d["before"]), fmt(d["after"]), fmt(d["delta"]), fmt(d["percent"])])
    for key in ("cpu_s", "observed_cpu_parallelism"):
        d = delta(comparison["sums"]["before"][key], comparison["sums"]["after"][key])
        timing_rows.append(["summed own " + key, fmt(d["before"], 3), fmt(d["after"], 3), fmt(d["delta"], 3), fmt(d["percent"])])
    lines += table(["Metric", "Before", "After", "Delta", "Delta %"], timing_rows)
    lines += ["", "Module CPU is GNU user + system time. Every compiler invocation is timed, including jobs under one second. Full wall time includes startup and measurement-wrapper/guard overhead; compiler peak RSS is not additive. Read each snapshot's RSS interpretation before comparing to other platforms.", ""]
    lines += table(["Health", "Before", "After"], [[key, b["health"][key], a["health"][key]] for key in
                    ("error_count", "warning_count", "sorry_warning_count", "unauthorized_sorry_tokens")]
                   + [["complete measured jobs", b["coverage"]["measured"], a["coverage"]["measured"]], ["build exit", b["build"]["returncode"], a["build"]["returncode"]]])
    for side, summary in (("Before", b), ("After", a)):
        lines += ["", side + " warning census:", "", "```json",
                  json.dumps(summary["health"]["warning_kinds"], indent=2, sort_keys=True), "```"]
    lines += ["", "## Heavy tail and top 30", ""]
    lines += table(["Wall threshold", "Before files", "After files", "Delta"], [["≥" + t + "s", x["before"], x["after"], x["after"] - x["before"]] for t, x in comparison["heavy_tail"].items()])
    lines += [""] + table(["Module", "Before wall s", "After wall s", "Delta wall s", "Before CPU s", "After CPU s", "Delta CPU s", "Source changed"],
              [[f"`{x['module']}`", fmt(x["wall_s"]["before"]), fmt(x["wall_s"]["after"]), fmt(x["wall_s"]["delta"]), fmt(x["cpu_s"]["before"]), fmt(x["cpu_s"]["after"]), fmt(x["cpu_s"]["delta"]), x["source_changed"]] for x in comparison["top_30_after"]])
    lines += ["", "The table ranks the after build. All modules are joined by identity, including files outside the prior top 30; the complete joined inventory is in the accompanying JSON.", "", "## File-family costs", ""]
    lines += table(["Filename prefix", "Files", "Before CPU s", "After CPU s", "Delta CPU s", "Delta wall s"],
                   [[f"`{name}`", x["files"], fmt(x["before_cpu_s"]), fmt(x["after_cpu_s"]), fmt(x["after_cpu_s"] - x["before_cpu_s"]), fmt(x["after_wall_s"] - x["before_wall_s"])]
                    for name, x in sorted(comparison["families"].items(), key=lambda item: item[1]["after_cpu_s"], reverse=True)])
    lines += ["", "These are reproducible filename families in the flat module directory, not parsed Lean namespaces.", "", "## Committed-source census", ""]
    census = data["source_census"]
    lines += table(["Metric", "Before", "After"], [[name, census["before"][name], census["after"][name]] for name in ("maximum_physical_lines", "legacy_nonmodule_count")]
                   + [["files over " + str(limit) + " physical lines", len(census["before"]["files_over_" + str(limit) + "_lines"]), len(census["after"]["files_over_" + str(limit) + "_lines"])] for limit in (1000, 1500)])
    lines += [""] + table(["Override", "Before occurrences", "After occurrences"], [[key, census["before"]["override_counts"].get(key, 0), census["after"]["override_counts"].get(key, 0)] for key in OVERRIDES])
    lines += [""] + table(["Tactic token", "Before", "After"], [[key, census["before"]["tactic_token_counts"].get(key, 0), census["after"]["tactic_token_counts"].get(key, 0)] for key in TACTICS])
    lines += ["", census["before"]["caveat"] + " Legacy module headers are recorded; this pass does not migrate module syntax. Full per-file override locations and large-file lists are retained in JSON.", "", "## Cached dependency provenance", ""]
    dep_rows = []
    for side, snapshot in (("Before", before), ("After", after)):
        for package in snapshot["dependencies"]["packages"]:
            dep_rows.append([side, package["package"], package["olean_count"], "`" + package["resolved_package"] + "`"])
    lines += table(["Snapshot", "Package", "Cached oleans", "Resolved cache path"], dep_rows)
    lines += ["", "Every required direct external import resolved before measurement. Initial/final cached-package artifact size, mtime and inode manifests agree within each run; dependencies were inputs, not compilation targets. This cannot detect a mutation perfectly restored between snapshots. Lean standard-library paths are resolved by the pinned toolchain; package stat manifests do not additionally inventory all standard-library artifacts.", "", "## Matched warm own-file profiles", "", data["profiles"]["caveat"], ""]
    profile_rows = []
    for item in data["profiles"]["modules"]:
        if not item["matched"]:
            profile_rows.append([f"`{item['module']}`", item.get("after_provenance") or "—", "UNMATCHED (" + item["available_side"] + " only)", "—", "—", "—"])
        else:
            for phase, d in item["phases"].items():
                profile_rows.append([f"`{item['module']}`", item["after_provenance"], phase, fmt(d["before"], 3), fmt(d["after"], 3), fmt(d["delta"], 3)])
    lines += table(["Module", "After profile provenance", "Exclusive phase", "Before s", "After s", "Delta s"], profile_rows)
    if data.get("supplemental_profiles"):
        lines += ["", data["supplemental_profiles"]["scope"] + ". Its summary and available adjacent raw records/logs have separate SHA-256 bindings in the accompanying JSON."]
    lines += ["", "### Largest retained events above 100 ms", ""]
    lines += table(["Side", "Provenance", "Module", "Category", "Declaration/context", "Seconds"], [[x["side"], x["provenance"], f"`{x['module']}`", x["category"], x.get("declaration") or x.get("context") or "unattributed", fmt(x["seconds"], 3)] for x in data["profiles"]["events"]])
    lines += ["", "At most ten events per module and side appear here; full events remain in the measured JSON/raw logs. An anonymous elaboration event needs declaration tracing and statement/proof isolation before a proof-level cause is claimed.", "", "## Interventions and A/B evidence", ""]
    if data["ab"]:
        lines += table(["Module", "Intervention", "Classification", "Basis", "Runs B/A", "Median before s", "Median after s", "Saving s / %", "Threshold + evidence requirements", "Reported kept"],
                       [[f"`{x['module']}`", x["intervention"], "FAILED; performance comparison excluded" if x.get("status") == "failed_intervention" else "valid completed A/B", x["basis"] + (": " + x["relevant_phase"] if x["relevant_phase"] else ""), str(len(x["before_runs"])) + "/" + str(len(x["after_runs"])), fmt(x["before_median_s"]), fmt(x["after_median_s"]), fmt(x["saving_s"]) + " / " + fmt(x["saving_percent"]), "excluded failed attempt" if x.get("status") == "failed_intervention" else "supported" if x["supports_retaining_edit"] else "not established", x["reported_kept"]] for x in data["ab"]])
        for failed in (x for x in data["ab"] if x.get("status") == "failed_intervention"):
            lines += ["", f"Failed intervention in `{failed['module']}`: {failed['failure_reason']}",
                      "Valid baseline control attempts and failed candidate attempts were retained. Candidate medians and savings are excluded; this is neither a valid speed regression nor a valid null result.", ""]
            diagnostics = failed["diagnostic_failed_attempts"]
            lines += table(["Candidate attempt", "Compiler exit", "Wall s (diagnostic)", "CPU s (diagnostic)", "Errors"],
                           [[x["repetition"], x["record"]["returncode"], fmt(x["record"]["timing"]["wall_s"]), fmt(x["record"]["timing"]["cpu_s"]), "; ".join(x["record"].get("diagnostics", {}).get("errors", []))] for x in diagnostics])
    else:
        lines += ["No per-intervention A/B record was supplied. The full-build snapshots alone do not establish that any retained edit met the intervention threshold."]
    lines += ["", "A retained performance intervention requires a ≥2 second or ≥10% improvement in its relevant phase, with matching setup, unchanged statements and no transferred regression. A wall-time claim requires at least three runs on each side. Median values are used here; supplied raw evidence and reverted/null experiments must remain reviewable.", "", "## Parallelism, contention and size prediction", ""]
    p = comparison["size_prediction"]
    lines += [f"Code-line change: **{p['delta_code_lines']}**. Baseline CPU cost: **{fmt(p['baseline_cpu_ms_per_code_line'], 3)} ms/code line**. Predicted CPU change from size alone: **{fmt(p['predicted_cpu_delta_s'])} s**. Actual summed own CPU change: **{fmt(p['actual_cpu_delta_s'])} s**. Absolute actual/predicted ratio: **{fmt(p['absolute_actual_predicted_ratio'])}** (undefined when predicted change is zero).", ""]
    lines += table(["Conservative contention screen", "Observed"], [[key, value] for key, value in comparison["contention"]["heuristic_signals"].items()])
    lines += ["", comparison["contention"]["limitation"],
              "Multiple screening signals are present: **" + str(comparison["contention"]["multiple_signals"]) + "**. " + ("Treat whole-build deltas as potentially contention-bound and avoid structural causal conclusions." if comparison["contention"]["multiple_signals"] else "Single whole-build runs still admit cache, scheduler, thermal and background-load noise; causality rests on targeted A/B evidence."),
              "", "The driver is serial. Host-core work floors and weighted import chains in the original snapshots are hypothetical scheduling bounds; they do not describe this serial driver's observed schedule.", "", "## Public theorem/API preservation", ""]
    if data.get("api_check"):
        api = data["api_check"]
        lines += [f"A supplied, source-bound record reports a **passed** comparison of **{api['compared_public_declarations']}** public declarations and all **{api['challenge_roots']}** challenge roots, using independently decoded canonical kernel-type bytes and exact public inventory/identity fields.", "", api.get("limitations") or "This does not establish English-to-Lean equivalence or unchanged definition bodies."]
    else:
        lines += ["No validated public-type comparison record was supplied. This report makes no API-preservation pass claim. Successful elaboration is separate from exact statement preservation and manuscript correspondence."]
    lines += ["", "## Reproduction and evidence", "", "```sh", shlex.join(data["invocation"]), "```", "",
              "This generator runs no compiler or proof checker. Reproduce the measurements using each snapshot's recorded harness invocation; keep cached dependencies populated and preserve the same compiler, GNU time and serial scheduling. Source censuses come from the snapshot commits and recorded build-scope inventories, never a moving working tree.", ""]
    for side, snapshot in (("Before", before), ("After", after)):
        lines += [side + " harness invocation:", "", "```sh", shlex.join(snapshot["summary"]["provenance"]["invocation"]), "```", ""]
    lines += ["Inputs and their SHA-256 bindings, all joined module deltas, full source censuses and evidence paths are in `comparison.json`. Original before/after reports and raw logs remain the authoritative measured observations. Two snapshots cannot establish a monotonic trend.", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--before", required=True, type=Path, help="Valid before summary.json")
    parser.add_argument("--after", required=True, type=Path, help="Valid after summary.json")
    parser.add_argument("--before-measurements", type=Path)
    parser.add_argument("--after-measurements", type=Path)
    parser.add_argument("--after-supplemental-profiles", type=Path,
                        help="Fixed continuation matched-profiles/summary.json; original after top8 stays unchanged")
    parser.add_argument("--before-commit", help="Optional expected full before SHA")
    parser.add_argument("--after-commit", help="Optional expected full after SHA")
    parser.add_argument("--initial-commit", help="Optional expected source SHA before dead sweep")
    parser.add_argument("--dead-code-json", type=Path)
    parser.add_argument("--ab-summary", action="append", default=[], type=Path, help="A/B JSON or directory containing summary.json; see README")
    parser.add_argument("--api-check", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        before, after = read_snapshot(args.before, args.before_measurements), read_snapshot(args.after, args.after_measurements)
        for side, snapshot in (("before", before), ("after", after)):
            expected = getattr(args, side + "_commit")
            require(expected is None or expected == snapshot["summary"]["provenance"]["commit"], "Unexpected " + side + " commit")
        data = {"schema_version": 1, "status": "completed", "generated_at_utc": datetime.now(timezone.utc).isoformat(),
                "invocation": [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
                "snapshots": {"before": before, "after": after}, "comparison": compare_builds(before, after),
                "profiles": compare_profiles(before, after), "source_census": {}, "ab": [],
                "input_sha256": {**before["input_sha256"], **after["input_sha256"]},
                "dead_code": None, "api_check": None, "supplemental_profiles": None}
        if args.after_supplemental_profiles:
            supplement = supplemental_profiles(args.after_supplemental_profiles, before, after)
            data["supplemental_profiles"] = supplement
            data["input_sha256"].update(supplement["input_sha256"])
            data["profiles"] = compare_profiles(before, after, supplement)
        for side, snapshot in (("before", before), ("after", after)):
            summary = snapshot["summary"]
            paths = sorted(summary["size"]["git_build_scope"]["per_file"])
            texts = git_blobs(args.repo.resolve(), summary["provenance"]["commit"], paths)
            data["source_census"][side] = source_census(summary, texts)
        initial = args.initial_commit
        if args.dead_code_json:
            dead = load(args.dead_code_json)
            require(initial is None or initial == dead["source_commit_before_sweep"], "Initial source commit differs from dead-code record")
            initial = dead["source_commit_before_sweep"]
            require(dead["private_declaration_sweep"]["safe_deletions"] == 0
                    and len(dead["removed_redundant_local_imports"]) == 50
                    and dead["local_module_closures_preserved"] is True,
                    "Dead sweep facts differ from the intended cleanup record")
            data["dead_code"] = dead
            data["input_sha256"][str(args.dead_code_json.resolve())] = file_hash(args.dead_code_json)
        for path in args.ab_summary:
            path = path / "summary.json" if path.is_dir() else path
            data["ab"].append(assess_ab(load(path)))
            data["input_sha256"][str(path.resolve())] = file_hash(path)
        if args.api_check:
            data["api_check"] = check_api(load(args.api_check), after, initial, args.repo.resolve())
            data["input_sha256"][str(args.api_check.resolve())] = file_hash(args.api_check)
        for path, expected in data["input_sha256"].items():
            require(file_hash(Path(path)) == expected, "Evidence input changed while reporting: " + path)
        args.output.mkdir(parents=True, exist_ok=True)
        json_path, markdown_path = args.output / "comparison.json", args.output / "ELABORATION_COMPARISON.md"
        json_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        markdown_path.write_text(report(data))
        print(markdown_path)
        return 0
    except (KeyError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("Comparative report rejected: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
