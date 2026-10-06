#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Measure the guarded, serial project build without invalidating any cache.

This is an original implementation of the lean-elaboration-test methodology.
It preserves build.sh, lean.sh and compiler.py, and instruments the actual
compiler through NONADDITIVITY_LEAN. No Lake command is invoked. A run directory
must be new or empty. Example:

  python3 scripts/elaboration_test.py --label before --output /tmp/elab-before \
      --time-bin /absolute/path/to/gnu-time

The default compiler is the actual executable under the pinned elan toolchain.
An after run can use --prior-summary /tmp/elab-before/summary.json.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import signal
import socket
import subprocess
import sys
import threading
from datetime import datetime, timezone
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DRIVER_FILES = ("build.sh", "lean.sh", "scripts/compiler.py", "lean-toolchain",
                "lakefile.toml", "lake-manifest.json", "scripts/elaboration_test.py")
TIME_LABELS = {
    "User time (seconds)": "user_s",
    "System time (seconds)": "sys_s",
    "Percent of CPU this job got": "percent_cpu",
    "Elapsed (wall clock) time (h:mm:ss or m:ss)": "wall_s",
    "Maximum resident set size (kbytes)": "max_rss_raw",
    "Exit status": "reported_exit_status",
}
REQUIRED_TIMES = set(TIME_LABELS.values())


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def captured(command: list[str], *, cwd: Path = ROOT) -> str:
    return subprocess.run(command, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()


def stat_entry(path: Path) -> dict[str, int]:
    stat = path.stat()
    return {"size": stat.st_size, "mtime_ns": stat.st_mtime_ns,
            "inode": stat.st_ino}


def own_modules(root: Path) -> dict[str, str]:
    paths = list((root / "Nonadditivity").rglob("*.lean"))
    paths += [root / name for name in ("Nonadditivity.lean", "Audit.lean", "All.lean")
              if (root / name).is_file()]
    return {".".join(path.relative_to(root).with_suffix("").parts):
            path.relative_to(root).as_posix() for path in sorted(paths)}


def source_stat_manifest(root: Path) -> dict[str, dict[str, int]]:
    paths = set(own_modules(root).values())
    paths.update(name for name in DRIVER_FILES if (root / name).is_file())
    return {name: stat_entry(root / name) for name in sorted(paths)}


def source_hash_manifest(root: Path) -> dict[str, str]:
    return {name: digest(root / name) for name in source_stat_manifest(root)}


def own_artifact_manifest(root: Path) -> dict[str, dict[str, int]]:
    build = root / ".lake/build/lib/lean"
    paths = list((build / "Nonadditivity").rglob("*.olean"))
    paths += [build / (name + ".olean") for name in ("Nonadditivity", "Audit", "All")
              if (build / (name + ".olean")).is_file()]
    return {path.relative_to(root).as_posix(): stat_entry(path) for path in sorted(paths)}


def manifest_changes(before: dict, after: dict) -> list[str]:
    return sorted(name for name in before.keys() | after.keys()
                  if before.get(name) != after.get(name))


def lexical_code(text: str, *, hide_strings: bool = False) -> str:
    """Mask nested Lean comments, retaining line positions and string code.

    Strings are retained for line counting but optionally masked for token scans.
    Character literals containing a double quote do not begin a string.
    """
    result = list(text)
    index, depth, in_string, in_line = 0, 0, False, False
    while index < len(text):
        char = text[index]
        pair = text[index:index + 2]
        if char == "\n":
            in_line = False
            index += 1
            continue
        if in_line:
            result[index] = " "
            index += 1
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                result[index:index + 2] = "  "
                index += 2
            else:
                result[index] = " "
                index += 1
        elif in_string:
            if hide_strings:
                result[index] = " "
            if char == "\\" and index + 1 < len(text):
                if hide_strings:
                    result[index + 1] = " "
                index += 2
            else:
                if char == '"':
                    in_string = False
                index += 1
        elif pair == "--":
            in_line = True
            result[index:index + 2] = "  "
            index += 2
        elif pair == "/-":
            depth = 1
            result[index:index + 2] = "  "
            index += 2
        elif text.startswith(("'\"'", "'\\\"'"), index):
            width = 3 if text[index + 1] == '"' else 4
            if hide_strings:
                result[index:index + width] = " " * width
            index += width
        else:
            if char == '"':
                in_string = True
                if hide_strings:
                    result[index] = " "
            index += 1
    return "".join(result)


def module_header(text: str) -> bool:
    # A module/doc comment before `module` is disallowed by Lean's module syntax.
    remaining = text.lstrip("\ufeff \t\r\n")
    while remaining.startswith(("--", "/-")):
        if remaining.startswith(("/--", "/-!")):
            return False
        if remaining.startswith("--"):
            remaining = remaining.partition("\n")[2].lstrip()
        else:
            depth, index = 1, 2
            while index < len(remaining) and depth:
                if remaining.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif remaining.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            remaining = remaining[index:].lstrip()
    return re.match(r"module(?![\w'.!?])", remaining) is not None


def size_snapshot(texts: dict[str, str]) -> dict:
    totals = {"lean_files_in_scope": len(texts), "counted_files": 0,
              "total_lines": 0, "code_lines": 0, "comment_only_files": [],
              "legacy_nonmodule_files": [], "per_file": {}}
    for name, text in sorted(texts.items()):
        code_lines = sum(bool(line.strip()) for line in lexical_code(text).splitlines())
        item = {"total_lines": len(text.splitlines()), "code_lines": code_lines,
                "module_header": module_header(text)}
        totals["per_file"][name] = item
        if Path(name).name != "lakefile.lean" and not item["module_header"]:
            totals["legacy_nonmodule_files"].append(name)
        if not code_lines:
            totals["comment_only_files"].append(name)
            continue
        totals["counted_files"] += 1
        totals["total_lines"] += item["total_lines"]
        totals["code_lines"] += code_lines
    return totals


def git_tree_texts(root: Path, commit: str) -> dict[str, str]:
    listing = subprocess.run(["git", "ls-tree", "-rz", commit], cwd=root,
                             check=True, stdout=subprocess.PIPE).stdout
    entries = []
    for entry in listing.split(b"\0"):
        if not entry:
            continue
        info, name = entry.split(b"\t", 1)
        mode, kind, oid = info.split()
        if kind == b"blob" and name.endswith(b".lean") and not name.startswith(b".lake/"):
            entries.append((name.decode(), oid.decode()))
    batch = subprocess.run(["git", "cat-file", "--batch"], cwd=root, check=True,
                           input="".join(oid + "\n" for _, oid in entries).encode(),
                           stdout=subprocess.PIPE).stdout
    result, cursor = {}, 0
    for name, _ in entries:
        end = batch.index(b"\n", cursor)
        header = batch[cursor:end].split()
        if len(header) != 3 or header[1] != b"blob":
            raise RuntimeError("Unexpected git cat-file response")
        length = int(header[2])
        result[name] = batch[end + 1:end + 1 + length].decode("utf-8")
        cursor = end + 2 + length
    return result


def import_graph(root: Path, modules: dict[str, str]) -> tuple[dict, dict]:
    graph, external = {}, {}
    for name, relative in modules.items():
        imports = []
        for line in lexical_code((root / relative).read_text(), hide_strings=True).splitlines():
            match = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)", line)
            if match:
                imports.extend(match.group(1).split())
        graph[name] = [entry for entry in imports if entry in modules]
        external[name] = [entry for entry in imports if entry not in modules]
    return graph, external


def topological_order(graph: dict[str, list[str]]) -> list[str]:
    order, seen, pending = [], set(), set()
    def visit(name: str) -> None:
        if name in seen:
            return
        if name in pending:
            raise ValueError("Import cycle at " + name)
        pending.add(name)
        for dependency in graph[name]:
            visit(dependency)
        pending.remove(name)
        seen.add(name)
        order.append(name)
    for name in sorted(graph, key=lambda entry: (entry == "Audit", entry)):
        visit(name)
    return order


def coverage_check(expected: list[str], records: list[dict]) -> dict:
    actual = [record["module"] for record in records if record["phase"] == "build"]
    counts = Counter(actual)
    missing = sorted(set(expected) - set(actual))
    unexpected = sorted(set(actual) - set(expected))
    duplicates = sorted(name for name, count in counts.items() if count > 1)
    failures = [record["module"] for record in records
                if record["phase"] == "build" and record["returncode"] != 0]
    return {"expected": len(expected), "measured": len(actual), "missing": missing,
            "unexpected": unexpected, "duplicates": duplicates,
            "failed": failures, "order_matches": actual == expected,
            "complete": not (missing or unexpected or duplicates or failures) and actual == expected}


def parse_elapsed(value: str) -> float:
    parts = value.strip().split(":")
    if not 1 <= len(parts) <= 3:
        raise ValueError("Invalid elapsed time: " + value)
    total = 0.0
    for part in parts:
        total = total * 60 + float(part)
    return total


def parse_gnu_time(text: str) -> dict:
    result: dict[str, Any] = {}
    for line in text.splitlines():
        stripped = line.strip()
        for label, key in TIME_LABELS.items():
            prefix = label + ":"
            if stripped.startswith(prefix):
                value = stripped[len(prefix):].strip()
                if key == "wall_s":
                    result[key] = parse_elapsed(value)
                elif key == "percent_cpu":
                    result[key] = float(value.removesuffix("%"))
                elif key in ("max_rss_raw", "reported_exit_status"):
                    result[key] = int(value)
                else:
                    result[key] = float(value)
        if stripped.startswith("Command terminated by signal"):
            result["signal"] = stripped
    missing = sorted(REQUIRED_TIMES - result.keys())
    if missing:
        raise ValueError("Incomplete GNU time output: " + ", ".join(missing))
    result["cpu_s"] = result["user_s"] + result["sys_s"]
    return result


def diagnostic_census(text: str) -> dict:
    warnings, errors, kinds = [], [], Counter()
    for line in text.splitlines():
        match = re.search(r"(?:^|:\s)(warning|error):\s*(.*)", line)
        if not match:
            continue
        severity, message = match.groups()
        if severity == "error":
            errors.append(message)
            continue
        warnings.append(message)
        if "sorry" in message:
            kind = "declaration uses sorry"
        elif "unused" in message.lower():
            kind = "unused variable/argument"
        elif "deprecated" in message.lower():
            kind = "deprecated declaration/syntax"
        elif "linter" in message.lower():
            kind = "linter"
        else:
            kind = message
        kinds[kind] += 1
    return {"warning_count": len(warnings), "error_count": len(errors),
            "sorry_warning_count": sum("sorry" in warning for warning in warnings),
            "warning_kinds": dict(kinds), "warnings": warnings, "errors": errors}


def duration_seconds(number: str, unit: str) -> float:
    factors = {"s": 1, "ms": 1e-3, "us": 1e-6, "µs": 1e-6, "ns": 1e-9}
    return float(number) * factors[unit]


def parse_profile(text: str) -> dict:
    phases, events, in_totals = {}, [], False
    for line in text.splitlines():
        if "cumulative profiling times" in line.lower():
            in_totals = True
            continue
        event = re.search(r"^(.*?)\s+took\s+([\d.eE+-]+)\s*(ms|µs|us|ns|s)\b(.*)$", line.strip())
        if event:
            category, number, unit, suffix = event.groups()
            declaration = None
            if " of " in category:
                category, declaration = category.split(" of ", 1)
            seconds = duration_seconds(number, unit)
            events.append({"category": category.strip(), "seconds": seconds,
                           "declaration": declaration, "context": suffix.strip(), "raw": line})
            continue
        if in_totals:
            match = re.match(r"^\s*(.+?)\s*(?::|=)\s*([\d.eE+-]+)\s*(ms|µs|us|ns|s)\s*$", line)
            if match:
                category, number, unit = match.groups()
                phases[category.strip()] = duration_seconds(number, unit)
            elif line.strip():
                # Lean versions can print aligned `category  1.23s` instead.
                match = re.match(r"^\s*(.+?)\s+([\d.eE+-]+)\s*(ms|µs|us|ns|s)\s*$", line)
                if match:
                    category, number, unit = match.groups()
                    phases[category.strip()] = duration_seconds(number, unit)
                else:
                    in_totals = False
    total = sum(phases.values())
    dominant = max(phases, key=phases.get) if phases else None
    significant = bool(dominant and phases[dominant] > 5 and phases[dominant] > total * .25)
    return {"phases_s": phases, "categorized_s": total, "dominant_phase": dominant,
            "dominant_above_action_floor": significant,
            "events_over_100ms": [event for event in events if event["seconds"] >= .1],
            "all_reported_events": events}


def longest_weighted_path(graph: dict[str, list[str]], weights: dict[str, float]) -> dict:
    values, paths = {}, {}
    for name in topological_order(graph):
        dependency = max(graph[name], key=lambda entry: values[entry]) if graph[name] else None
        values[name] = weights.get(name, 0) + (values[dependency] if dependency else 0)
        paths[name] = (paths[dependency] if dependency else []) + [name]
    endpoint = max(values, key=values.get) if values else None
    return {"seconds": values[endpoint] if endpoint else 0,
            "modules": paths[endpoint] if endpoint else []}


def dependencies_snapshot(root: Path, compiler: Path, external: dict) -> dict:
    packages = root / ".lake/packages"
    libraries = sorted(path / ".lake/build/lib/lean" for path in packages.iterdir()
                       if path.is_dir() and (path / ".lake/build/lib/lean").is_dir())
    libraries.append(compiler.parent.parent / "lib/lean")
    required = sorted({name for imports in external.values() for name in imports})
    resolved, missing = {}, []
    for name in required:
        relative = Path(*name.split(".")).with_suffix(".olean")
        matches = [lib / relative for lib in libraries if (lib / relative).is_file()]
        if matches:
            resolved[name] = str(matches[0].resolve())
        else:
            missing.append(name)
    if missing:
        raise RuntimeError("Missing cached imports; do not rebuild upstream: " + ", ".join(missing))
    artifacts, package_records = {}, []
    for lib in libraries[:-1]:
        paths = sorted(lib.rglob("*.olean"))
        package = lib.parents[3]
        package_records.append({"package": package.name, "resolved_package": str(package.resolve()),
                                "olean_count": len(paths)})
        for path in paths:
            artifacts[str(path.resolve())] = stat_entry(path)
    return {"packages_path": str(packages), "resolved_packages_path": str(packages.resolve()),
            "packages": package_records, "required_external_imports": resolved,
            "artifacts": artifacts, "olean_count": len(artifacts),
            "manifest_policy": "Initial/final size, mtime_ns and inode; no cache invalidation or polling."}


def process_inventory() -> dict:
    """Informational only: restricted process visibility must not gate builds."""
    try:
        process = subprocess.run(["ps", "-axo", "pid,etime,command"], text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as error:
        return {"available": False, "processes": [], "error": str(error)}
    if process.returncode:
        return {"available": False, "processes": [],
                "error": process.stderr.strip() or f"ps exited {process.returncode}"}
    return {"available": True, "processes": [
        line for line in process.stdout.splitlines()
        if re.search(r"(?:^|[/\s])(?:lean|lake)(?:\s|$)", line)], "error": None}


def process_inventory_description(inventory: dict) -> str:
    return str(len(inventory["processes"])) if inventory["available"] else "unavailable"


def check_source_guard(config: dict) -> None:
    changes = manifest_changes(config["source_stats"], source_stat_manifest(Path(config["root"])))
    if changes:
        raise RuntimeError("Source/driver changed during measurement: " + ", ".join(changes))


def guarded_subprocess(command: list[str], log_path: Path, config: dict, env: dict) -> int:
    """Abort a running compiler/build on observed source mutation.

    Only the small own-source stat manifest is polled. Upstream cache manifests
    are taken outside timing, so cache traversal does not contend with Lean.
    """
    guard_failure: list[str] = []
    done = threading.Event()
    with log_path.open("w") as log:
        process = subprocess.Popen(command, cwd=config["root"], env=env,
                                   stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        def watch() -> None:
            while not done.wait(1):
                try:
                    check_source_guard(config)
                except Exception as error:
                    guard_failure.append(str(error))
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    return
        watcher = threading.Thread(target=watch, daemon=True)
        watcher.start()
        try:
            returncode = process.wait()
        except KeyboardInterrupt:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            raise
        finally:
            done.set()
            watcher.join()
    if guard_failure:
        with log_path.open("a") as log:
            log.write("\nMEASUREMENT INVALID: " + guard_failure[0] + "\n")
        raise RuntimeError(guard_failure[0])
    return returncode


def compiler_entry(config_path: Path, arguments: list[str]) -> int:
    """Internal NONADDITIVITY_LEAN endpoint, never a replacement build driver."""
    config = read_json(config_path)
    root, output = Path(config["root"]), Path(config["output"])
    compiler = config["compiler"]
    if arguments == ["--version"]:
        return subprocess.run([compiler, *arguments], cwd=root).returncode
    candidates = [arg for arg in arguments if arg.endswith(".lean")]
    if len(candidates) != 1:
        raise RuntimeError("Expected exactly one own Lean source")
    source = Path(candidates[0])
    source = (source if source.is_absolute() else root / source).resolve()
    reverse = {str((root / relative).resolve()): name for name, relative in config["modules"].items()}
    if str(source) not in reverse or not source.is_relative_to(root):
        raise RuntimeError("Refusing upstream/non-project compiler invocation: " + str(source))
    name = reverse[str(source)]
    relative = config["modules"][name]
    check_source_guard(config)
    state_path = output / "artifact-state.json"
    state = read_json(state_path)
    changes = manifest_changes(state, own_artifact_manifest(root))
    if changes:
        raise RuntimeError("Own build artifacts changed outside harness: " + ", ".join(changes))
    source_before = digest(source)
    if source_before != config["source_hashes"][relative]:
        raise RuntimeError("Source content no longer matches snapshot: " + relative)
    output_flags = {"-o", "-i", "-c", "-b"}
    if config["phase"] == "build":
        if arguments.count("-o") != 1:
            raise RuntimeError("Build invocation must have one explicit own olean output")
        output_arg = Path(arguments[arguments.index("-o") + 1])
        expected = root / ".lake/build/lib/lean" / Path(relative).with_suffix(".olean")
        if output_arg.resolve() != expected or expected.resolve() != expected:
            raise RuntimeError("Compiler output escapes expected own artifact: " + str(output_arg))
        if any(arg in output_flags - {"-o"} or arg.startswith(("--o=", "--i=", "--c=", "--bc="))
               for arg in arguments):
            raise RuntimeError("Unexpected extra compiler output flag")
        allowed_change = expected.relative_to(root).as_posix()
    else:
        if any(arg in output_flags or arg.startswith(("--o=", "--i=", "--c=", "--bc="))
               for arg in arguments):
            raise RuntimeError("Warm profiles must not write compiler artifacts")
        allowed_change = None
    phase = config["phase"]
    stem = name.replace(".", "_")
    log_path = output / "logs" / f"{phase}-{stem}.log"
    time_path = output / "timings" / f"{phase}-{stem}.time.txt"
    command = [config["time_bin"], "-v", "-o", str(time_path), compiler, *arguments]
    with log_path.open("w") as log:
        process = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert process.stdout is not None
        for line in iter(process.stdout.readline, b""):
            log.buffer.write(line)
            log.flush()
            sys.stdout.buffer.write(line)
            sys.stdout.flush()
        returncode = process.wait()
    timing = parse_gnu_time(time_path.read_text())
    final_artifacts = own_artifact_manifest(root)
    artifact_changes = manifest_changes(state, final_artifacts)
    unexpected = [path for path in artifact_changes if path != allowed_change]
    guard_errors = []
    try:
        check_source_guard(config)
    except RuntimeError as error:
        guard_errors.append(str(error))
    if digest(source) != source_before:
        guard_errors.append("Source changed while compiler ran: " + relative)
    if unexpected:
        guard_errors.append("Unexpected own artifact mutation: " + ", ".join(unexpected))
    if returncode == 0 and allowed_change and allowed_change not in final_artifacts:
        guard_errors.append("Compiler succeeded without its expected own olean")
    record = {"phase": phase, "module": name, "source": relative, "returncode": returncode,
              "timing": timing, "log": str(log_path), "time_log": str(time_path),
              "command": command, "source_sha256": source_before,
              "artifact_changes": artifact_changes, "guard_errors": guard_errors,
              "diagnostics": diagnostic_census(log_path.read_text())}
    if phase == "profile":
        record["profile"] = parse_profile(log_path.read_text())
    with (output / "measurements.jsonl").open("a") as records:
        records.write(json.dumps(record, sort_keys=True) + "\n")
    write_json(state_path, final_artifacts)
    if guard_errors:
        raise RuntimeError("; ".join(guard_errors))
    return returncode


def profile_finding(record: dict) -> str:
    profile = record["profile"]
    phase = (profile["dominant_phase"] or "").lower()
    if not profile["phases_s"]:
        return "Profile phase totals were not recognized; inspect the raw log before attribution."
    if not profile["dominant_above_action_floor"]:
        return "No phase exceeds both 5 seconds and 25% of categorized cost; no local lever established."
    if "import" in phase:
        return "Import load dominates; inspect consumer imports or upstream load before changing proofs."
    if "typeclass" in phase:
        return "Inspect searched classes and closed/open goals; a cache is not justified without that trace."
    if "simp" in phase:
        return "Inspect individual simp events over 1 second before testing a targeted simp-only change."
    if "interpretation" in phase:
        return "Inspect named tactic events; explicit arithmetic bounds are candidates only if arithmetic dominates."
    if "elaboration" in phase:
        return "Unattributed elaboration needs declaration tracing and statement/proof isolation before a fix."
    if "type checking" in phase:
        return "Inspect large proof terms; named intermediate facts may reduce term checking."
    return "Inspect the named events before selecting a measured intervention."


def aggregation(records: list[dict], graph: dict, code_lines: int, cores: int) -> dict:
    built = [record for record in records if record["phase"] == "build"]
    ordered = sorted(built, key=lambda record: record["timing"]["wall_s"], reverse=True)
    namespace: dict[str, dict] = defaultdict(lambda: {"files": 0, "cpu_s": 0.0, "wall_s": 0.0})
    for record in built:
        parts = record["module"].split(".")
        # This project has a flat module directory. The first CamelCase
        # component provides a useful, reproducible file-family breakdown.
        family = re.match(r"[A-Z][a-z0-9]*", parts[-1])
        prefix = (parts[0] + "." + family.group(0)) if len(parts) > 1 and family else parts[0]
        namespace[prefix]["files"] += 1
        for field in ("cpu_s", "wall_s"):
            namespace[prefix][field] += record["timing"][field]
    cpu = sum(record["timing"]["cpu_s"] for record in built)
    wall = sum(record["timing"]["wall_s"] for record in built)
    cpu_path = longest_weighted_path(graph, {record["module"]: record["timing"]["cpu_s"] for record in built})
    wall_path = longest_weighted_path(graph, {record["module"]: record["timing"]["wall_s"] for record in built})
    return {"cumulative_file_cpu_s": cpu, "cumulative_file_wall_s": wall,
            "cpu_ms_per_code_line": cpu * 1000 / code_lines if code_lines else None,
            "timing_visible_fraction": len(built) / len(graph) if graph else 0,
            "heavy_tail_wall_tiers": {str(tier): sum(record["timing"]["wall_s"] >= tier for record in built)
                                      for tier in (10, 20, 30, 40)},
            "top_30": [{"module": record["module"], **record["timing"]} for record in ordered[:30]],
            "per_namespace": dict(namespace), "critical_path_cpu": cpu_path,
            "critical_path_wall": wall_path, "host_cores": cores,
            "host_work_floor_s": cpu / cores, "serial_work_floor_s": cpu,
            "ideal_host_parallel_cpu_lower_bound_s": max(cpu / cores, cpu_path["seconds"]),
            "host_bound": "chain" if cpu_path["seconds"] >= cpu / cores else "work",
            "bound_caveat": "Build driver is serial. Host-core bounds are hypothetical scheduling bounds, not its observed schedule."}


def markdown_report(summary: dict, prior: dict | None) -> str:
    provenance = summary["provenance"]
    tree, own = summary["size"]["git_tree"], summary["size"]["working_build_scope"]
    build, aggregate = summary.get("build", {}), summary.get("aggregate", {})
    timing = build.get("timing", {})
    lines = [f"# Elaboration report — {provenance['started_utc'][:10]} ({summary['label']})", "",
             "## Setup and provenance", "", f"Window: {provenance['started_utc']} to {provenance['finished_utc']}.",
             f"Commit: `{provenance['commit']}`. Host: `{provenance['host']}` ({provenance['platform']}).",
             f"Pinned compiler: `{provenance['compiler']}`; {provenance['compiler_version']}.",
             f"Timing: `{provenance['time_bin']}`; {provenance['time_version'].splitlines()[0]}.",
             f"RSS interpretation: {provenance['rss_interpretation']}", "",
             "The existing `./build.sh` recompiles every own module in serial order; no cache was removed.",
             "Dependency oleans are inputs. Their initial/final stat manifests are retained separately.",
             f"Initial co-running Lean/Lake processes: {process_inventory_description(provenance['processes_before'])}; final: {process_inventory_description(provenance['processes_after'])}. Presence or unavailable process visibility alone does not invalidate this run.",
             "", "## Size snapshot", "",
             "| Scope | Lean files | Counted files | Physical lines | Non-comment code lines | Comment-only excluded |",
             "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for title, snapshot in (("Git commit tree", tree), ("Git tree own build scope", summary["size"]["git_build_scope"]),
                            ("Measured working own scope", own)):
        lines.append(f"| {title} | {snapshot['lean_files_in_scope']} | {snapshot['counted_files']} | {snapshot['total_lines']} | {snapshot['code_lines']} | {len(snapshot['comment_only_files'])} |")
    lines += ["", "The full git tree includes mirrors, comparator challenges and verification probes that the production build does not compile. Cost per line uses the measured own scope.",
              f"Legacy own files without a `module` header: {len(own['legacy_nonmodule_files'])}. They are recorded in JSON; this measurement does not migrate module syntax.",
              f"Dirty status at start: `{provenance['git_status_before'] or '(clean)'}`.", "", "## Headline", "",
              "| Metric | This run | Prior run |", "| --- | ---: | ---: |"]
    metrics = (("Build wall seconds", timing.get("wall_s"), "wall_s"), ("User CPU seconds", timing.get("user_s"), "user_s"),
               ("System CPU seconds", timing.get("sys_s"), "sys_s"), ("CPU percent", timing.get("percent_cpu"), "percent_cpu"),
               ("Peak RSS (raw GNU field)", timing.get("max_rss_raw"), "max_rss_raw"))
    for name, value, key in metrics:
        old = prior.get("build", {}).get("timing", {}).get(key) if prior else None
        lines.append(f"| {name} | {value if value is not None else 'unavailable'} | {old if old is not None else '—'} |")
    lines += [f"| Measured jobs | {summary['coverage']['measured']}/{summary['coverage']['expected']} | — |",
              f"| Cumulative own-file CPU seconds | {aggregate.get('cumulative_file_cpu_s', 'unavailable')} | {prior.get('aggregate', {}).get('cumulative_file_cpu_s', '—') if prior else '—'} |",
              f"| CPU milliseconds per own code line | {aggregate.get('cpu_ms_per_code_line', 'unavailable')} | {prior.get('aggregate', {}).get('cpu_ms_per_code_line', '—') if prior else '—'} |",
              f"| Own CPU / full build wall | {summary.get('observed_cpu_parallelism', 'unavailable')} | — |", "",
              "Every own compiler invocation is timed, including jobs under one second. Module CPU is GNU user + system time, not a Lake progress-line estimate.",
              "", "## Build health", "", f"Validity: **{'valid' if summary['valid'] else 'INVALID'}**. Build exit: {build.get('returncode', 'unavailable')}.",
              f"Errors: {summary['health']['error_count']}; warnings: {summary['health']['warning_count']}; sorry warnings: {summary['health']['sorry_warning_count']}.",
              f"Authorized sorry modules: {', '.join(summary['health']['allowed_sorry_modules']) or 'none'}.",
              f"Unauthorized static sorry/admit tokens: {summary['health']['unauthorized_sorry_tokens']}.",
              f"Coverage: `{json.dumps(summary['coverage'], sort_keys=True)}`.",
              f"Warning census: `{json.dumps(summary['health']['warning_kinds'], sort_keys=True)}`."]
    if summary["invalid_reasons"]:
        lines += ["", *["- " + reason for reason in summary["invalid_reasons"]]]
    lines += ["", "## Heavy tail", "", "| Per-module wall threshold | Files | Delta vs prior |", "| --- | ---: | ---: |"]
    for tier, count in aggregate.get("heavy_tail_wall_tiers", {}).items():
        old = prior.get("aggregate", {}).get("heavy_tail_wall_tiers", {}).get(tier) if prior else None
        lines.append(f"| ≥{tier}s | {count} | {count - old if old is not None else '—'} |")
    lines += ["", "| Top files | Wall seconds | CPU seconds | Delta wall vs prior |", "| --- | ---: | ---: | ---: |"]
    prior_files = {item["module"]: item for item in prior.get("aggregate", {}).get("top_30", [])} if prior else {}
    for item in aggregate.get("top_30", []):
        old = prior_files.get(item["module"], {}).get("wall_s")
        delta = f"{item['wall_s'] - old:+.2f}" if old is not None else "—"
        lines.append(f"| `{item['module']}` | {item['wall_s']:.2f} | {item['cpu_s']:.2f} | {delta} |")
    lines += ["", "## Module-family cost", "", "| File-family prefix | Files | CPU seconds | Wall seconds | Delta CPU |", "| --- | ---: | ---: | ---: | ---: |"]
    for name, item in sorted(aggregate.get("per_namespace", {}).items(), key=lambda entry: entry[1]["cpu_s"], reverse=True):
        old = prior.get("aggregate", {}).get("per_namespace", {}).get(name, {}).get("cpu_s") if prior else None
        delta = f"{item['cpu_s'] - old:+.2f}" if old is not None else "—"
        lines.append(f"| `{name}` | {item['files']} | {item['cpu_s']:.2f} | {item['wall_s']:.2f} | {delta} |")
    lines += ["", "## Warm own-file profiles", "", "Profiles run one at a time after the complete build, without writing oleans.",
              "", "| Module | Warm wall seconds | Dominant phase | Categorized phase seconds |", "| --- | ---: | --- | --- |"]
    for record in summary["profiles"]:
        phases = "; ".join(f"{name}: {value:.3f}" for name, value in sorted(record["profile"]["phases_s"].items(), key=lambda entry: entry[1], reverse=True))
        lines.append(f"| `{record['module']}` | {record['timing']['wall_s']:.2f} | {record['profile']['dominant_phase'] or 'unrecognized'} | {phases or 'inspect raw log'} |")
    lines += ["", "## Findings ranked by actionability", ""]
    for record in sorted(summary["profiles"], key=lambda item: item["profile"]["categorized_s"], reverse=True):
        lines.append(f"- `{record['module']}`: {profile_finding(record)}")
    if not summary["profiles"]:
        lines.append("No warm profile conclusions are available.")
    if aggregate:
        lines += ["", f"Host work floor ({aggregate['host_cores']} cores): {aggregate['host_work_floor_s']:.2f}s. CPU-weighted import chain: {aggregate['critical_path_cpu']['seconds']:.2f}s. Hypothetical host scheduling is {aggregate['host_bound']}-bound; the measured driver itself is serial.",
                  "", "CPU-weighted chain: " + " → ".join(f"`{name}`" for name in aggregate["critical_path_cpu"]["modules"]),
                  "", f"Wall-weighted chain: {aggregate['critical_path_wall']['seconds']:.2f}s."]
    lines += ["", "Measurement only; no elaboration improvement is applied by this harness.", "", "## What is not established", "",
              "Warm phase totals need not sum to wall time: startup, serialization and other work are not all categorized. Unattributed elaboration is not a proof-tactic diagnosis. Events under Lean's profiler threshold are absent from individual listings.",
              "Peak RSS is a maximum, not a sum across files. The full-build number includes the Python and wrapper processes. Compiler startup and wrapper/guard overhead are included in full-build wall time.",
              "Dependency guards compare stat provenance before/after; they do not prove that a mutation was made and perfectly restored between snapshots. Own sources are stat-polled and hash-checked. Other processes are disclosed, not treated as evidence of contamination.",
              "Two snapshots do not establish a monotonic trend. Family labels use the first CamelCase component of the flat module filename (for example Haar or Operational); they are not parsed Lean namespace declarations.",
              "", "## Methodology", "", "```sh", shlex.join(provenance["invocation"]),
              "# Actual timed full-build command", shlex.join(build.get("command", [])), "```", "",
              "Per-module raw stdout/stderr and GNU time output are in `logs/` and `timings/`; exact compiler commands are in `measurements.jsonl`. `summary.json` retains source hashes, build coverage, phase events, dependency provenance pointers and guard outcomes.",
              "", "## Pointers", "", f"Prior summary: `{summary.get('prior_summary') or 'none'}`.", ""]
    if summary.get("comparison"):
        lines += ["Comparability: " + summary["comparison"]["note"], ""]
    return "\n".join(lines)


def run(args: argparse.Namespace) -> int:
    root = ROOT
    output = args.output.expanduser().resolve()
    if output.exists() and any(output.iterdir()):
        raise RuntimeError("Output directory must be new or empty: " + str(output))
    if output.is_relative_to(root / ".lake") or output.is_relative_to(root / "Nonadditivity"):
        raise RuntimeError("Measurement output cannot be inside source or build/dependency trees")
    output.mkdir(parents=True, exist_ok=True)
    for directory in ("logs", "timings"):
        (output / directory).mkdir()
    pin = (root / "lean-toolchain").read_text().strip()
    compiler = (args.compiler or Path.home() / ".elan/toolchains" / pin.replace("/", "--").replace(":", "---") / "bin/lean").expanduser().resolve()
    time_bin = args.time_bin.expanduser().resolve()
    for name, path in (("compiler", compiler), ("GNU time", time_bin)):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise RuntimeError(f"Missing executable {name}: {path}")
    time_version = captured([str(time_bin), "--version"])
    if "GNU" not in time_version:
        raise RuntimeError("--time-bin must be GNU time supporting -v and -o")
    compiler_version = captured([str(compiler), "--version"])
    expected_version = pin.split(":")[-1].lstrip("v")
    if "version " + expected_version + "," not in compiler_version:
        raise RuntimeError("Compiler does not match lean-toolchain: " + compiler_version)
    modules = own_modules(root)
    if not modules or "Audit" not in modules:
        raise RuntimeError("Missing own modules or required Audit root")
    # The measured source must equal a committed snapshot. Untracked harness
    # output and unrelated files do not prevent the run.
    dirty_scope = captured(["git", "diff", "--name-only", "HEAD", "--", "Nonadditivity",
                            "Nonadditivity.lean", "Audit.lean", "All.lean", *DRIVER_FILES])
    if dirty_scope:
        raise RuntimeError("Commit own-source/driver edits before measurement: " + dirty_scope.replace("\n", ", "))
    tracked_sources = subprocess.run(["git", "ls-files", "-z", "--", "Nonadditivity",
                                     "Nonadditivity.lean", "Audit.lean", "All.lean"],
                                    cwd=root, check=True, stdout=subprocess.PIPE).stdout
    tracked = {entry.decode() for entry in tracked_sources.split(b"\0") if entry}
    untracked_sources = sorted(set(modules.values()) - tracked)
    if untracked_sources:
        raise RuntimeError("Commit new own Lean sources before measurement: " + ", ".join(untracked_sources))
    graph, external = import_graph(root, modules)
    order = topological_order(graph)
    closure: set[str] = set()
    def reachable(name: str) -> None:
        if name not in closure:
            closure.add(name)
            for dependency in graph[name]:
                reachable(dependency)
    reachable("All" if "All" in modules else "Audit")
    if set(modules) != closure:
        raise RuntimeError("Default audit root omits own modules: " + ", ".join(sorted(set(modules) - closure)))
    commit = captured(["git", "rev-parse", "HEAD"])
    texts = git_tree_texts(root, commit)
    working = {relative: (root / relative).read_text() for relative in modules.values()}
    source_stats, source_hashes = source_stat_manifest(root), source_hash_manifest(root)
    build_root = (root / ".lake/build/lib/lean").resolve()
    if build_root != root / ".lake/build/lib/lean":
        raise RuntimeError("Own build subtree must not be redirected by a symlink")
    for relative in modules.values():
        destination = build_root / Path(relative).with_suffix(".olean")
        if destination.resolve() != destination:
            raise RuntimeError("Own artifact destination must not be redirected by a symlink: " + relative)
    dependencies = dependencies_snapshot(root, compiler, external)
    write_json(output / "dependencies-before.json", dependencies)
    artifact_before = own_artifact_manifest(root)
    write_json(output / "artifacts-before.json", artifact_before)
    write_json(output / "artifact-state.json", artifact_before)
    config = {"root": str(root), "output": str(output), "compiler": str(compiler),
              "time_bin": str(time_bin), "phase": "build", "modules": modules,
              "source_stats": source_stats, "source_hashes": source_hashes}
    config_path = output / "wrapper-config.json"
    write_json(config_path, config)
    wrapper = output / "timed-compiler"
    wrapper.write_text("#!" + sys.executable + "\nimport subprocess, sys\n"
                       "sys.exit(subprocess.run(" + repr([sys.executable, str(Path(__file__).resolve()),
                       "_compiler", str(config_path)]) + " + sys.argv[1:]).returncode)\n")
    wrapper.chmod(0o755)
    source_sorries = {name: len(re.findall(r"\b(?:sorry|admit)\b", lexical_code(working[relative], hide_strings=True)))
                      for name, relative in modules.items()}
    allowed = sorted(set(args.allow_sorry_module))
    if set(allowed) - modules.keys():
        raise RuntimeError("Unknown authorized sorry module")
    unauthorized = sum(count for name, count in source_sorries.items() if name not in allowed)
    time_config = time_bin.parent / "config.h"
    rss_normalized = (time_config.is_file() and
                      re.search(r"^#define GETRUSAGE_RETURNS_BYTES 1$", time_config.read_text(), re.M) is not None)
    provenance = {"started_utc": utc_now(), "commit": commit,
                  "git_status_before": captured(["git", "status", "--short"]),
                  "compiler": str(compiler), "compiler_sha256": digest(compiler), "compiler_version": compiler_version,
                  "pin": pin, "time_bin": str(time_bin), "time_sha256": digest(time_bin), "time_version": time_version,
                  "host": socket.gethostname(), "platform": platform.platform(), "cores": args.cores,
                  "time_config_sha256": digest(time_config) if time_config.is_file() else None,
                  "darwin_rusage_bytes_normalized": rss_normalized,
                  "rss_interpretation": ("GNU time reports KiB. Its config.h enables GETRUSAGE_RETURNS_BYTES, normalizing Darwin's native byte-valued ru_maxrss."
                                         if platform.system() == "Darwin" and rss_normalized else
                                         "GNU time raw maxrss is retained. Darwin's native ru_maxrss is bytes; without build-configuration evidence confirm normalization before comparing it to Linux."
                                         if platform.system() == "Darwin" else "GNU time maxrss is reported in KiB on this Linux host."),
                  "processes_before": process_inventory(), "invocation": [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
                  "driver_parallelism": 1, "NONADDITIVITY_PARALLEL": "0",
                  "lean_internal_threads": "Compiler default; no -j override (same pinned compiler for both runs)",
                  "scope": "build.sh own modules; all compiled serially without deleting caches"}
    summary = {"schema_version": 1, "label": args.label, "provenance": provenance,
               "size": {"git_tree": size_snapshot(texts),
                        "git_build_scope": size_snapshot({name: text for name, text in texts.items() if name in working}),
                        "working_build_scope": size_snapshot(working)},
               "modules": modules, "import_graph": graph, "source_hashes_before": source_hashes,
               "source_stats_before": source_stats, "source_sorry_tokens": source_sorries,
               "dependency_manifests": {"before": str(output / "dependencies-before.json"),
                                        "after": str(output / "dependencies-after.json")},
               "dependency_olean_count": dependencies["olean_count"], "invalid_reasons": [], "profiles": [],
               "prior_summary": str(args.prior_summary.resolve()) if args.prior_summary else None}
    write_json(output / "snapshot-before.json", summary)
    env = os.environ.copy()
    env.update({"LC_ALL": "C", "NONADDITIVITY_LEAN": str(wrapper), "NONADDITIVITY_PARALLEL": "0",
                # compiler.py cannot silently substitute `lake env lean`.
                "NONADDITIVITY_LEAN_PATH": str(compiler.parent.parent / "lib/lean")})
    command = [str(time_bin), "-v", "-o", str(output / "build.time.txt"), str(root / "build.sh")]
    build_returncode = None
    try:
        if unauthorized:
            raise RuntimeError(f"Unauthorized sorry/admit tokens in own sources: {unauthorized}")
        build_returncode = guarded_subprocess(command, output / "build.log", config, env)
        if build_returncode:
            summary["invalid_reasons"].append(f"Build exited with {build_returncode}")
        build_records = [json.loads(line) for line in (output / "measurements.jsonl").read_text().splitlines()]
        coverage = coverage_check(order, build_records)
        if not coverage["complete"]:
            summary["invalid_reasons"].append("Full own-module build coverage/order was not established")
        if build_returncode == 0 and coverage["complete"]:
            config["phase"] = "profile"
            write_json(config_path, config)
            candidates = sorted(build_records, key=lambda record: record["timing"]["wall_s"], reverse=True)[:args.profile_count]
            for record in candidates:
                print("Warm profiling " + record["module"], flush=True)
                profile_command = [str(root / "lean.sh"), "--profile", record["source"]]
                returncode = guarded_subprocess(profile_command, output / ("profile-driver-" + record["module"] + ".log"), config, env)
                if returncode:
                    summary["invalid_reasons"].append(f"Warm profile failed: {record['module']} ({returncode})")
                    break
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        summary["invalid_reasons"].append(str(error))
    except KeyboardInterrupt:
        summary["invalid_reasons"].append("Run interrupted")
    final_records = [json.loads(line) for line in (output / "measurements.jsonl").read_text().splitlines()] if (output / "measurements.jsonl").is_file() else []
    summary["coverage"] = coverage_check(order, final_records)
    if not summary["coverage"]["complete"] and "Full own-module build coverage/order was not established" not in summary["invalid_reasons"]:
        summary["invalid_reasons"].append("Full own-module build coverage/order was not established")
    summary["build"] = {"returncode": build_returncode, "command": command,
                        "log": str(output / "build.log"), "time_log": str(output / "build.time.txt")}
    if (output / "build.time.txt").is_file():
        try:
            summary["build"]["timing"] = parse_gnu_time((output / "build.time.txt").read_text())
        except ValueError as error:
            summary["invalid_reasons"].append(str(error))
    summary["profiles"] = [record for record in final_records if record["phase"] == "profile"]
    for record in summary["profiles"]:
        if not record["profile"]["phases_s"]:
            summary["invalid_reasons"].append("Warm profile cumulative phase totals were not recognized: " + record["module"])
    summary["aggregate"] = aggregation(final_records, graph, summary["size"]["working_build_scope"]["code_lines"], args.cores)
    build_wall = summary["build"].get("timing", {}).get("wall_s", 0)
    summary["observed_cpu_parallelism"] = summary["aggregate"]["cumulative_file_cpu_s"] / build_wall if build_wall else None
    health = {"warning_count": 0, "error_count": 0, "sorry_warning_count": 0, "warning_kinds": Counter(),
              "allowed_sorry_modules": allowed, "unauthorized_sorry_tokens": unauthorized}
    for record in final_records:
        summary["invalid_reasons"].extend(record["guard_errors"])
        if record["phase"] != "build":
            continue
        for key in ("warning_count", "error_count", "sorry_warning_count"):
            health[key] += record["diagnostics"][key]
        health["warning_kinds"].update(record["diagnostics"]["warning_kinds"])
        if record["diagnostics"]["sorry_warning_count"] and record["module"] not in allowed:
            summary["invalid_reasons"].append("Unauthorized sorry warning: " + record["module"])
    health["warning_kinds"] = dict(health["warning_kinds"])
    summary["health"] = health
    try:
        hashes_after = source_hash_manifest(root)
        summary["source_hashes_after"] = hashes_after
        source_changes = manifest_changes(source_hashes, hashes_after)
        stat_changes = manifest_changes(source_stats, source_stat_manifest(root))
        summary["source_changes"] = source_changes
        if source_changes or stat_changes:
            summary["invalid_reasons"].append("Own source/driver mutation: " + ", ".join(sorted(set(source_changes + stat_changes))))
        dependencies_after = dependencies_snapshot(root, compiler, external)
        write_json(output / "dependencies-after.json", dependencies_after)
        dependency_changes = manifest_changes(dependencies["artifacts"], dependencies_after["artifacts"])
        summary["dependency_artifact_changes"] = dependency_changes
        if dependency_changes:
            summary["invalid_reasons"].append(f"Upstream artifact provenance changed: {len(dependency_changes)} artifacts")
        artifact_after = own_artifact_manifest(root)
        write_json(output / "artifacts-after.json", artifact_after)
        unexpected = manifest_changes(read_json(output / "artifact-state.json"), artifact_after)
        if unexpected:
            summary["invalid_reasons"].append("Own artifacts changed outside last compiler invocation: " + ", ".join(unexpected))
    except (OSError, RuntimeError) as error:
        summary["invalid_reasons"].append("Final provenance guard failed: " + str(error))
    provenance.update({"finished_utc": utc_now(), "git_status_after": captured(["git", "status", "--short"]),
                       "processes_after": process_inventory()})
    prior = read_json(args.prior_summary) if args.prior_summary else None
    if prior:
        old = prior["provenance"]
        matched = all(provenance[key] == old.get(key) for key in ("compiler_sha256", "time_sha256", "cores", "host"))
        summary["comparison"] = {"matched_timing_setup": matched,
                                 "note": ("Compiler, GNU time, core count and host match; processes and warm caches can still introduce noise."
                                          if matched else "Timing setup differs; wall/RSS trends are not directly comparable. Use per-file CPU with caveats.")}
    summary["invalid_reasons"] = list(dict.fromkeys(summary["invalid_reasons"]))
    summary["valid"] = not summary["invalid_reasons"]
    write_json(output / "summary.json", summary)
    report_path = output / f"ELABORATION_REPORT_{provenance['started_utc'][:10]}_{args.label}.md"
    report_path.write_text(markdown_report(summary, prior))
    print(f"{'VALID' if summary['valid'] else 'INVALID'}: {report_path}", flush=True)
    return 0 if summary["valid"] else 1


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "_compiler":
        try:
            return compiler_entry(Path(sys.argv[2]), sys.argv[3:])
        except Exception as error:
            print("ELABORATION GUARD ERROR: " + str(error), file=sys.stderr, flush=True)
            return 97
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--label", required=True, choices=("before", "after"))
    parser.add_argument("--output", required=True, type=Path, help="New/empty run directory")
    parser.add_argument("--time-bin", required=True, type=Path, help="Absolute GNU time executable")
    parser.add_argument("--compiler", type=Path, help="Actual pinned Lean executable; defaults to the elan toolchain binary")
    parser.add_argument("--profile-count", type=int, choices=range(5, 11), default=8)
    parser.add_argument("--cores", type=int, default=os.cpu_count() or 1, help="Host cores for hypothetical scheduling floor")
    parser.add_argument("--prior-summary", type=Path, help="Prior summary.json for comparable trend columns")
    parser.add_argument("--allow-sorry-module", action="append", default=[], help="Explicit authorized own module; default policy permits no sorry/admit")
    args = parser.parse_args()
    if args.cores < 1:
        parser.error("--cores must be positive")
    try:
        return run(args)
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("Elaboration precondition failed: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
