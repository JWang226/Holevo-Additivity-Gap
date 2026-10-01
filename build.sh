#!/bin/sh
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
# Compile only this project's files, then audit every transitive proof dependency.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$project_dir"
python3 - "$@" <<'PYTHON'
from pathlib import Path
import os
import re
import subprocess
import sys

root = Path.cwd()
compiler = root / "lean.sh"
modules = {}
for path in (root / "Nonadditivity").rglob("*.lean"):
    modules[".".join(path.relative_to(root).with_suffix("").parts)] = path
for filename in ("Nonadditivity.lean", "Audit.lean", "All.lean"):
    path = root / filename
    if path.exists():
        modules[path.stem] = path

if not modules:
    sys.exit("No project Lean files found.")

imports = {}
for name, path in modules.items():
    imported = []
    for line in path.read_text().splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line)
        if match:
            imported.extend(match.group(1).split("--", 1)[0].split())
    imports[name] = [entry for entry in imported if entry in modules]

order, visited, visiting = [], set(), set()
def visit(name):
    if name in visited:
        return
    if name in visiting:
        sys.exit("Import cycle at " + name)
    visiting.add(name)
    for dependency in imports[name]:
        visit(dependency)
    visiting.remove(name)
    visited.add(name)
    order.append(name)

if "Audit" not in modules:
    sys.exit("Audit.lean is required for a verified build.")
reachable = set()
def audit_closure(name):
    if name in reachable:
        return
    reachable.add(name)
    for dependency in imports[name]:
        audit_closure(dependency)
audit_closure("All" if "All" in modules else "Audit")
missing = sorted(set(modules) - reachable)
if missing:
    sys.exit("Modules not imported by the audit: " + ", ".join(missing))

for name in sorted(modules, key=lambda n: (n == "Audit", n)):
    visit(name)

version = subprocess.run([str(compiler), "--version"], text=True, capture_output=True)
if version.returncode:
    sys.stderr.write(version.stderr)
    sys.exit(version.returncode)
print(version.stdout.strip(), flush=True)
expected = (root / "lean-toolchain").read_text().strip().split(":")[-1].lstrip("v")
if "version " + expected + "," not in version.stdout:
    sys.exit("The compiler does not match lean-toolchain: " + expected)

for name in order:
    source = modules[name]
    relative = source.relative_to(root)
    output = root / ".lake" / "build" / "lib" / "lean" / relative.with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    print("Checking " + str(relative), flush=True)
    result = subprocess.run([str(compiler), "-o", str(output), str(relative), *sys.argv[1:]])
    if result.returncode:
        sys.exit(result.returncode)

print("BUILD PASSED: " + str(len(order)) + " project modules.", flush=True)
PYTHON
