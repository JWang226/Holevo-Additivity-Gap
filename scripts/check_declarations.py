#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Check mapped declarations against the compiled Lean environment.

This checks existence, declared source module, theorem/definition role, and
transitive axioms. It does not replace the complete Audit.lean or Comparator.
Run after building the proof library; logs and generated input stay in .lake/.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys


NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def check_declarations(root: Path, results: dict) -> int:
    references: dict[str, tuple[str, str]] = {}
    for result in results["results"]:
        for ref in result["lean"]:
            name = ref["declaration"]
            source = Path(ref["file"])
            module = ".".join(source.with_suffix("").parts)
            if not NAME.fullmatch(name) or not NAME.fullmatch(module):
                raise ValueError(f"Unsupported declaration/module name: {name}, {module}")
            value = (module, ref["role"])
            if name in references and references[name] != value:
                raise ValueError(f"Inconsistent metadata references for {name}")
            references[name] = value
    if not references:
        raise ValueError("The metadata contains no Lean declarations")

    lines = [
        "/- Generated declaration validation input; not part of the proof library. -/",
        "import Nonadditivity",
        "import Lean.Util.CollectAxioms",
        "open Lean Elab Command",
    ]
    for name in sorted(references):
        lines.append(f"#check @{name}")
    lines += ["run_cmd do", "  let env ← getEnv", "  let refs : Array (Name × Name × Bool) := #["]
    entries = []
    for name, (module, role) in sorted(references.items()):
        theorem = "true" if role == "theorem" else "false"
        entries.append(f"    (``{name}, `{module}, {theorem})")
    lines.append(",\n".join(entries))
    lines += [
        "  ]",
        "  for (name, expectedModule, isTheorem) in refs do",
        "    let info ← getConstInfo name",
        "    if isTheorem then",
        "      unless (match info with | .thmInfo _ => true | _ => false) do",
        '        throwError "Expected a theorem: {name}"',
        "    else",
        "      unless (match info with | .defnInfo _ => true | _ => false) do",
        '        throwError "Expected a definition: {name}"',
        "    let actualModule ← findModuleOf? name",
        "    unless actualModule == some expectedModule do",
        '      throwError "Wrong source module for {name}: {actualModule}; expected {expectedModule}"',
        "  let names := refs.map (·.1)",
        "  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}",
        "  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]",
        "  let unexpected := state.axioms.filter (fun a => !allowed.contains a)",
        "  unless unexpected.isEmpty do",
        '    throwError "Unexpected mapped declaration axioms: {unexpected}"',
        '  logInfo m!"DECLARATIONS PASSED: {refs.size} exact names, source modules, roles, and transitive axioms."',
        "",
    ]
    scratch = root / ".lake"
    scratch.mkdir(exist_ok=True)
    source = scratch / "ReleaseDeclarations.lean"
    log = scratch / "release-declarations.log"
    source.write_text("\n".join(lines), encoding="utf-8")
    with log.open("w", encoding="utf-8") as out:
        proc = subprocess.run(
            [str(root / "lean.sh"), str(source.relative_to(root))],
            cwd=root, stdout=out, stderr=subprocess.STDOUT, check=False,
        )
    output = log.read_text(encoding="utf-8")
    if proc.returncode or "DECLARATIONS PASSED:" not in output:
        errors = [i for i, line in enumerate(output.splitlines()) if "error:" in line]
        lines = output.splitlines()
        start = errors[0] if errors else max(0, len(lines) - 30)
        sys.stderr.write("\n".join(lines[start:]) + "\n")
        raise ValueError(f"Lean declaration validation failed; see {log.relative_to(root)}")
    print(next(line for line in output.splitlines() if "DECLARATIONS PASSED:" in line))
    return len(references)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        results = json.loads((root / "metadata/results.json").read_text(encoding="utf-8"))
        check_declarations(root, results)
    except (OSError, ValueError, KeyError) as exc:
        print(f"DECLARATIONS FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
