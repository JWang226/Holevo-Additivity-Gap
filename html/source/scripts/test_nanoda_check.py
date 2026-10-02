#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# Original QMDL attribution/licensing: https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/NOTICE
# Copyright (c) 2026 the Nonadditivity project contributors (adaptations).
# See COPYRIGHT.md for this project’s attribution and licensing status.
# Adapted for Holevo-Additivity-Gap from JWang226/QMDL at fd36df94068299e3d5e0bb193d19649319a40422; original attribution retained.
"""Exercise the hardened wrapper with genuine Lean exports and the real kernel.

Run after building lean4export in a pinned Lean project:
  python3 scripts/test_nanoda_check.py --lake-project /path/to/lean \
    --nanoda-bin /path/to/nanoda_bin

Only temporary fixture sources/exports are written. Existing project proof
artifacts are neither rebuilt nor changed. No success evidence is restamped.
"""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-project", type=Path, required=True)
    parser.add_argument("--nanoda-bin", type=Path, required=True)
    args = parser.parse_args()
    project = args.lake_project.resolve()
    binary = args.nanoda_bin.resolve()
    lake = shutil.which("lake")
    if lake is None or not binary.is_file():
        parser.error("lake and a real, already-built Nanoda binary are required")
    helper = Path(__file__).resolve().parents[1] / "verification/nanoda/check_nanoda.py"
    spec = importlib.util.spec_from_file_location("nanoda_check", helper)
    check = importlib.util.module_from_spec(spec)
    # Avoid even a Python bytecode cache in the repository.
    exec(compile(helper.read_bytes(), str(helper), "exec"), check.__dict__)
    checker, exporter = check.common.prepare_comparator()
    if not exporter.is_file():
        parser.error("Build the pinned lean4export first; this test does not build dependencies")

    def command(argv, **kwargs):
        return subprocess.run(argv, cwd=project, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=180, **kwargs)

    paths = command([lake, "env", "printenv", "LEAN_PATH"], check=True).stdout.decode().strip()
    axioms = ["propext", "Quot.sound", "Classical.choice"]
    outcomes = []
    with tempfile.TemporaryDirectory(prefix="holevo-nanoda-controls-", dir="/tmp") as temporary:
        work = Path(temporary)
        source = work / "NanodaRegression.lean"
        source.write_text("""import Init
namespace NanodaRegression
theorem good : True := True.intro
axiom forbidden : False
theorem badAxiom : False := forbidden
theorem proofHole : False := by sorry
def definitionRoot : Prop := True
end NanodaRegression
""")
        command([lake, "env", "lean", "-R", str(work), "-o", str(work / "NanodaRegression.olean"),
                 str(source)], check=True)
        environment = dict(os.environ, LEAN_PATH=str(work) + os.pathsep + paths)

        def export(name, label):
            roots = check.BUILTINS + [name] + axioms + check.PRIMITIVES + check.QUOTIENTS
            result = command([str(exporter), "NanodaRegression", "--", *roots], env=environment)
            path = work / (label + ".export")
            path.write_bytes(result.stdout)
            return path, result

        def kernel(path, names):
            config = work / "kernel.json"
            config.write_text(json.dumps(check.kernel_options(names, axioms)))
            return command([str(binary), str(config)], input=path.read_bytes())

        def reject_root(path, names):
            try:
                check.require_exported_theorems(path, names)
            except ValueError:
                return
            raise AssertionError("Wrapper accepted a missing or non-theorem root")

        def comparator(expected, solution, names, accept, label):
            config = work / "comparator.json"
            config.write_text(json.dumps({"challenge_module": "NanodaRegression",
                "solution_module": "NanodaRegression", "theorem_names": names,
                "permitted_axioms": axioms, "enable_nanoda": False}))
            result = subprocess.run([lake, "env", "lean", "--run",
                str(check.common.ROOT / "verification/comparator/ReplayExports.lean"),
                str(config), str(expected), str(solution)], cwd=checker,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180,
                env=dict(os.environ, LEAN_ABORT_ON_PANIC="1"))
            if (result.returncode == 0) != accept:
                raise AssertionError(label + ": " + result.stdout.decode() + result.stderr.decode())
            outcomes.append("Comparator: " + label)

        good_name = "NanodaRegression.good"
        good, result = export(good_name, "valid")
        if result.returncode != 0:
            raise AssertionError(result.stderr.decode())
        check.require_exported_theorems(good, [good_name])
        result = kernel(good, [good_name])
        if result.returncode != 0:
            raise AssertionError("Valid theorem rejected: " + result.stderr.decode())
        outcomes.append("valid theorem accepted")
        comparator(good, good, [good_name], True, "valid theorem accepted")

        missing_name = "NanodaRegression.missing"
        missing, result = export(missing_name, "missing")
        reject_root(missing, [missing_name])
        if kernel(missing, [missing_name]).returncode == 0:
            raise AssertionError("Real kernel accepted an export without its requested target")
        outcomes.append("missing target rejected by wrapper and kernel")
        comparator(missing, missing, [missing_name], False, "missing target rejected")

        name = "NanodaRegression.definitionRoot"
        definition, result = export(name, "definition")
        if result.returncode != 0:
            raise AssertionError(result.stderr.decode())
        reject_root(definition, [name])
        outcomes.append("non-theorem root rejected")

        for short in ("badAxiom", "proofHole"):
            name = "NanodaRegression." + short
            path, result = export(name, short)
            if result.returncode != 0:
                raise AssertionError(result.stderr.decode())
            check.require_exported_theorems(path, [name])
            result = kernel(path, [name])
            if result.returncode == 0:
                raise AssertionError("Kernel accepted forbidden proof dependency: " + short)
            forbidden = "NanodaRegression.forbidden" if short == "badAxiom" else "sorryAx"
            if forbidden not in result.stderr.decode():
                raise AssertionError("Negative failed for an unexpected reason: " + result.stderr.decode())
            outcomes.append(short + " rejected by real kernel axiom policy")
            comparator(path, path, [name], False, short + " rejected by axiom policy")

        # Corrupt the actual valid proof term while preserving its theorem name
        # and dependency table. This must reach the typechecker, not fail the
        # wrapper's presence check or an axiom allowlist check.
        records = [json.loads(line) for line in good.read_text().splitlines()]
        exported_names = {0: ""}
        for record in records:
            if "in" in record:
                part = record.get("str", record.get("num"))
                suffix = part.get("str", str(part.get("i")))
                prefix = exported_names[part["pre"]]
                exported_names[record["in"]] = prefix + ("." if prefix else "") + suffix
        proof = next(record["thm"] for record in records
                     if "thm" in record and exported_names[record["thm"]["name"]] == good_name)
        proof["value"] = proof["type"]
        corrupt = work / "ill-typed.export"
        corrupt.write_text("\n".join(json.dumps(record) for record in records) + "\n")
        check.require_exported_theorems(corrupt, [good_name])
        result = kernel(corrupt, [good_name])
        if result.returncode == 0:
            raise AssertionError("Kernel accepted an ill-typed proof term")
        if "assertion failed: self.def_eq" not in result.stderr.decode():
            raise AssertionError("Corrupt proof failed for an unexpected reason: " + result.stderr.decode())
        outcomes.append("ill-typed proof rejected by real kernel")
        comparator(good, corrupt, [good_name], False, "ill-typed proof rejected")

        # Same theorem name, different expected proposition: comparison must fail.
        source.write_text("import Init\nnamespace NanodaRegression\ntheorem good : False := by sorry\nend NanodaRegression\n")
        command([lake, "env", "lean", "-R", str(work), "-o", str(work / "NanodaRegression.olean"),
                 str(source)], check=True)
        mismatch, result = export(good_name, "mismatched-statement")
        if result.returncode != 0:
            raise AssertionError(result.stderr.decode())
        comparator(mismatch, good, [good_name], False, "mismatched expected statement rejected")

    for names in ([], ["same", "same"], [""], [" spaced"], ["A..B"]):
        try:
            check.theorem_names({"theorem_names": names})
        except ValueError:
            continue
        raise AssertionError("Invalid target selection accepted: " + repr(names))
    outcomes.append("empty, duplicate, and malformed target selections rejected")
    print(json.dumps({"status": "passed", "checks": outcomes}, indent=2))


if __name__ == "__main__":
    main()
