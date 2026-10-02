#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# Original QMDL attribution/licensing: https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/NOTICE
# Copyright (c) 2026 the Nonadditivity project contributors (adaptations).
# See COPYRIGHT.md for this project’s attribution and licensing status.
# Adapted for Holevo-Additivity-Gap from JWang226/QMDL at fd36df94068299e3d5e0bb193d19649319a40422; original attribution retained.
"""Unsandboxed Comparator diagnostic; never report a secure Comparator pass."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification"))
import kernel_common as common
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
]


def run(args, **kwargs):
    common.run(args, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    parser.add_argument("configs", nargs="*")
    args = parser.parse_args()
    if args.report and args.report.exists():
        parser.error("Use a fresh report path")
    snapshot = common.bindings()
    outcomes = {}
    configs = args.configs or common.DEFAULT_CONFIGS
    common.validate_configs(configs)
    print("UNSANDBOXED local diagnostic; Landrun is not run; Nanoda is disabled.", flush=True)
    directory, exporter = common.prepare_comparator()
    for config_name in configs:
        config_path = ROOT / config_name
        config = json.loads(config_path.read_text())
        if config["enable_nanoda"]:
            raise SystemExit("Local diagnostic does not support nanoda.")
        run(["lake", "build", config["challenge_module"], config["solution_module"]])
        targets = config["theorem_names"] + config["permitted_axioms"] + PRIMITIVES
        with tempfile.TemporaryDirectory(prefix="holevo-comparator-") as temp:
            exports = []
            for side in ["challenge", "solution"]:
                out = Path(temp) / f"{side}.export"
                print(f"Exporting {side}: {config[side + '_module']}", flush=True)
                with out.open("w") as handle:
                    run(["lake", "env", str(exporter), config[side + "_module"],
                         "--", *targets], stdout=handle)
                exports.append(str(out))
            common.replay(directory, config_path, *exports)
            outcomes[config_path.relative_to(ROOT).as_posix()] = {"status": "passed", "theorem_names": config["theorem_names"], "config_sha256": common.digest(config_path), "solution_export_sha256": common.digest(Path(exports[1])), "solution_export_bytes": Path(exports[1]).stat().st_size}
        print(f"LOCAL DIAGNOSTIC PASSED: {config_name}", flush=True)

    record = common.report("unsandboxed_comparator_lean_replay", outcomes, snapshot)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
