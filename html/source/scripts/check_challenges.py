#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Check challenge elaboration and solution proofs against explicit types.

This is a local Lean check, not Comparator. Existing project and mathlib object
files must be available. Only challenge and scratch modules are compiled.
"""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = Path('.lake/challenge-checks')
REPORT = Path('.lake/challenge-checks.json')
ALLOWED_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}

# Arguments bound in each explicit expected statement. Its type is preserved.
APPLICATIONS = {
    'Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound': ' hK hn',
    'Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum': ' T',
    'Nonadditivity.OperationalConsequences.exists_small_chi_large_capacity_gain_and_two_use_ratio': ' hε A R',
    'Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits': ' T n',
    'Nonadditivity.PrescribedCost.growingFamily_chi_input_cost_bounds': '',
    'Nonadditivity.PrescribedCost.growingFamily_two_use_input_cost_lower': '',
    'Nonadditivity.DeterministicConsequences.actual_small_large': ' hε',
}
# E repeats this exact concrete definition instead of importing either target.
REPEATED_DEFINITION = 'def inputLogScale : ℝ := Real.sqrt (2/Real.log 2)\n'
REPEATED_DEFINITION_SOURCE = Path('Nonadditivity/PrescribedCostScaling.lean')


def digest(path: Path) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def save_report(report: dict) -> None:
    (ROOT / REPORT).write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')


def run_lean(arguments: list[str], log: Path) -> dict:
    command = ['./lean.sh', *arguments]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    (ROOT / log).write_text(result.stdout + result.stderr, encoding='utf-8')
    return {'status': 'passed' if result.returncode == 0 else 'failed',
            'command': command, 'exit_code': result.returncode, 'log': log.as_posix()}


def proof_check_source(source: str, config: dict, stem: str) -> str:
    """Replace only identified theorem bodies, never occurrences in comments."""
    names = config['theorem_names']
    short_names = [name.rsplit('.', 1)[1] for name in names]
    if re.findall(r'^theorem\s+([^\s(:{]+)', source, re.M) != short_names:
        raise ValueError(f'{stem}: theorem declarations differ from configuration order')
    if len(re.findall(r'^  sorry$', source, re.M)) != len(names):
        raise ValueError(f'{stem}: unexpected challenge placeholder layout')
    checked = re.sub(r'^import [^\n]+\n', '', source, flags=re.M)
    if stem == 'E_InputCost':
        if checked.count(REPEATED_DEFINITION) != 1:
            raise ValueError('E_InputCost: repeated concrete definition changed')
        original = (ROOT / REPEATED_DEFINITION_SOURCE).read_text(encoding='utf-8')
        if original.count(REPEATED_DEFINITION) != 1:
            raise ValueError('E_InputCost: solution concrete definition changed')
        checked = checked.replace(REPEATED_DEFINITION, '', 1)
    for full_name, short_name in zip(names, short_names):
        if full_name not in APPLICATIONS:
            raise ValueError(f'{stem}: unknown theorem {full_name}')
        pattern = re.compile(
            r'^theorem ' + re.escape(short_name)
            + r'(?P<type>\b(?:(?!^theorem |^def |^end ).)*?)'
            + r':= by\n  sorry(?=\n)', re.M | re.S)
        matches = list(pattern.finditer(checked))
        if len(matches) != 1:
            raise ValueError(f'{stem}: cannot isolate expected theorem {short_name}')
        match = matches[0]
        replacement = ('theorem checked_' + short_name + match.group('type')
                       + ':= by\n  exact ' + full_name + APPLICATIONS[full_name])
        checked = checked[:match.start()] + replacement + checked[match.end():]
    if re.search(r'^\s*sorry\s*$', checked, re.M):
        raise ValueError(f'{stem}: unexpected proof placeholder remains')
    return 'import ' + config['solution_module'] + '\n' + checked


def main() -> int:
    (ROOT / OUT / 'expected').mkdir(parents=True, exist_ok=True)
    (ROOT / OUT / 'StatementChecks').mkdir(parents=True, exist_ok=True)
    report = {
        'schema_version': 1,
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'running',
        'method': 'local_lean_elaboration_and_solution_against_explicit_expected_type',
        'baseline_modules_recompiled': False,
        'comparator_execution': 'not_run', 'nanoda_execution': 'not_run',
        'intentional_challenge_placeholders': 7, 'checks': [],
    }
    save_report(report)
    seen = set()
    try:
        configs = sorted((ROOT / 'ComparatorChallenges').glob('*.json'))
        if len(configs) != 6:
            raise ValueError('Expected exactly six Comparator configurations')
        for absolute_config in configs:
            config_path = absolute_config.relative_to(ROOT)
            config = json.loads(absolute_config.read_text(encoding='utf-8'))
            stem = config_path.stem
            source_path = config_path.with_suffix('.lean')
            if config['challenge_module'] != 'ComparatorChallenges.' + stem:
                raise ValueError(f'{stem}: challenge module/path mismatch')
            if set(config['permitted_axioms']) != ALLOWED_AXIOMS:
                raise ValueError(f'{stem}: unexpected permitted axioms')
            if config.get('enable_nanoda') is not False:
                raise ValueError(f'{stem}: expected explicit enable_nanoda=false')
            if seen.intersection(config['theorem_names']):
                raise ValueError(f'{stem}: duplicate target theorem')
            seen.update(config['theorem_names'])
            source = (ROOT / source_path).read_text(encoding='utf-8')
            checked_source = proof_check_source(source, config, stem)
            check_path = OUT / 'StatementChecks' / (stem + '.lean')
            (ROOT / check_path).write_text(checked_source, encoding='utf-8')
            item = {
                'config': config_path.as_posix(), 'config_sha256': digest(config_path),
                'challenge_source': source_path.as_posix(),
                'challenge_source_sha256': digest(source_path),
                'theorem_names': config['theorem_names'],
                'generated_statement_check': check_path.as_posix(),
            }
            report['checks'].append(item)
            expected_log = OUT / (stem + '_expected.log')
            item['challenge_elaboration'] = run_lean(
                ['-o', str(OUT / 'expected' / (stem + '.olean')), str(source_path)], expected_log)
            if item['challenge_elaboration']['exit_code']:
                raise RuntimeError(f'{stem}: challenge compilation failed; see {expected_log}')
            proof_log = OUT / (stem + '_statement.log')
            item['proof_against_expected_statement'] = run_lean(
                ['--root=' + str(OUT), str(check_path)], proof_log)
            if item['proof_against_expected_statement']['exit_code']:
                raise RuntimeError(f'{stem}: solution/type check failed; see {proof_log}')
            print(f'{stem}: expected statement and solution/type check passed', flush=True)
            save_report(report)
        if seen != set(APPLICATIONS):
            raise ValueError('Configurations do not cover the seven expected theorems')
        report.update(status='passed', challenge_modules_checked=len(report['checks']),
                      theorems_checked=len(seen))
        save_report(report)
        print(f'Saved {REPORT}. Comparator execution remains not_run.')
        return 0
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        report.update(status='failed', error=str(error))
        save_report(report)
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
