# Verification evidence

## Current cleanup and release verification

The October 6–7 [elaboration cleanup](elaboration-20261006/README.md) completed
two full 369-module Linux rebuilds, three guarded cleanup trials, and an exact
comparison of all 5,323 public types and six challenge roots. See its
[before/after report](elaboration-20261006/comparison/ELABORATION_COMPARISON.md)
and [reproducer commands](../docs/ELABORATION_CLEANUP.md).

For the current sources, select the rebuild/type evidence explicitly:

```sh
bash scripts/verify.sh lean \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

The cleanup measurement publication did not rerun Comparator or Nanoda. Its
certificate retains that narrower scope. The full release selects its portable
evidence separately through `portable_verification_current.directory` in
[release metadata](../metadata/results.json), pointing to
`verification/portable-20261007`. `python3 verification/check_reports.py`
accepts those records only when their source/checker hashes, scope, controls,
and retained evidence hashes match the current checkout.

The October 2 sections below describe the earlier reviewed release. Their
records remain unchanged; their historical source-freshness checks intentionally
do not pass for edited cleanup sources. Selecting current evidence never changes
the source bindings or execution claims in those historical files.

## Release-source Lean CI

[GitHub Actions run 37577412043, attempt 1](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/37577412043)
passed on release-source commit `38b360705c55fe4ee28e52f6cc493495fb7c1955`.
It rebuilt all **369 project modules** from source and audited
**9,107 declarations** / **7,219 theorem constants**, with only `propext`,
`Classical.choice`, and `Quot.sound`. The 25 manuscript mappings,
49 declaration references, and six expected-statement type checks also passed.
The pinned Mathlib dependency cache was reused; Lean and Mathlib were not
rebuilt from source.

[The execution record](github-actions-release-38b36070.json) and
[selected verbatim log lines](github-actions-release-38b36070-excerpt.log)
identify the actual source commit, run, job and completed steps. The downloaded
artifact's SHA-256 matches GitHub's digest; its proof-source and metadata hashes
match that frozen commit. This job did not run Comparator or Nanoda. Their
successful portable execution and the separate statement-evidence recovery
are recorded below.

## Preserved October 2 project-source build

[GitHub Actions run 36956367986, attempt 1](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/36956367986)
passed on commit `5345459acb1c072cfdc307904973fdca582ce13f` on October 2, 2026.
It rebuilt all **369 project modules** from source, including the aggregate and
audit, and accepted **9,107 declarations** and **7,219 theorem constants** with
only `propext`, `Classical.choice`, and `Quot.sound`. The 25 manuscript mappings,
49 declaration references, and six expected-statement type checks also passed.
Mathlib came from its pinned dependency cache; this was not a source rebuild of
Mathlib or Lean itself.

[The execution record](github-actions-5345459.json) and
[selected verbatim log lines](github-actions-5345459-excerpt.log) identify the
commit, run, job, and completed steps. Full logs and generated audit artifacts
are available on the linked run, subject to GitHub's retention policy.
The [earlier full-build record](github-actions-141f355.json) remains preserved.
Later documentation and reproducer changes do not alter the proof bodies;
each commit's workflow status is separately visible in GitHub Actions.

## Portable verification

For the current checkout, run the following command to rebuild/audit the Lean
proof library, compare all five challenge configurations with pinned Comparator
and replay their six theorem roots in Lean, then check their exports with pinned
Nanoda:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

Individual modes are `lean`, `comparator`, and `nanoda`; only `lean` and `all`
accept the certificate option. Each run writes new reports. The current release's
retained files are under [portable-20261007](portable-20261007/); the evidence
checker uses the explicit metadata selector rather than choosing the newest
directory or reusing a historical success record.
No landrun or systemd is needed. Comparator and Nanoda run unsandboxed.
See [reproducer commands](../docs/verify.md) for prerequisites and trust scope.

### Current release run

The all-mode verifier and portable archive passed in
[GitHub Actions run 37577412179](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/37577412179)
on source commit `38b360705c55fe4ee28e52f6cc493495fb7c1955`. The run rebuilt
all 369 project modules, audited 9,107 declarations / 7,219 theorem constants,
checked 49 mapped declaration references and six expected types, then passed
Comparator/Lean replay and Nanoda for five configurations / six roots.
All 13 acceptance/rejection controls passed. Nanoda was built from its recorded
source, Cargo lock and Rust pins; the pinned Mathlib dependency cache was reused.

The **overall workflow and job failed** afterward in statement-axiom recording:
the recorder expected bare axiom names but Lean printed universe annotations.
Fresh declaration export passed before that recording failure; the website
step was skipped. The [job record](github-actions-release-all-38b36070.json)
and [verbatim excerpt](github-actions-release-all-38b36070-excerpt.log) retain
the original success and failure markers. The portable records keep their
original execution commit and source/checker bindings.

Retained current proof evidence:

- [Full-run summary](portable-20261007/run-summary.json), [full log](portable-20261007/all.log), and [Lean build/audit log](portable-20261007/lean.log).
- [Comparator report](portable-20261007/comparator-result.json) and [log](portable-20261007/comparator.log).
- [Nanoda report](portable-20261007/nanoda-result.json), [log](portable-20261007/nanoda.log), [build receipt](portable-20261007/nanoda-build.json), and [controls log](portable-20261007/nanoda-controls.log).

### Recovered statement checks

The completed Linux expected-statement applications and six root-axiom probes
were recovered from the hash-verified original artifact. They executed on
`38b36070` using the fresh Linux project objects; that run's declaration export
matched the frozen metadata. Recovery corrected the recording of those outputs
and reran no proof commands. The original recorder driver's argument list was
not retained and was not reconstructed; this limit is explicit in the
[recovery provenance](statement-audit-20261007/recovery.json).

The [selected continuation](statement-audit-current.json) and
[mechanical checks](statement-audit-20261007/checks.json) retain all six historical
qualified correspondence findings. Both evidence freshness checks pass, as do
44 statement-record and 17 portable-record regression tests. These records
do not upgrade the failed GitHub job, repeat the full semantic review, establish
machine-certified English–Lean equivalence, or claim independent human review.
The earlier semantic reports and portable evidence remain unchanged.

### Preserved October 2 run

The October 2, 2026 native macOS `all` run passed. It rebuilt all 369 project
modules and audited 9,107 declarations / 7,219 theorem constants, checked the
49 mapped declaration references and six local expected types, then passed all
five configurations and six theorem roots in Comparator/Lean replay and Nanoda.
The pinned prebuilt Mathlib/dependency cache was reused; Lean and Mathlib were
not rebuilt from source. Nanoda was built from the recorded source, Cargo lock,
and Rust compiler pins. Thirteen acceptance/rejection controls passed.

Retained evidence:

- [Full-run summary](portable-20261002/run-summary.json), [full log](portable-20261002/all.log), and [Lean build/audit log](portable-20261002/lean.log).
- [Comparator report](portable-20261002/comparator-result.json) and [log](portable-20261002/comparator.log).
- [Nanoda report](portable-20261002/nanoda-result.json), [log](portable-20261002/nanoda.log), [build receipt](portable-20261002/nanoda-build.json), and [controls log](portable-20261002/nanoda-controls.log).

The historical source/artifact hashes identify the exact inputs checked on
October 2. The base Git commit alone does not identify the uncommitted checker
additions present at execution. The evidence checker and website validate the
selected current records against the current tree; neither reruns proof checking.
The October 2 portable files and historical CI records retain their original
execution status and hashes. No sandboxed upstream CLI execution is claimed.

## Reproduce the declaration browser

After the current Lean reproducer succeeds, export the compiled project constants and
rebuild the offline website:

```sh
python3 scripts/export_declarations.py --check
python3 tools/docs-site/build.py
python3 tools/docs-site/build.py --check
```

The first command re-exports the actual Lean environment and compares it with
`metadata/declarations.json`. To update the export after changing proof sources,
rebuild the proofs and run the exporter without `--check`. Export logs remain in
`.lake/export-declarations.log`; the site opens at `html/index.html`.
Live export progress is saved in `.lake/export-declarations-progress.json`.
Complete matching records can be resumed; `--check` always exports afresh.

The export records types and direct constant references from compiled objects.
The site check verifies generated bytes, links, source copies, and provenance.
These commands do not perform an independent kernel or Comparator check.

## Historical development and release preparation

`baseline-verification.json` and `baseline-verification.log` are preserved
evidence from the completed proof-development audit at
2026-10-01T04:10:05.782491+00:00. They cover 368 source modules, 9,107 project
declarations, and 7,219 theorem constants, including generated helpers. The
permitted transitive axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The proof library has no `sorry`, `admit`, or custom axioms.

That verification reused previously compiled objects whose source/object hashes
matched the recorded baseline, rebuilt changed sources and affected dependencies,
and recompiled the aggregate and full audit. It was not a clean rebuild of every
unchanged source. The full reproducible source build is `./check.sh`.

The baseline JSON is historical and is retained without editing. A few older
descriptive flags in it were superseded by later fields and proved endpoints
(in particular the general Hilbert-space factorization and the sharper Haar
moment range). It also contains historical document hashes for the earlier
project layout. Use `formalization.yaml`, `metadata/results.json`, and
`docs/FORMALIZATION_STATUS.md` for current scope. Use the baseline source/object
hashes and audit log as evidence, not as a new-release file inventory.

The organization pass prepends copyright comments to the existing Lean files.
The validator removes only that exact new header and checks the remaining bytes
against all 368 baseline source hashes. This establishes unchanged proof bodies;
it is not described as recompiling those bodies. The added `All.lean` imports
the audit. Challenge statements are checked separately and never imported by
the proof library or its audit.

The organization pass also recompiled `Nonadditivity`, `Audit`, and `All` against
the hash-checked proof objects. Its fresh audit again accepted 9,107 project
declarations and 7,219 theorem constants. The metadata check verified 49 exact
declaration names, defining modules, roles, and transitive axioms in Lean.

See [release-verification.json](release-verification.json),
[release-validation.json](release-validation.json), and
[challenge-checks.json](challenge-checks.json) for the precise execution status.
[release-manifest.json](release-manifest.json) records current file hashes.
The challenge record retains the commands and `.lake/` log paths from its run;
copies of those logs and generated statement checks are under
`verification/challenge-checks/`. They can be regenerated using
`python3 scripts/check_challenges.py` from the repository root.

The historical records above retain their original cache/rebuild boundaries.
The later full project-source build is recorded separately at the top of this
page. A successful local challenge/type check is separate from a successful
Comparator run.
