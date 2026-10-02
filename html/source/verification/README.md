# Verification evidence

## Full project-source build on GitHub

[GitHub Actions run 36901743100, attempt 2](https://github.com/JWang226/Holevo-Additivity-Gap/actions/runs/36901743100)
passed on commit `141f355a841cbf56fd1715750eebb9d2bcc488cb` on October 1, 2026.
It rebuilt all **369 project modules** from source, including the aggregate and
audit, and accepted **9,107 declarations** and **7,219 theorem constants** with
only `propext`, `Classical.choice`, and `Quot.sound`. The 25 manuscript mappings,
49 declaration references, and six expected-statement type checks also passed.
Mathlib came from its pinned dependency cache; this was not a source rebuild of
Mathlib or Lean itself.

[The execution record](github-actions-141f355.json) and
[selected verbatim log lines](github-actions-141f355-excerpt.log) identify the
commit, run, job, and completed steps. Full logs and generated audit artifacts
are available on the linked run, subject to GitHub's retention policy.
Later documentation and reproducer changes do not alter the proof bodies;
each commit's workflow status is separately visible in GitHub Actions.

Run `./verification/lean/run.sh` from a clean clone to reproduce the project
source build, metadata checks, and isolated challenge checks. The command
retains `.lake/check.log` and per-step logs under `.verify-work/logs/`.
`./verification/comparator/run.sh` is the separate Linux Comparator reproducer.
An end-to-end Comparator run and independent-kernel check remain pending.

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
