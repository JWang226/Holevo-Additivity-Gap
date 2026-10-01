# Verification evidence

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

Comparator execution and a new clean rebuild of every proof module remain
explicitly pending. A successful local challenge/type check must not be renamed
as a successful Comparator run.
