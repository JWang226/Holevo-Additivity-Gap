# Holevo Additivity Gap

Lean 4 proofs accompanying Jinzhao Wang’s manuscript on unbounded Holevo additivity gaps for finite-dimensional quantum channels, including dimension bounds and operational classical-capacity consequences.

[Proof website](https://jwang226.github.io/Holevo-Additivity-Gap/) · [Proof route](PROOF-PATH.md) · [Manuscript](paper/nonadditivity.tex)

## Verify with Lean

Requires Linux or macOS, Git, [elan](https://github.com/leanprover/elan), and Python 3.11+ with `venv`/`pip`. Dependencies are pinned to Lean `4.29.0-rc6` and the committed mathlib revision.

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
./verification/lean/run.sh
```

This rebuilds all project proofs, audits their axioms, validates metadata, and checks the challenge statements locally. Success ends with `LEAN REPRODUCTION PASSED`; logs are saved under `.verify-work/logs/`.

## Verify with Comparator

Requires Linux, a nonroot account, a working systemd user session, and [landrun](https://github.com/Zouuup/landrun). Use a separate fresh checkout:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git Holevo-Comparator-Check
cd Holevo-Comparator-Check
./verification/comparator/run.sh
```

The script builds the pinned checker and runs all five configurations. Success ends with `COMPARATOR REPRODUCTION PASSED`. See [verification instructions](https://jwang226.github.io/Holevo-Additivity-Gap/verify.html) for prerequisites, expected output, logs, and trust assumptions.

## Status and scope

The full project-source Lean build and axiom audit [passed](verification/github-actions-5345459.json), permitting only `propext`, `Classical.choice`, and `Quot.sound`. **Comparator and independent-kernel execution remain pending.**

The principal endpoints are proved; **the full manuscript is not formalized**. The revised manuscript incorporates the [two counting repairs](docs/CORRECTIONS.md). See [formalization status](docs/FORMALIZATION_STATUS.md) for the exact scope.

Proofs are in [Nonadditivity/](Nonadditivity/); [All.lean](All.lean) includes the audit. Open `html/index.html` for offline browsing. [Copyright and attribution](COPYRIGHT.md) are preserved; original material has no blanket open-source license selected.
