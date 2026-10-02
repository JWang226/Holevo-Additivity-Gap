# Holevo Additivity Gap

Lean 4 proofs accompanying Jinzhao Wang’s manuscript on unbounded Holevo additivity gaps for finite-dimensional quantum channels, including dimension bounds and operational classical-capacity consequences.

[arXiv paper](https://arxiv.org/abs/2609.18222) · [Proof website](https://jwang226.github.io/Holevo-Additivity-Gap/) · [Proof route](PROOF-PATH.md) · [Manuscript](paper/nonadditivity.tex)

The website explains the results and concepts alongside their Lean statements.

## Verify

On macOS or Linux, install Git, [elan](https://github.com/leanprover/elan), Python 3.11+ with `venv`/`pip`, and a native C/C++ build toolchain. Nanoda also needs [Rustup](https://rustup.rs/) to build its pinned kernel. Clone the repository:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
```

Choose a verifier; each command runs independently:

| Check | Command |
| --- | --- |
| Lean build and axiom audit | `bash scripts/verify.sh lean` |
| Comparator statement comparison and Lean replay | `bash scripts/verify.sh comparator` |
| Nanoda independent kernel | `bash scripts/verify.sh nanoda` |

Or run all three:

```sh
bash scripts/verify.sh all
```

No landrun or systemd is needed. Success ends with `VERIFICATION PASSED: <mode>`; fresh logs and reports are under `.verify-work/run-*`. Comparator and Nanoda run unsandboxed on trusted local sources. [Commands, prerequisites, and trust assumptions](docs/verify.md).

## Status and scope

The full project-source Lean build and axiom audit [passed](verification/github-actions-5345459.json), permitting only `propext`, `Classical.choice`, and `Quot.sound`. The [portable run](verification/README.md#portable-verification) also passed Comparator/Lean replay and Nanoda for all six challenge roots.

The principal endpoints are proved; **the full manuscript is not formalized**. The revised manuscript incorporates the [two counting repairs](docs/CORRECTIONS.md). See [formalization status](docs/FORMALIZATION_STATUS.md) for the exact scope.

Proofs are in [Nonadditivity/](Nonadditivity/); [All.lean](All.lean) includes the audit. Open `html/index.html` for offline browsing. [Copyright and attribution](COPYRIGHT.md) are preserved; original material has no blanket open-source license selected.
