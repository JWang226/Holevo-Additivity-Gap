# Holevo Additivity Gap

Lean 4 proofs for unbounded Holevo additivity gaps of finite-dimensional quantum channels, including dimension bounds and classical-capacity consequences.

[arXiv paper](https://arxiv.org/abs/2609.18222) · [Proof website](https://jwang226.github.io/Holevo-Additivity-Gap/) · [Proof route](PROOF-PATH.md) · [Manuscript-to-Lean map](https://jwang226.github.io/Holevo-Additivity-Gap/correspondence.html) · [Manuscript](paper/nonadditivity.tex)

The website explains the results and concepts alongside their Lean statements. The release includes [detailed elaboration reports](verification/elaboration-20261006/README.md), exact public-type comparisons, and [verification records](verification/README.md) tied to the sources that were checked.

## Verify

On macOS or Linux, install Git, [elan](https://github.com/leanprover/elan), Python 3.11+ with `venv`/`pip`, and a native C/C++ build toolchain. Nanoda also needs [Rustup](https://rustup.rs/) to build its pinned kernel. Clone the repository:

```sh
git clone https://github.com/JWang226/Holevo-Additivity-Gap.git
cd Holevo-Additivity-Gap
```

Choose a verifier; each command runs independently:

| Check | Command |
| --- | --- |
| Lean build and axiom audit | `bash scripts/verify.sh lean --source-certificate verification/elaboration-20261006/source-certificate.json` |
| Comparator statement comparison and Lean replay | `bash scripts/verify.sh comparator` |
| Nanoda independent kernel | `bash scripts/verify.sh nanoda` |

Or run all three:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/elaboration-20261006/source-certificate.json
```

The explicit certificate selects the current cleanup's recorded source evidence; the command still performs a fresh Lean build and audit. Omission retains the strict historical source check. No landrun or systemd is needed. Success ends with `VERIFICATION PASSED: <mode>`; fresh logs and reports are under `.verify-work/run-*`. Comparator and Nanoda run unsandboxed on trusted local sources. [Commands, prerequisites, and trust assumptions](docs/verify.md).

## Status and scope

The cleanup’s [full Lean build and source certificate](verification/elaboration-20261006/source-certificate.json) cover all 369 modules, with no proof holes and only `propext`, `Classical.choice`, and `Quot.sound`. [Fresh public-type comparison](verification/elaboration-20261006/public-types.json) checks all 5,323 public declarations and six challenge roots. [Cleanup and timing reproduction](docs/ELABORATION_CLEANUP.md).

The [verification index](verification/README.md#portable-verification) distinguishes the current release's selected portable evidence from the preserved October 2 Comparator/Lean replay and Nanoda records. Fresh portable verification and the [statement-review continuation](docs/STATEMENT_AUDIT_DELTA.md) must pass their evidence checks before release publication. Historical evidence keeps its original source bindings.

The principal endpoints are proved; **the full manuscript is not formalized**. The revised manuscript incorporates the [two counting repairs](docs/CORRECTIONS.md). See [formalization status](docs/FORMALIZATION_STATUS.md) for the exact scope.

Proofs are in [Nonadditivity/](Nonadditivity/); [All.lean](All.lean) includes the audit. Open `html/index.html` for offline browsing. [Copyright and attribution](COPYRIGHT.md) are preserved; original material has no blanket open-source license selected.
