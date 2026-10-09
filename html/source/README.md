# Holevo Additivity Gap

Lean 4 proofs for unbounded Holevo additivity gaps of finite-dimensional quantum channels, including dimension bounds and classical-capacity consequences.

[arXiv v2](https://arxiv.org/abs/2609.18222v2) · [Proof website](https://jwang226.github.io/Holevo-Additivity-Gap/) · [Proof route](PROOF-PATH.md) · [Manuscript-to-Lean map](https://jwang226.github.io/Holevo-Additivity-Gap/correspondence.html) · [Manuscript](paper/nonadditivity.tex)

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
| Lean build and axiom audit | `bash scripts/verify.sh lean --source-certificate verification/additive-20261008/source-certificate.json` |
| Comparator statement comparison and Lean replay | `bash scripts/verify.sh comparator` |
| Nanoda independent kernel | `bash scripts/verify.sh nanoda` |

Or run all three:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/additive-20261008/source-certificate.json
```

The explicit certificate extends the recorded cleanup evidence to the added challenge configuration; the command still performs a fresh Lean build and audit. Omission retains the strict historical source check. No landrun or systemd is needed. Success ends with `VERIFICATION PASSED: <mode>`; fresh logs and reports are under `.verify-work/run-*`. Comparator and Nanoda run unsandboxed on trusted local sources. [Commands, prerequisites, and trust assumptions](docs/verify.md).

## Status and scope

The manuscript is the exact published source of **arXiv:2609.18222v2**, without local wording changes. [Source provenance](paper/arxiv-v2.json) binds it to the [upstream source archive](verification/manuscript-v2-20261008/source.tar.gz). The [v2 correspondence review](docs/STATEMENT_AUDIT_V2.md) records the unchanged mathematical endpoints and the revised exploration-mark prose.

The current suite has **six configurations and seven theorem roots**. Root F checks `DeterministicConsequences.actual_small_large`, the absolute two-use separation `chiTwo / 2 ≥ R` in `cor:separation`; C checks operational gain and the two-use ratio. The [current portable record](verification/portable-20261008/run-summary.json) and [statement-review continuation](verification/statement-audit-delta-20261008.json) identify their checked sources and results separately. The [challenge notes](ComparatorChallenges/README.md) explain their scope and shared proof dependencies.

The October 6–7 cleanup’s [full Lean build and source certificate](verification/elaboration-20261006/source-certificate.json) retain their original 369-module and six-root scope. Its [public-type comparison](verification/elaboration-20261006/public-types.json) covers 5,323 public declarations. The [additive certificate](verification/additive-20261008/source-certificate.json) preserves that evidence and binds the new configuration for an existing theorem; it is separate from fresh proof execution. [Cleanup and timing reproduction](docs/ELABORATION_CLEANUP.md).

The October 7 [portable run](verification/portable-20261007/run-summary.json) passed on its recorded inputs for five configurations and six roots; the [overall GitHub job](verification/github-actions-release-all-38b36070.json) failed afterward in statement recording. Those records and the older semantic reviews keep their original source bindings. [Verification details](verification/README.md) distinguish the current records from that history.

The principal endpoints are proved; **the full manuscript is not formalized**. The upstream manuscript's broad certificate wording does not expand this release's scope. Its v2 exploration-mark prose differs from the formal encoding; no literal proof-by-proof correspondence is claimed. See [counting repairs](docs/CORRECTIONS.md), [formalization status](docs/FORMALIZATION_STATUS.md), and the [qualified v2 review](docs/STATEMENT_AUDIT_V2.md).

Proofs are in [Nonadditivity/](Nonadditivity/); [All.lean](All.lean) includes the audit. Open `html/index.html` for offline browsing. [Copyright and attribution](COPYRIGHT.md) are preserved; original material has no blanket open-source license selected.
