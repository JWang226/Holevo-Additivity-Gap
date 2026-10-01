# Formalization status

The principal channel construction, quantitative information bounds, operational coding theorem, and listed asymptotic consequences are proved in Lean without unproved analytic or coding premises. **The entire manuscript is not formalized.** Broader Haar-convergence interfaces and some background generalizations remain outside the completed endpoints.

The release contains the original, unedited [manuscript source](../paper/nonadditivity.tex). Two counting repairs have been proved in Lean and are documented in [CORRECTIONS.md](CORRECTIONS.md); they have not been incorporated into that source. Its SHA-256 is:

```text
90e0b856882650a67fba7ee1fd11db117100eb8705ffc2f8b0077c6d4253db39
```

## Completed principal results

All information quantities below are in bits. Channels are actual finite Kraus completely positive trace-preserving maps; ensembles consist of complex density matrices.

### Prescribed dimensions and information gap

For integers `K ≥ 2` and

\[
n\ge n_0(K)=\left\lceil256(1+\ln K)^2\right\rceil,
\qquad
N=\left\lceil\exp\bigl(40(7\ln K+2)n\bigr)\right\rceil,
\]

`HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound` constructs a channel `T` with input dimension `2N^n K^(2n)` and output dimension `K^n` satisfying

\[
\begin{aligned}
0<\frac{2n}{K}\le\chi(T)
&\le n\log_2(1+9/K)+2\log_2\kappa_n,\\
\chi(T\otimes T)&\ge\frac{n\log_2 K}{K},\\
\chi(T\otimes T)-2\chi(T)
&\ge n\delta_K-4\log_2\kappa_n,
\end{aligned}
\]

where `κ_n = (n+1)/(n−1)` and `δ_K = log₂(K)/K − 2log₂(1+9/K)`. Its only hypotheses are the stated numerical conditions. No Haar expectation, path count, coefficient estimate, or norm bound remains to be supplied.

Source: [HaarPrescribedBound.lean](../Nonadditivity/HaarPrescribedBound.lean). The same actual channel family and its divergence and ratio consequences are in [HaarPrescribedConsequences.lean](../Nonadditivity/HaarPrescribedConsequences.lean), [HaarPrescribedRatio.lean](../Nonadditivity/HaarPrescribedRatio.lean), and [HaarPrescribedScaling.lean](../Nonadditivity/HaarPrescribedScaling.lean).

### Operational classical capacity

For every finite Kraus channel, the development proves

\[
C(T)=\sup_{m\ge1}\frac{\chi(T^{\otimes m})}{m}
    =\lim_{m\to\infty}\frac{\chi(T^{\otimes m})}{m}.
\]

Capacity is defined independently through actual density-matrix codewords, normalized POVM decoders, and vanishing average Born error on all positive block lengths. The identity is a theorem, not a definition or an assumed coding theorem. The proof includes achievability, the converse, and physical block regrouping and padding.

Sources: [OperationalCodingTheorem.lean](../Nonadditivity/OperationalCodingTheorem.lean), [QuantumCodingHSW.lean](../Nonadditivity/QuantumCodingHSW.lean), [OperationalWeakConverse.lean](../Nonadditivity/OperationalWeakConverse.lean), and [OperationalBlocking.lean](../Nonadditivity/OperationalBlocking.lean).

[OperationalConsequences.lean](../Nonadditivity/OperationalConsequences.lean) proves the resulting actual capacity gains and ratios, including a sequence with `χ(T_K) → 0` and `C(T_K) → ∞`. The setting is finite-dimensional, unassisted classical communication over a memoryless channel, permitting arbitrary block input states and joint POVM decoding. These statements do not assert nonadditivity of operational capacity across two distinct channels or a strong converse at every rate above capacity.

### Further completed endpoints

| Result | Lean source |
| --- | --- |
| Independent qualitative construction for every `K ≥ 2`, `n ≥ 1`, `η > 0`, with positive `χ(T) ≤ nlog₂(1+9/K)+η` and exact `χ(T⊗T) ≥ nlog₂(K)/K` | [ExactQualitative.lean](../Nonadditivity/ExactQualitative.lean) |
| Weyl-extension Holevo identity at every positive tensor power, including entangled inputs; corresponding regularized identity | [WeylPowersEntropy.lean](../Nonadditivity/WeylPowersEntropy.lean), [WeylPowersRegularized.lean](../Nonadditivity/WeylPowersRegularized.lean) |
| One finite-set factorization with the same scalar and coefficients in every nonzero complete complex Hilbert-space unitary representation, including infinite dimension | [UniversalFactorization.lean](../Nonadditivity/UniversalFactorization.lean) |
| Actual one-pair Haar moment estimate at the original dimension range `N ≥ 2^32 p^80` | [HaarSharpBound.lean](../Nonadditivity/HaarSharpBound.lean) |
| Fixed-`K` gap proportional to the square root of actual input qubits, when `δ_K > 0` | [HaarInputScaling.lean](../Nonadditivity/HaarInputScaling.lean) |
| Explicit favorable Haar probability and explicit large-`K` remainder for the gap fraction | [HaarPrescribedProbability.lean](../Nonadditivity/HaarPrescribedProbability.lean), [GapFractionAsymptotics.lean](../Nonadditivity/GapFractionAsymptotics.lean) |
| For `n_K = ⌈K/√ln K⌉`, actual input qubits satisfy `q_in/K² → 280/ln 2`; `χ(T_K)` has order `1/√log₂ q_in`, while two-use information per use and capacity have a positive lower bound of order `√log₂ q_in` | [PrescribedCostDimensions.lean](../Nonadditivity/PrescribedCostDimensions.lean), [PrescribedCostScaling.lean](../Nonadditivity/PrescribedCostScaling.lean), [PrescribedCostCapacity.lean](../Nonadditivity/PrescribedCostCapacity.lean) |
| A fixed channel's regrouped two-use gap, divided by block length, tends to zero | [HolevoPowerGap.lean](../Nonadditivity/HolevoPowerGap.lean) |

The nonzero-Hilbert-space hypothesis in the universal factorization is explicit and necessary for its additive scalar norm identity. The prescribed dimensions are proved sufficient; no dimension-optimality claim is made.

## Remaining scope

The following distinctions are preserved in this release:

- The generic `HaarStrongConvergence`, `AllHaarStrongConvergence`, `HaarUpperConvergence`, and `HaarTraceMomentControl` interfaces remain unproved in their stated generality. Their conditional theorems retain their explicit premises. None is a premise of the principal unconditional channel or operational results listed above.
- The finite-dimensional part of manuscript lemma `lem:cy`, **“Free and finite-dimensional norm bounds,”** asserts an undamped unitary realization for every `κ > 1` and every sufficiently large integer dimension. That exact broader claim is not supplied by the particular prescribed-dimension theorem or the alternative qualitative construction.
- The one-pair moment theorem is implemented for actual finite matrices and the remaining free-factor coefficient representations needed by the construction. It is not packaged at the full generality of every abstract traced C*-algebra used in the appendix's exposition.
- Some standard background generalizations and illustrative numerical examples are not separate formal endpoints. In particular, this release does not claim a statement-by-statement formalization of the paper.
- The two counting repairs are proved in Lean; the reference manuscript remains unedited.

These are scope limitations, not hidden hypotheses of the completed endpoints. More technical discussion appears in [ANALYTIC_INPUTS.md](ANALYTIC_INPUTS.md), with a theorem map in [PROOF_MAP.md](PROOF_MAP.md).

## Verification evidence and release organization

The mathematical verification recorded before this release organization completed at **2026-10-01 04:10:05 UTC**. The preserved [baseline verification metadata](../verification/baseline-verification.json) and [baseline compiler and audit log](../verification/baseline-verification.log) record:

| Audit item | Recorded result |
| --- | --- |
| Successfully compiled project modules | 368, including the aggregate root and audit |
| Audited project declarations | 9,107 |
| Theorem constants, including generated helpers | 7,219 |
| Explicit source `theorem`/`lemma` declarations | 3,469 |
| Permitted transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| `sorry`, `admit`, custom axioms, or unexpected transitive axioms | None found |

The transitive audit covers private helpers and definitions with proof fields. It distinguishes theorem hypotheses from axioms and rejects `sorryAx` and custom axioms. Some baseline modules emitted nonfatal warnings; those are retained in the log.

This was **incremental verification, not a clean rebuild** of every unchanged baseline module. It compared unchanged source/object hashes with the previous manifest, used successful session compilations of new sources, rebuilt newer sources and stale dependents in dependency order, and recompiled the complete aggregate and transitive axiom audit.

This release-organization task places the sources, manuscript, documentation, and preserved evidence into a distributable layout. The counts above describe the prior mathematical verification; they are not a claim that organizing the files itself performed a new clean Lean build. Any release-layout integrity checks are separate from that compiler evidence. The preserved baseline manifest uses the paths and metadata of its original workspace and is historical evidence, not a current-layout file manifest.

The baseline JSON is preserved verbatim, including older descriptive fields that were not all refreshed when stronger endpoints were added. For example, its older infinite-representation factorization flag remains false and its older moment-scope field describes only the `2^80` route, while later fields and the corresponding source theorems record the completed universal factorization and `2^32` threshold. These historical descriptive fields should not override the current result map, current formalization metadata, or the exact Lean statements linked above.

The project pins **Lean 4.29.0-rc6** and mathlib revision **`f156f7abd91ac67adb22bf999e5a71ba22e22e41`**. After restoring the pinned dependencies, run `./check.sh` from the release root for the full project rebuild and audit. Compilation and the dependency audit establish the included formal statements under Lean's standard foundations; this release does not claim an independent human review of the manuscript-to-formalization correspondence.
