# Counting corrections and their effect on the manuscript

Two intermediate counting assertions used in the Haar-moment argument fail on explicit finite paths. The Lean development proves the counterexamples and replacement estimates. The principal channel bounds, prescribed dimensions, and original Haar moment range survive these corrections.

The author's revised [manuscript source](../paper/nonadditivity.tex) **incorporates both counting repairs**. This note maps the repaired argument to the formalization. Its SHA-256 is:

```text
3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98
```

## Location in the manuscript

The affected argument is in the appendix **“The random-matrix estimate and parameter bounds”**, label `app:finite-threshold`, subsection **“The two-generator Haar estimate”**, in the proof of **“Explicit two-generator Haar estimate”**, label `lem:haar`. Its paragraphs *“Coefficient sums”* and *“Weighted class enumeration”* explain the failed counts and their repairs. The revised labels `eq:path-weight`, `eq:class-sum`, `eq:coefficient-sum`, and `eq:class-count` locate the path weight, class decomposition, coefficient bound, and weighted enumeration.

The revised manuscript explicitly describes both false intermediate assertions and replaces the old `6400 e p^24 ρ^p / N` calculation with the error budget below. The final moment hypothesis, label `eq:haar-hypotheses`, is unchanged. The exploration mark records the endpoint of the run along already discovered tree edges and the source color of the next step, as in `HaarPathMarks.explorationMark`. The source also includes the nonzero-Hilbert-space qualification in `eq:linear-id` and restricts the one-pair estimate to finite-support matrix/free-factor polynomial coefficients.

## 1. Important exploration times

Write

\[
\delta=\ell+e_1-2v,
\]

where `ℓ` is path length, `e₁` counts edges traversed exactly once, and `v` counts visited vertices. Here `δ` is an integer path defect, distinct from the channel gap coefficient `δ_K`. In half-defect notation `g = δ/2`, the same bounds read `2g + 1` and `2g + 2`.

The asserted bound of **at most `δ + 1` important times** is false. Let uppercase letters denote inverse generators. The six-step reduced, closed, generator-balanced path with word

```text
abaBAA
```

and vertex sequence `(0,1,1,1,1,1,0)` has `δ = 2` and four important times, indexed `1,2,3,4` starting from zero. Thus `4 > δ + 1 = 3`. The final traversal is a tree-edge visit; excluding it still leaves those same four important times.

The proved replacement is

\[
\#\{\text{important times}\}\le\delta+2.
\]

The terminal tree-edge visit is why one cannot always deduct the extra unit. This example refutes the intermediate exploration-time bound; it does **not**, by itself, refute the final class-count conclusion of the cited lemma.

The first explicit replacement class count is `128^(δ+2) ℓ^(3δ+6)`. A sharper weighted chronological encoding is used to recover the original moment range; it retains the actual positions of important times rather than charging every position independently.

Lean sources:

- [HaarPathExplorationCounterexample.lean](../Nonadditivity/HaarPathExplorationCounterexample.lean): `violates_uncorrected_important_bound` and `attains_corrected_important_bound`.
- [HaarPathExploration.lean](../Nonadditivity/HaarPathExploration.lean): `Path.card_importantTimes_le`.
- [HaarPathCounting.lean](../Nonadditivity/HaarPathCounting.lean): the explicit replacement coarse-class count.
- [HaarSharpCounting.lean](../Nonadditivity/HaarSharpCounting.lean): the weighted chronological class count.

## 2. Blocks between first and last visits

Isolate each edge's first and last visits as marked singleton blocks. The unmarked intervals form middle blocks. The assertion that the total block count satisfies **`r ≤ 3e`**, where `e` is the relevant distinct-edge count, is false.

The reduced balanced word `aaabABAA`, with every vertex equal, uses two loop edges. Its first/last-visit flags are

```text
true, false, false, true, false, true, false, true
```

There are four marked positions and three intervening runs: seven blocks, exceeding `3 × 2 = 6`. This is an actual path, not just an arbitrary Boolean pattern; its Haar entry monomial is `|U_a(x,x)|^6 |U_b(x,x)|^2`.

Let `M` be the number of marked positions. The valid bounds are

\[
\#\{\text{middle blocks}\}\le M-1,
\qquad M\le2e.
\]

Each middle block is charged to its following marker; the initial marker is unused. Although this allows more blocks, only marked coefficient factors incur the extra moment-order factor. The combined exponent is therefore bounded by

\[
(r-1)+M\le6e-2.
\]

This proves the required grouped coefficient exponent `9δ + 11`. There is no need to retain the false bound `r ≤ 3e`.

Lean sources:

- [HaarPathRunCounterexample.lean](../Nonadditivity/HaarPathRunCounterexample.lean): the literal path and `violates_uncorrected_run_bound`.
- [HaarPathRuns.lean](../Nonadditivity/HaarPathRuns.lean): `middleRuns_add_one_le`, `corrected_exponent_le`, and `occurrence_exponent_le`.
- [HaarMarkedCompositions.lean](../Nonadditivity/HaarMarkedCompositions.lean) and [HaarBranchGraphBudget.lean](../Nonadditivity/HaarBranchGraphBudget.lean): the marked-factor counting and coefficient exponent.

## Final error budget and unchanged endpoints

With the corrected weighted path count and coefficient bound, the sum of the length contributions is bounded by

\[
\sum_{t=1}^{p}|D_t|
\le \frac{4096p^{26}}{N}\left(1+\frac{64}{p}\right)^p\rho^p
\le N^{-1/2}\rho^p,
\qquad p\ge2,\quad N\ge2^{32}p^{80}.
\]

Here `N` denotes actual matrix dimension, as in the manuscript. The Lean endpoint indexes that dimension by `N + 1`. For the manuscript's moment application, `p` is even. The scalar estimate `(1 + 64/p)^p ≤ 16p^14` makes the final absorption explicit.

The replacement error budget is proved in [HaarSharpSummation.lean](../Nonadditivity/HaarSharpSummation.lean), [HaarSharpConstants.lean](../Nonadditivity/HaarSharpConstants.lean), and [HaarSharpBound.lean](../Nonadditivity/HaarSharpBound.lean). In particular, `HaarSharpBound.onePairTraceBound` proves the actual mixed one-pair Haar integral estimate for finite matrix coefficients and the remaining free factors, with no unproved analytic premise.

The original condition `N ≥ 2^32 p^80` is preserved. The principal prescribed choice

\[
N=\left\lceil\exp\bigl(40(7\ln K+2)n\bigr)\right\rceil
\]

and the final channel information bounds are unchanged. The main prescribed-channel theorem already follows from a valid corrected route with the stronger intermediate threshold `2^80 p^80`, which its chosen parameters satisfy; the sharper weighted route separately restores the original `2^32 p^80` range.

This note records formal counterexamples, proved repairs, and their incorporation into the revised manuscript. The coefficient proofs use different internal encodings, so the correspondence concerns the stated bounds rather than every proof line. Full manuscript formalization and independent human certification remain outside the recorded verification scope. See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact scope and verification record.
