# Counting corrections and their effect on the manuscript

Two intermediate counting assertions used in the Haar-moment argument fail on explicit finite paths. The Lean development proves the counterexamples and replacement estimates. The principal channel bounds, prescribed dimensions, and original Haar moment range survive these corrections.

The supplied [manuscript source](../paper/nonadditivity.tex) has **not been edited**. This note describes the corrections established in the formalization and the corresponding manuscript revision still needed. Its SHA-256 is:

```text
90e0b856882650a67fba7ee1fd11db117100eb8705ffc2f8b0077c6d4253db39
```

## Location in the manuscript

The affected argument is in the appendix **“The random-matrix estimate and parameter bounds”**, label `app:finite-threshold`, subsection **“The two-generator Haar estimate”**, in the proof of **“Explicit two-generator Haar estimate”**, label `lem:haar`. Within the paragraph *“The estimate for one pair,”* the manuscript invokes Bordenave–Collins Lemmas 5.3 and 5.8 for path counts and Lemma 5.9 for operator coefficients, then displays a bound for `|D_t|` and the aggregate error `6400 e p^24 ρ^p / N`.

The manuscript does not itself display the two false intermediate combinatorial assertions below. They arise in the cited counting argument on which that passage relies. The correction is to supply the repaired counting and coefficient argument and replace that numerical error calculation. The final moment hypothesis, label `eq:haar-hypotheses`, can remain unchanged.

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

This note records formal counterexamples and proved repairs. It does not claim that the manuscript has been revised, that every background statement has been formalized, or that an independent human review has occurred. See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact scope and verification record.
