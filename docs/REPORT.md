# Lean formalization: operational coding and the prescribed channel bounds


The project now proves the operational classical coding theorem for every
finite Kraus channel:

\[
C(T)=\sup_{m\ge1}\frac{\chi(T^{\otimes m})}{m}
    =\lim_{m\to\infty}\frac{\chi(T^{\otimes m})}{m}.
\]

Here capacity is defined independently through physical density-matrix
codewords, normalized POVM decoders, and vanishing average Born error on
all positive block lengths. `OperationalCodingTheorem.lean` proves the
identity; it is not a definition or an assumed coding theorem.

The achievability proof constructs typical spectral projectors, proves a
sequential projection union bound and finite random-code packing bound,
and constructs codes below each ensemble's Holevo information. Actual block
flattening and padding then give every regularized lower bound. The converse
uses a proved POVM dilation, a gentle projection estimate, entropy continuity,
and exact flagged-state entropy. Its finite-code estimate is
\(\ln M\le\chi(T)+2\sqrt{2\epsilon}\ln(Md)+4\ln2\), followed by
a vanishing rate correction. It applies to arbitrary encoded states and decoders.

`OperationalConsequences.lean` transfers the construction to genuine
operational capacity: the same channels can have arbitrarily small positive
single-use Holevo information, arbitrarily large capacity gain, and arbitrarily
large two-use Holevo ratio. A single explicit channel sequence has
\(\chi(T_K)\to0\) and \(C(T_K)\to\infty\).

The all-use Weyl-extension identity is proved for every positive tensor power,
including arbitrary entangled inputs. Consequently the actual operational
capacity of a Weyl extension equals the output log dimension minus regularized
minimum output entropy. These results concern the gap between operational
capacity and single-use Holevo information; they do not assert nonadditivity
of operational capacity between two distinct channels.

`UniversalFactorization.lean` proves that the same explicit finite-set
factorization coefficients and scalar work simultaneously in every unitary
representation on a nonzero complete complex Hilbert space, including infinite
dimension. The nonzero-space condition is necessary for the additive scalar
norm identity. The correction bound and backward error transfer are also proved.

The manuscript's prescribed dimension choice is now proved in Lean. For integers
\(K\ge 2\) and \(n\ge n_0(K)\), set

\[
n_0(K)=\left\lceil256(1+\ln K)^2\right\rceil,
\qquad
N=\left\lceil\exp\bigl(40(7\ln K+2)n\bigr)\right\rceil.
\]

`HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound`, in
`Nonadditivity/HaarPrescribedBound.lean`, proves the existence of a genuine finite
Kraus CPTP channel \(T\) with

\[
\dim\operatorname{Input}(T)=2N^nK^{2n},
\qquad
\dim\operatorname{Output}(T)=K^n,
\]

and the following bounds, all in bits:

\[
\begin{aligned}
0<\frac{2n}{K}\le\chi(T)
&\le n\log_2(1+9/K)+2\log_2\kappa_n,\\
\chi(T\otimes T)
&\ge \frac{n\log_2 K}{K},\\
\chi(T\otimes T)-2\chi(T)
&\ge n\delta_K-4\log_2\kappa_n,
\end{aligned}
\]

where \(\kappa_n=(n+1)/(n-1)\) and
\(\delta_K=\log_2(K)/K-2\log_2(1+9/K)\). The information quantities use actual
finite ensembles of complex density matrices. The theorem has only the stated
numerical hypotheses: no Haar expectation, path-counting, coefficient, or norm
estimate remains an assumption. This is the prescribed dimension bound; no
optimality claim is made.

## The quantitative Haar branch is complete

The proof now establishes the literal `ExplicitHaarExpectation K n` used by the
channel construction. It combines actual Haar entry integrals and their
vanishing conditions, exact trace expansion over closed reduced paths, genuine
coarse and refined path quotients, Haar-weight invariance on refined classes,
and grouped operator coefficient estimates. The coefficient proof constructs
the actual profile fibres and preserves coefficient sums through noncommutative
Cauchy–Schwarz and non-returning word segmentation. Finite scalar summation then
gives the mixed one-pair moment estimate; tensor replacement supplies the
required Haar expectation. The existing net and entropy arguments convert that
estimate into the channel theorem above.

Two intermediate combinatorial claims required correction. Both failures have
explicit Lean-checked counterexamples, and the replacement estimates are proved.
Here \(\delta=\ell+e_1-2v\), where \(e_1\) counts singly traversed edges and
\(v\) counts visited vertices.

- A closed reduced, generator-balanced six-step path with word `abaBAA` has
  integer defect \(\delta=2\) and four important exploration times. The proposed
  bound \(\delta+1\) fails even after excluding the final traversal. Accounting
  for the final tree visit gives \(\delta+2\). A concrete injective encoding proves
  the corrected coarse-class bound
  \(128^{\delta+2}\ell^{3\delta+6}\) for path length \(\ell\).
- The first/last marker pattern
  `[true,false,false,true,false,true,false,true]` has four marked positions and
  three middle runs: seven blocks, exceeding \(3\cdot2\). Charging each middle
  run to its following marker, and charging moment-order factors only at marked
  positions, yields the needed coefficient exponent \(9\delta+11\).

The resulting extra constants and polynomial factors are included in the final
error budget. The stronger dimension slack already supplied by the prescribed
moment choice absorbs them, so the displayed choice of \(N\) is unchanged.
These counterexamples refute intermediate estimates, not the final channel
statement.

## Original Haar moment range and supplementary asymptotics

`HaarSharpBound.onePairTraceBound` proves the literal one-pair Haar integral
bound at the original dimension range \(N\ge2^{32}p^{80}\). It uses the
corrected exploration and coefficient estimates. A chronological sparse code
assigns an optional mark to each actual time and retains a weighted generating
function instead of overcounting every time coordinate separately. The resulting
geometric ratios fit the original range, and exact scalar estimates absorb the
remaining prefactor. The earlier \(2^{80}p^{80}\) route remains valid but is
no longer the strongest proved range.

The same prescribed family now has a named real-valued ratio liminf,
\(\Delta_\chi=\Theta_K(\sqrt{q_{\mathrm{in}}})\), the explicit favorable
probability \(\varepsilon/[2(1+\varepsilon)]\), and a proved remainder bound
for the gap fraction's large-K expansion. A fixed channel's regrouped gap,
divided by the number of uses, is proved to tend to zero.

For the actual growing family at \(n_K=\lceil K/\sqrt{\ln K}\rceil\),
`PrescribedCostDimensions.lean` proves
\(q_{\mathrm{in}}/K^2\to280/\ln2\).
`PrescribedCostScaling.lean` proves positive two-sided bounds on
\(\chi(T_K)\sqrt{\log q_{\mathrm{in}}}\), and
`PrescribedCostCapacity.lean` proves the positive lower bound on both
\(\chi(T_K^{\otimes2})/[2\sqrt{\log q_{\mathrm{in}}}]\) and
\(C(T_K)/\sqrt{\log q_{\mathrm{in}}}\).
The threshold condition is proved eventually for the original rounded block
length; no growing-dimension assumption is hidden in these endpoints.

## Consequences for the same prescribed channel family

`HaarPrescribedConsequences.lean` selects an actual channel family from the
strengthened construction. It proves the finite regularized-Holevo gain bound,
divergence of the additive and regularized gains when the gap coefficient is
positive, and the stated eventual two-use and regularized ratio thresholds.
The supplementary bound `2*n/K <= chi(T)` holds for this same family.

`HaarPrescribedScaling.lean` proves the exact output-qubit count, matching
linear lower and upper bounds on the gap, and the output-normalized gap
liminf. The input-qubit expansion has a remainder tending to zero, with the
actual input dimension inside the logarithm. These results introduce no new
analytic assumptions.

## Qualitative results and scope

The earlier qualitative theorem remains unchanged and unconditional.
`ExactQualitative.exists_actual_channel_bounds_with_dimensions` gives, for
all \(K\ge2\), \(n\ge1\), and \(\eta>0\), an actual finite channel with
\(0<\chi(T)\le n\log_2(1+9/K)+\eta\) and the exact lower bound
\(\chi(T\otimes T)\ge n\log_2(K)/K\). Its independent deterministic
finite-moment and damping construction remains available.

The proved qualitative consequences still include arbitrarily small positive
single-use Holevo information with arbitrarily large additive gaps and ratios,
and, by the new coding theorem, the corresponding operational capacity statements. The independent
Gaussian construction also remains checked.

The older, more general `HaarStrongConvergence`, `AllHaarStrongConvergence`, and
`HaarUpperConvergence` predicates remain unproved. The new specialized
quantitative theorem does not assert them. Their conditional interfaces remain in the project and
are not hypotheses of `exists_prescribed_channel`. The original undamped
Haar realization in every sufficiently large dimension is a broader statement
than the alternative qualitative construction proved here. The strengthened prescribed-channel theorem includes the supplementary lower
bound \(2n/K\) on the same channel witness. The revised manuscript incorporates both counting repairs;
[CORRECTIONS.md](CORRECTIONS.md) maps the repaired passages to Lean.

## Verification and reproduction

The [full project-source GitHub Actions build](../verification/github-actions-5345459.json) subsequently rebuilt all 369 project modules, including the aggregate audit, and passed. It checked 9,107 project declarations, including 7,219 theorem constants, with no `sorry`, `admit`, custom axiom, or unexpected transitive axiom. Comparator and independent-kernel execution remain pending.

The earlier local verification was incremental: all 368 mathematical project modules compiled successfully, unchanged baseline source/object hashes were checked against the prior manifest, and newer sources, stale dependents, and the aggregate audit were recompiled. The source contains 3,469 explicit theorem/lemma declarations. This historical check did not rebuild the unchanged baseline. Some baseline modules emitted nonfatal unused-variable or simplifier warnings; exact compiler output is retained in the [baseline verification log](../verification/baseline-verification.log).

The permitted transitive axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The audit covers private helpers and definitions with proof
fields, rejects `sorryAx` and custom axioms, and distinguishes explicit theorem
hypotheses from axioms.

Lean is pinned to 4.29.0-rc6 and mathlib to
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`. [baseline verification metadata](../verification/baseline-verification.json) records source
hashes and exact audit counts; [baseline verification log](../verification/baseline-verification.log) records the compilation verification and final audit.
After restoring dependencies, run `./check.sh` from the project directory.
