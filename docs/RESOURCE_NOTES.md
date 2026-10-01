# Sources and provenance of the Haar and alternative constructions

Search and source inspection date: 2026-09-30 UTC. This is a bounded search of
public sources, not a claim that no relevant formalization exists anywhere.
No external theorem below has been imported as an axiom or treated as a Lean
proof. The required finite-Haar argument has now been implemented locally,
through `HaarPrescribedDimension.exists_prescribed_channel`. Its complete
dependency chain and two repaired intermediate counts are recorded in
`PROOF_MAP.md`; `ANALYTIC_INPUTS.md` distinguishes the proved result from
older, unused convergence predicates and operational coding claims.

## Mathematical proofs that match or help the target

**Shou--Gorshkov, _A constructive violation of additivity of minimum output
von Neumann entropy_, arXiv:2609.23946v2 (24 September 2026).**
[Version-pinned source](https://arxiv.org/html/2609.23946v2).
Its finite-moment damping method motivated the new deterministic route.
Version 2 also extends the method to large gaps using product free groups
in Appendix B; we do not claim that generalization as new.
Our Lean implementation constructs finite models by completing partial free-word
translations to permutations, rather than importing its explicit matrix group.
The checked product-group moment bound, arbitrary-block realization, normalized
Bell stability, strict positivity, and unbounded additive consequences are proved
in the project. No result from this paper is an axiom or an assumed channel bound.
The weighted Bell reserve in `ExactQualitative` removes the two-use error and
matches the exact qualitative proposition.
This deterministic route does not establish the prescribed dimension; the
separate completed Haar proof does.

**Bordenave--Collins, _Norm of matrix-valued polynomials in random unitaries
and permutations_, arXiv:2304.05714v2 (10 January 2024).**
[Version-pinned source, Section 9.3](https://arxiv.org/html/2304.05714v2#S9.SS3).
Theorem 9.2 is the relevant tensor-leg result: independent unitary families
act on distinct tensor factors and converge to the product free-group model.
Lemma 9.3 and the preceding uniform amplification estimates explain the
tensor step. The paper also supplies the expectation bounds and quantitative
linearization behind the manuscript's dimension argument. This is the
closest mathematical reference. The required finite expectation estimate is
now proved in Lean through invariant tensors and Weingarten estimates, actual
path/refined-class and coefficient sums, and successive tensor replacement.
The implementation repairs two intermediate counting claims from Lemmas 5.3
and 5.9 while retaining the manuscript's final dimension formula. This is not
a claim to have formalized every theorem in the reference, in particular its
full two-sided strong-convergence statement.

**Chen--Garza-Vargas--van Handel, _A new approach to strong convergence II.
The classical ensembles_, arXiv:2412.00593v3 (6 June 2026).**
[Version-pinned source](https://arxiv.org/html/2412.00593v3).
Theorem 1.5 bounds upper tails for polynomials in one independent Haar family,
allowing coefficient dimension `exp(c*N*eps^2/log(N*eps^2)^2)`. Section 7
offers an alternative route through rational moments, polynomial inequalities,
spectral tests, and Haar concentration; these still need formalization.
The tensor applications in Section 9.4 and Appendix B concern GUE models.
The one-family Haar theorem does not directly cover our distinct tensor
legs: `U tensor I` is not Haar on the full tensor-product space.

**Collins--Matsumoto--Novak, _The Weingarten Calculus_ (2022).**
[Author preprint](https://arxiv.org/abs/2109.14890),
[publisher record](https://doi.org/10.1090/noti2474).
Sections 2 and 4 explain Haar integration through invariant tensors and the
unitary Weingarten formula. This is a useful blueprint for implementing the
moment algebra needed by either convergence approach. It is a mathematical
exposition, not executable Lean source; moment identities alone do not
establish an operator-norm upper bound.

## Lean libraries and source files inspected

| Resource | Verified scope | Consequence for this project |
| --- | --- | --- |
| [mathlib Haar measure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar/Basic.html) | Construction, normalization, invariance, and uniqueness | Already used by `HaarModel`; it supplies the probability law, not a large-dimension norm theorem. |
| [mathlib independence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html) | Independence and operations on independent random variables | Already provides the finite-product infrastructure. |
| [SLT](https://github.com/YuanheZ/lean-stat-learning-theory) | Actual matrix Bernstein source, Gaussian concentration, matrix spectral infrastructure | Potential supporting tools; no matching strong-freeness theorem was located. |
| [HighDimProb](https://github.com/dududuguo/HighDimProb) | Actual matrix Bernstein and concentration source | Potential supporting tools; no matching Haar/free-limit theorem was located. |
| [SemicircleLaw](https://github.com/FredRaj3/SemicircleLaw) | Wigner moment-method development | Different ensemble and objective; the inspected principal moment-limit theorems contain `sorry`. |
| [Gaussian boson-sampling formalization](https://zenodo.org/records/21969265) | Haar construction and elementary COE second moments; explicit concentration input | Useful invariance proof patterns, but it does not discharge full Haar concentration or strong freeness. |

The local mathlib tree at commit
`f156f7abd91ac67adb22bf999e5a71ba22e22e41` was searched for Weingarten calculus,
asymptotic freeness, random matrices, and free probability. No relevant
declaration was found under those terms. Haar and convergence-in-measure
modules are present. Current public repository searches were checked as
well; absence from these searches is not a universal nonexistence result.

### SLT

Inspected commit: `d0f506f0a695018265dccb33bcb05e2f5ca1c876`.
[Pinned matrix Bernstein source](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/RMT/MatBern.lean).
`RMT.matrix_bernstein_inequality_hdp_all` has a proof body and a standard
independent, centered, bounded real symmetric matrix setting. The repository
targets Lean/mathlib 4.32.0, while this project targets 4.29.0-rc6. Source was
read, but its complete dependency closure was not rebuilt here. Generic
matrix Bernstein cannot simply be substituted for convergence to the exact
free polynomial norm; its variance and dimension losses must be analyzed.

### HighDimProb

Inspected commit: `c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae`.
[Pinned matrix concentration source](https://github.com/dududuguo/HighDimProb/blob/c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae/HighDimProb/RandomMatrix/MatrixBernsteinProvider.lean).
`MatrixBernstein.operatorNormTail_of_primitives` is an alias for a proved
tail theorem with explicit independence, centering, integrability, norm, and
variance assumptions. This version targets Lean/mathlib 4.29.1. Its API is
close to the project's toolchain, but no theorem converting this particular
Haar polynomial to its exact free norm was located. No dependency was added.

### SemicircleLaw

Inspected commit: `9f72b2d562583f89b093d05387d942c1ca8c02f4`.
[Pinned Wigner source](https://github.com/FredRaj3/SemicircleLaw/blob/9f72b2d562583f89b093d05387d942c1ca8c02f4/SemicircleLaw/RandomMatrix/WignerMatrix.lean).
The file has admitted proofs for `wignerMatrixMomentEvenExpectationLimit`
and `wignerMatrixMomentsVarianceLimit`, among other declarations. Even a
completed weak semicircle law would not establish Haar operator-norm
convergence. It was therefore not imported.

### Gaussian boson-sampling archive

Inspected Zenodo record: `21969265`; archive filename:
`lean_verification_von_neumann_typicality_v1.0.1_zenodo.zip`.
The files `COE/HaarMoments.lean` and `COE/HaarInvariance.lean` derive COE
second moments from actual normalization, permutation, phase, and rotation
invariance. `normalizedUnitaryHaar_finiteCOESecondMomentInvariance` connects
these finite identities to Haar measure. The archive's declared boundary
still includes full unitary Haar concentration. Its source is helpful for
elementary invariant integration, but neither its concentration assumption
nor its low-order moments supplies the finite norm estimates now proved by
the project's separate Weingarten/path argument.

## Implemented Haar proof and retained scope

The proof preserves the original independent Haar-pair sampling model and
literal polynomial evaluation. It constructs the Haar invariant-tensor
projection, proves the required spanning and Gram-inverse identities, and
estimates the actual Weingarten expansion. Exact word-to-path expansion,
phase vanishing, sparse class reconstruction, refined-profile invariance,
and an exact palette parametrization connect these integrals to the actual
operator coefficient sums. Noncommutative first/last occurrence contractions
and finite composition counts supply the grouped coefficient estimate.
The final finite sums, successive replacement on distinct tensor legs, and
canonical basis transport prove the expected norm inequality consumed by the
channel theorem.

`HaarPathExplorationCounterexample` checks that the smaller important-time
count in the proof of Bordenave--Collins Lemma 5.3 can fail when the final
traversal is a tree edge. The corrected count includes that case and both
endpoint color labels. `HaarPathRunCounterexample` and `HaarPathRuns` record
the failure of the intermediate `r <= 3*e` claim in Lemma 5.9; charging length
factors only to first/last markers preserves the required combined exponent.
These corrections are proved and carried into the final moment budget.
They do not enlarge the prescribed dimension or refute the paper's final
norm theorem. No optimality claim is made for the dimension formula.

The generic `HaarStrongConvergence`, `AllHaarStrongConvergence`,
`HaarUpperConvergence`, and `HaarTraceMomentControl` predicates remain
unproved in their stated generality. They are not assumptions of
`HaarPrescribedDimension.exists_prescribed_channel`. In particular, the
finite expectation bound does not assert a lower spectral convergence theorem.

## A constructed Gaussian route for the multiplicative conclusion

The earlier spherical strategy has been superseded by a rectangular Gaussian
construction. It avoids Gaussian polar decomposition on the sphere and does
not use Haar strong convergence. The construction and final
`GaussianConsequences` declarations have compiled successfully; the final
consequence module completed with exit code 0 and no warnings. The report
and [baseline verification metadata](../verification/baseline-verification.json) record the repository-wide rebuild and axiom-audit
status.

Let `K >= 4096` and take `N = K^2`. The starting matrix is

```
G : C^N -> C^K tensor C^N,
G_(b,e),d = (X_(b,e),d + i Y_(b,e),d) / sqrt(2*K*N),
```

where the real coordinates are independent standard Gaussians. The Lean
sampling space is the complex Euclidean coordinate array regarded as a real
inner-product space, with mathlib's actual `stdGaussian` measure. Its
normalization gives `E(G* G) = I`.

The source implements the following chain:

1. `GaussianQuadratic` integrates a scalar Gaussian square exponential
   directly, diagonalizes each real symmetric quadratic form, and derives
   the centered quadratic MGF and two-sided Chernoff bound. No concentration
   certificate is assumed.
2. `GaussianRectangular`, `GaussianRectangularAlgebra`, and
   `GaussianSampleEvaluation` identify the actual complex matrix quadratic
   forms with those real Gaussian operators and calculate their norms,
   traces, and squared traces.
3. `QuadraticNet` and `GaussianCertificates` use an input `1/4`-net of size
   at most `9^(2N)` and a traceless Hermitian output `1/2`-net of size at most
   `5^(K^2)`. The combined failure bound is

   ```
   2 * 9^(2N) * exp(-K*N/128)
     + 2 * 5^(K^2) * 9^(2N) * exp(-63*N/2) < 1.
   ```

   Consequently there is an actual Gaussian sample passing both sets of
   tests: Gram quadratic error below `1/4`, and observable quadratic forms
   below `64/K` on the two nets.
4. The deterministic net bounds yield `norm(G*G-I) <= 1/2` and extend the
   observable estimates. `GaussianNormalization` constructs
   `V = G (G*G)^(-1/2)` by the finite matrix spectral theorem, proves
   `V*V = I`, and slices `V` into actual Kraus matrices. Polar normalization
   costs at most a factor two. Including both net losses, the resulting
   channel `Phi : M_N -> M_K`, with environment dimension `N`, satisfies

   ```
   norm(Phi*(A)) <= (512/K) * hsLength(A)
   ```

   for every Hermitian traceless `A`. This is the statement of
   `GaussianConstruction.exists_channel`; its general dimension hypothesis
   is `N >= K^2`.
5. `GeneralBell`, `SmallEnvironment`, and `GaussianChannelBounds` provide
   the Bell witness, strict positivity of the actual Holevo information,
   and the existing switch/Weyl conversion. For the converted channel `Q`,
   when `log K >= 1`, the information quantities in bits obey

   ```
   0 < chi(Q) <= 512^2 / (K * log 2),
   chi(Q tensor Q) / (2 * chi(Q)) >= (log K - 1) / (2 * 512^2).
   ```

   The converted input dimension is `2*N*K^2 = 2*K^4`, and the output
   dimension is `K`. `GaussianScalar.exists_parameter` chooses one integer
   `K` making the first upper bound arbitrarily small and the ratio lower
   bound arbitrarily large simultaneously.

`GaussianConsequences.exists_small_chi_large_ratio` now connects the complete
chain: for every `epsilon > 0` and real `R`, an actual finite channel has
`0 < chi <= epsilon` and `R <= chi(Q tensor Q)/(2*chi(Q))`, with no unproved
analytic premise. `exists_nonadditive_channel` supplies an actual strict
Holevo nonadditivity witness. `exists_small_chi_large_regularized_ratio`
also proves the corresponding unbounded ratio for the formally defined
regularized Holevo supremum. This last statement uses the checked
regularization inequalities; it does not assert a separately formalized
operational coding theorem.

Here `log` is the natural logarithm; division by `log 2` converts the
single-use information bound to bits. The dimension and the constant 512
are those of this new Gaussian proof, not the manuscript's prescribed Haar
construction. In particular, this route does not establish unbounded
**additive** gaps or the manuscript's multi-block explicit-dimension theorem.
Its Bell lower bound is `(log K-1)/(K*log 2)`, which tends to zero as `K`
grows; the ratio conclusion must not be confused with additive growth.

### Limited reuse of SLT eigenbasis proofs

The inspected SLT commit contains a general
[`SLT/HansonWright.lean`](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/HansonWright.lean)
proof. Two short eigenbasis coordinate proof patterns were adapted to this
project's pinned mathlib: `symmetric_inner_apply_eq_sum_eigenvalues_repr`
and `orthonormalBasis_repr_sum_smul`, now named
`GaussianQuadratic.quadratic_eq_eigen_sum` and `basis_repr_sum`.
The broader SLT Hanson–Wright theorem and dependency tree are not imported.
The exact Gaussian MGF, tail bound, and subsequent construction are proved
locally. Attribution and modification notices are recorded in
`THIRD_PARTY_NOTICES.md`, and the pinned repository's complete Apache 2.0
license is reproduced unchanged in `LICENSES/SLT-Apache-2.0.txt`.

## Further proved Haar algebra

The Haar route has also progressed beyond second and fourth moments.
`HaarColumnMoments.integral_entry_norm_even` proves, for every order `p`
and the actual Haar law in dimension `d = N+1`,

```
E |U_ij|^(2p) = p! / (d*(d+1)*...*(d+p-1)) <= p! / d^p.
```

`HaarMixedMoments` proves the complete scalar mixed-moment formula and the
vanishing of any entry monomial with unbalanced row multiplicities.
`HaarAveraging` constructs `U^(tensor p) tensor conjugate(U)^(tensor q)` and
proves that its actual Haar average is a Hermitian idempotent with range
exactly the invariant tensors. These declarations have compiled without
warnings or unproved assumptions.

The subsequent invariant-spanning, Weingarten inverse, literal path-class,
coefficient-fibre, and tensor-replacement modules complete the required
mixed-word high-trace estimate. `HaarPrescribedBound.lean` joins these results
into the unconditional prescribed-dimension channel theorem. The earlier
moment modules remain useful components; low-order moments alone were never
used as a substitute for the full argument.

## Operational coding and sequential measurements

The coding development constructs actual physical codes and proves both bounds.
The elementary projection argument in `QuantumCodingUnion.lean` follows the
quantum union-bound method of Gao and its short proof by O'Donnell and
Venkateswaran; the checked proof is implemented locally. References:
[Gao, arXiv:1410.5688](https://arxiv.org/abs/1410.5688) and
[O'Donnell–Venkateswaran, short proof](https://www.cs.cmu.edu/~odonnell/papers/quantum-union-bound.pdf).
The references are mathematical background, not imported proof axioms.
