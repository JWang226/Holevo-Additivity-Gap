# Unconditional channel theorems and analytic scope

The manuscript's **exact Section 2 qualitative existence bounds are now
unconditional**, including the two-use lower bound without an error term.
Unbounded additive gaps, vanishing positive single-use information with
diverging two-use information, and unbounded multiplicative ratios also have
an unconditional deterministic construction. The proof uses exact
finite-group trace moments, a small nonuniform perturbation of the branch
probabilities, and invertible input damping. The full Collins--Youn estimate
is proved internally for every block length. No Haar convergence, assumed
moment estimate, or channel-existence hypothesis is used in this route.

The manuscript's prescribed-dimension theorem is also unconditional.
`HaarPrescribedDimension.exists_prescribed_channel` in `HaarPrescribedBound.lean`
proves the original dimension formula and all three information bounds under
only the stated numerical thresholds. The actual finite-Haar expectation,
path counts, refined coefficient sums, and tensor transfer are proved.
The older general Haar convergence predicates remain unproved in their stated
form and are not used by this final theorem. Dimension optimality is outside
the claim. The arbitrary-use Weyl-extension equality and the operational
classical coding theorem are now proved separately, from their concrete
channel, state, and code definitions.

## Unconditional finite-block realization

`ExactQualitative.exists_actual_channel_bounds_with_dimensions`
proves, for every `K >= 2`, `n >= 1`, and `eta > 0`, that there are an actual
finite Kraus CPTP channel `T` and an integer `N > 0` such that, in bits,

```text
input dimension  = 2*N^n*K^(2*n)
output dimension = K^n
0 < chi(T)
chi(T) <= n*log2(1 + 9/K) + eta
n*log2(K)/K <= chi(T tensor T).
```

`ExactQualitative.exists_actual_channel_gap` proves the exact qualitative
gap lower bound `n*(log2(K)/K - 2*log2(1 + 9/K)) - 2*eta`.
`ExactQualitative.exists_actual_channel_bounds_positive` packages the same
information bounds without recording dimensions. Here `N` is the actual
local dimension, not the Haar model's dimension-minus-one index.

The proof has the following concrete components:

- `FiniteFreeModel` extends partial translations on a finite free-word ball
  to permutations. The resulting finite group representation detects every
  nonidentity word within the chosen radius, including coordinatewise
  detection in product free groups.
- `FiniteRegularMatrix` supplies genuine finite unitary regular
  representations and their exact characters. `FiniteMomentMatching` proves
  that finite normalized trace moments equal the identity coefficient of
  the corresponding free-group polynomial. `FiniteBlockModel` identifies
  the finite evaluation with the actual block-channel adjoint. Radius `4*p`
  gives the required even moment of order `2*p`, bounded by the proved
  Collins--Youn constant.
- `SpectralDamping` constructs `F=(I+R)^(-1)`, with
  `R=sum_A (X_A/L)^(2*p)` for the actual finite observable net. It proves
  `norm(F*X_A*F) <= L`, positive residual `I-F^2`, an explicit left inverse,
  and normalized trace loss at most twice the normalized trace of `R`.
  `DampedRealization` chooses the finite moment order before choosing the
  finite input dimension and obtains the uniform adjoint certificate.
- `DampedChannel` constructs an actual complete Kraus family for
  `rho |-> T(F*rho*F) + trace((I-F^2)*rho)*I/d`. On traceless observables its
  adjoint is exactly `F*T.adjointMap(A)*F`.
- `WeightedBellScalar` perturbs two branch probabilities by `+s` and `-s`,
  preserving positivity and normalization for `0 < s < 1/K`. Their squared
  mass becomes `1/K + 2*s^2`. `WeightedBell` and `WeightedBlockBell` turn this
  into a strict Bell entropy margin `2*n*s^2*ln(K)` for the actual weighted
  block channel.
- `WeightedBlock` proves exact output scaling and its continuity at uniform
  weights. `WeightedCertificate` bounds the additional adjoint error per
  unit HS observable by `delta*(2+delta)` when the output scale differs from
  the identity by at most `delta`. `WeightedParameters` chooses a nonzero
  perturbation inside the prescribed single-use tolerance.
- `CanonicalBlockBell`, `DampedBellStability`, `EntropyContinuity`, and
  `EntropyStability` transport the original Bell entropy estimate to the
  damped channel. The error depends on the fixed output dimension and the
  normalized trace loss, not on the growing input dimension. The moment
  order is chosen after the strict weighted Bell margin is fixed, so the
  damping error is completely absorbed and no two-use error remains.
- `StrictEntropy` proves strict entropy maximality only at the maximally
  mixed state. `WeightedPositivity` exhibits the nonuniform diagonal
  `p_i^n` of a product-input output. `DampedPositivity` pulls that witness
  back through the inverse filter, proving strictly positive converted
  Holevo information even with the additional replacement Kraus branches.

Weighting and damping change the base channel. This alternative proof
establishes the exact qualitative existence bounds, without proving norm
convergence of the original unitary families or a Haar convergence predicate.
It proves strict positivity, rather than the supplementary numerical lower
bound `chi_bits >= 2*n/K` for the original undamped construction.

The earlier `DeterministicQualitative` theorem remains valid: it allows a
freely prescribed error in both information bounds, without perturbing the
branch weights. It is still used by `DeterministicConsequences` for the
asymptotic statements below. `ExactQualitative` removes that finite-block
two-use error; it is no longer an outstanding qualitative gap.

## Unconditional separating families

`DeterministicConsequences.actual_vanishing_diverging` constructs actual
channels with `chi(T_K) -> 0` and `chi(T_K tensor T_K)/2 -> infinity`.
The single-use quantity is positive for every `K >= 2`.
`actual_gap_tendsto_atTop` and `actual_ratio_tendsto_atTop` prove divergence
of the additive gap and the two-use ratio. In particular,
`exists_small_chi_large_gap_and_ratio` proves

```text
forall epsilon > 0, forall A R, exists an actual finite channel T,
  0 < chi(T) <= epsilon,
  A <= chi(T tensor T) - 2*chi(T),
  R <= chi(T tensor T)/(2*chi(T)).
```

`actual_regularizedHolevo_tendsto_atTop`,
`actual_regularizedGain_tendsto_atTop`, and
`actual_regularizedRatio_tendsto_atTop` give the regularized counterparts.
`exists_small_chi_large_regularized_gain_and_ratio` makes the simultaneous
existence statement. These concern the actual tensor-power Holevo rate
limit. The independently proved operational coding theorem now identifies
that limit and its equal regularized supremum with classical capacity.

## The original conditional Haar route

An older one-sided Haar interface for the qualitative bounds is
`Nonadditivity.UpperHaarRealization.exists_block_channel`. For fixed
`K >= 2`, `n >= 1`, and `eta > 0`, its only analytic premise is
`UpperHaarRealization.HaarUpperConvergence K n`. It constructs an actual finite
Kraus CPTP channel `T`, with information measured in bits, satisfying

```
0 < chi(T)
chi(T) <= n * log2(1 + 9/K) + eta
n * log2(K)/K <= chi(T tensor T)
n * (log2(K)/K - 2*log2(1 + 9/K)) - 2*eta
  <= chi(T tensor T) - 2*chi(T).
```

The channels, density matrices, spectral entropy, finite output ensembles,
and Holevo suprema in these statements are all concrete formal definitions.
The selected Haar index `N` denotes local dimension `N+1`. The construction
has input dimension `2*(N+1)^n*K^(2*n)` and output dimension `K^n`; no
quantitative upper bound on the selected `N` is proved. This remains a
proved conditional route using the original Haar model. Its unproved
premise is not required by either `ExactQualitative` or the new
`HaarPrescribedDimension.exists_prescribed_channel` theorem.

## Unconditional Gaussian multiplicative separation

`GaussianConsequences.exists_small_chi_large_ratio` proves

```text
forall epsilon > 0, forall R, exists an actual finite channel T,
  0 < chi(T) <= epsilon and R <= chi(T tensor T)/(2*chi(T)).
```

`exists_small_chi_large_regularized_ratio` proves the analogous statement for
`T.regularizedHolevo/T.chi`, using the established actual tensor-power limit.
`exists_nonadditive_channel` gives a strictly positive additive gap. There is
no Haar, moment, concentration, or channel-existence premise in these
statements. The Gaussian route alone does not establish arbitrarily large
additive gaps or a simultaneous vanishing-single-use/diverging-two-use
family; those conclusions now follow from the deterministic route above.

The proof constructs a complex `K*N` by `N` Gaussian matrix, proves a
simultaneous finite-net event, and normalizes it to an isometry by the actual
positive inverse square root. `GaussianQuadratic` derives the centered
quadratic MGF from the Gaussian density and the spectral theorem, then
proves the tail bound and integrability. `GaussianRectangularAlgebra` gives
the literal real quadratic coefficient operator, for a unit input and a
Hermitian observable `A`, with

```text
norm(T) <= norm(A)/(2*K*N)
trace_real(T) = Re(trace(A))/K
trace_real(T*T) = Re(trace(A*A))/(2*K^2*N).
```

`GaussianCertificates` proves the union-bound budget for the actual input
and observable nets. `GaussianNormalization` and `GaussianNetRealization`
turn the resulting event into a complete Kraus channel and its uniform
traceless HS-to-operator certificate. `GaussianConstruction.exists_channel`
proves the bound `512/K` for every `K >= 4096` and `N >= K^2`.

`GeneralBell` proves the Bell overlap and entropy estimate for this actual
channel; `GaussianChannelBounds` then uses the existing switch/Weyl
conversion. With `N=K^2`, the converted channel has input dimension `2*K^4`,
output dimension `K`,

```text
0 < chi(T) <= 512^2/(K*ln(2))
(ln(K)-1)/(2*512^2) <= chi(T tensor T)/(2*chi(T)).
```

These constants are deliberately generous. This construction proves the
multiplicative conclusion independently and does not prove the original
Haar convergence predicate or the manuscript's exact block constants.

## The full free-group estimate is now a theorem

`FreeModel` defines

- `ProductFreeGroup K n := Fin n -> FreeGroup (Fin K)`;
- `Branch K n := Fin n -> Fin K`;
- the actual Hilbert space `lp (fun _ : ProductFreeGroup K n => Complex) 2`;
- bounded left shifts `leftRegular g f h = f (g^-1 * h)`;
- `branchWord a j = FreeGroup.of (a j)`;
- `gamma A = (1/K^n) * sum_{a,b} A[a,b] * leftRegular (branchWord a^-1 * branchWord b)`;
- `freeNorm A := norm (gamma A)` and
  `c K n := sqrt(((1 + 9/K)^n - 1)/K^n)`.

The theorem

```lean
CollinsYounProduct.collinsYounBound
  (hK : 2 <= K) (hn : 1 <= n) : FreeModel.CollinsYounBound K n
```

proves, for every complex coefficient matrix with zero trace,

```
freeNorm A <= c K n * AdjointPurity.hsLength A.
```

No analytic norm bound is supplied as a premise. `CollinsYounTensor` proves
the one-coordinate length-two estimate with arbitrary bounded operator
coefficients: the three cancellation components each obey the appropriate
coefficient norm bound. `RegularFubini` proves the actual lp product isometry
and regular-polynomial intertwining. `CollinsYounProduct` then splits the
first-coordinate diagonal and off-diagonal sectors and proves unrestricted
and traceless squared-norm estimates simultaneously. Their constants are
`(K+9)^n` and `(K+9)^n-K^n`, respectively. Dividing by `K^n` gives the exact
constant above.

This is the manuscript's finite-generator version of the published estimate.
`RegularRestriction` also proves equality with the corresponding
infinite-generator regular norm by an actual coset decomposition. The older
one-block proof and interfaces with an explicit CY premise remain available;
`HaarConsequences` supplies the general theorem internally.

## The sufficient one-sided Haar input

`UpperHaarRealization.HaarUpperConvergence K n` means that, for every fixed
Hermitian traceless matrix `A` of HS length one and every `eps > 0`,

```
sampleMeasure K n N {omega |
  collinsYounConstant K n + eps <=
    norm ((blockChannel (sampleUnitary K n N omega) n).adjointMap A)}
  --> 0 as N --> infinity.
```

`upper_of_strong` derives this predicate from the original full strong
convergence and the proved Collins--Youn estimate.
`eventually_exists_certificate` proves the actual uniform matrix adjoint
certificate from these one-sided tails. This older conditional channel
interface then uses the certificate and the actual Bell/entropy conversion.

- `exists_arbitrarily_large_gap_of_all_upper` proves unbounded additive gaps
  from the upper-tail predicate at all fixed `K >= 2, n >= 1`.
- `exists_arbitrarily_large_ratio` needs only the predicate at `n=1` and all
  fixed `K >= 2`; `exists_one_block_ratio` gives `log(K)/36` at each fixed `K`.

These are proved implications. The Haar upper-tail predicate itself remains
unproved. The older `HaarConsequences` interfaces below retain full strong
convergence for their simultaneous-family and regularized statements.

## Earlier moment interfaces

`HaarMoments` proves the canonical Haar entry means and second moments:
`E U_ij = 0` and `E[U_ij conj(U_kl)] = delta_ik delta_jl/(N+1)`.
It also proves the conjugation twirl `E[U A U*] = trace(A)/(N+1) I`, entry
moments in each independent sampled coordinate, and zero covariance between
entries from distinct sampled unitaries. These are actual integrals, derived
from Haar invariance and unitary orthogonality.

`HaarMomentTail.measure_norm_ge_le_trace_moment` proves the high-moment
Markov step on actual Hermitian matrices with the Euclidean operator norm:

```
P(norm X >= t) <= E[Re trace(X^(2*p))] / t^(2*p),  t > 0.
```

The normalized-trace version displays the exact matrix dimension as a
multiplicative factor. `canonical_upper_tail_of_trace_moments` specializes
this to the actual sampled block adjoint, with arbitrary dimension-dependent
moment order `p(N)`. Hermitian preservation and norm measurability are proved
internally. `UpperHaarRealization.HaarTraceMomentControl K n` explicitly asks
for such a sequence of moment orders at each normalized test and each
threshold `collinsYounConstant K n + eps`.
`upper_of_trace_moments` supplies the upper-tail predicate, and
`exists_block_channel_of_trace_moments` connects it directly to the actual
channel bounds. This general convergence predicate remains unproved in its
stated form; the prescribed-dimension proof instead constructs its required
finite moment estimates directly in `HaarPrescribedBound.lean`.

`HaarFourthMoments` also proves `E|U_ij|^4 = 2/(d*(d+1))` and, for `i != k`,
`E[|U_ij|^2 |U_kj|^2] = 1/(d*(d+1))`, where `d=N+1`. Explicit phase and
Hadamard unitaries derive these identities from Haar invariance. These
low-order identities are supplemented by the all-order Weingarten and path
estimates used in the completed prescribed-dimension proof.

## The original full strong-convergence statement

`HaarModel` constructs the compact complex unitary group on `Fin (N+1)`, its
normalized Haar probability, and the finite product indexed by `Fin n × Fin K`.
The coordinate samples are proved independent and each has the exact Haar
law. Tensor words and channel-adjoint matrices are continuous; the actual
Euclidean operator norms are measurable and their failure events are Borel.

`FreeBridge.outputFreeNorm K n A` reindexes `A`, with the same output-basis
bijection used by the actual block channel, into the concrete regular model.
Trace, Hermitian symmetry, and Hilbert--Schmidt length are preserved.

This stronger predicate fixes all probability spaces, matrices, and norms:

```lean
HaarModel.HaarStrongConvergence K n
-- means, for the canonical sampleMeasure and sampleUnitary:
forall A : Matrix (ZMod (K^n)) (ZMod (K^n)) Complex,
  A.IsHermitian -> A.trace = 0 -> AdjointPurity.hsLength A = 1 ->
  forall delta : Real, 0 < delta ->
    Filter.Tendsto
      (fun N => sampleMeasure K n N {omega | delta <=
        abs (norm ((BlockConstruction.blockChannel
          (sampleUnitary K n N omega) n).adjointMap A)
          - FreeBridge.outputFreeNorm K n A)})
      Filter.atTop (nhds 0)
```

Probabilities take values in `ENNReal`. This is convergence in probability
for every fixed test matrix at fixed `K,n`; it does not assume a good channel,
a uniform finite norm certificate, entropy estimates, or Holevo separation.
The finite-net selection and all those consequences are proved from it.

The mathematical reference for this full convergence predicate is
Bordenave--Collins, arXiv:2304.05714v2, Theorem 9.2, on distinct tensor legs.
The project does not claim that full theorem or its lower spectral bound.
It now proves the finite one-sided expectation estimate required by the
prescribed-dimension construction, including the actual high moments, path
combinatorics, coefficient sums, and transfer across distinct tensor legs.
[Version-pinned primary source](https://arxiv.org/html/2304.05714v2#S9.SS3).

## Existing family consequences from full strong convergence

`HaarConsequences.AllHaarStrongConvergence` asks for the same predicate at
every fixed `K >= 2`, `n >= 1`. It implies all fields of the older
`ActualConsequences.AnalyticInputs` structure because its CY field is now
filled by a proved theorem.

- `exists_large_gap_and_ratio` constructs an actual finite channel with
  positive single-use information, an arbitrarily large additive gap, and an
  arbitrarily large two-use ratio simultaneously.
- `exists_separating_family` gives actual channels with single-use information
  tending to zero, half-two-use information tending to infinity, and additive
  gaps and two-use ratios tending to infinity.
- `exists_small_chi_large_regularized_gain` and
  `exists_large_regularized_gain_and_ratio` prove the regularized counterparts.
- The stronger hypothesis reduction for multiplicative separation remains:
  `OneBlockRealization.exists_arbitrarily_large_ratio` needs only canonical
  one-block convergence. It proves the explicit lower bound `ln(K)/36` for
  the ratio, with a positive denominator.

Positive information is not an assumption. `PositiveHolevo` proves the
universal lower bound `chi_bits >= 2*n/K` for these undamped converted block channels,
using normalized eigenvectors, coincident pure outputs, an exact merged
ensemble, and tensor entropy. The damped construction separately proves
strict positivity; it does not assert the same numerical lower bound.

## Quantitative geometry and operator factorization

The following ingredients no longer need separate analytic premises:

- The exact injective free-group substitution with generator length
  `2*Nat.log 2 (K-1)+1`, regular norm preservation at every finite matrix
  amplification, and coordinate/total support-degree bounds.
- The stated finite-dimensional packing and symmetric sphere-net bounds.
  `QuantitativeNet` derives these by Haar volume and maximal separated sets,
  including a prescribed test and its negative without cardinality overhead.
- Actual positive Gram assembly, square-root coefficients, coefficient energy,
  and the correction bound `theta <= |S| * norm(P_regular)`.
- The exact factor identity for every nonempty finite unitary representation
  and for the actual infinite regular representation, with the same
  representation-independent square coefficients of dimension `2*m*|S|`.
- Finite-versus-regular relative-error transfer from those actual factors.

`RegularShiftedDilation` proves the infinite spectral step by a concrete
grading unitary and the symmetric spectrum of the actual dilation. It proves
`norm(H(P)+theta I)=norm(P)+theta` for `theta >= 0`. `RegularFactorization`
evaluates the constructed Gram matrix and padded factor on the actual
vector-valued lp space, so the resulting norm equality is a conclusion.

The dilation is essential: for an arbitrary Hermitian polynomial, positivity
of `Q*Q=P+theta I` alone would not imply `norm Q^2=norm P+theta`. The negative
spectral endpoint could realize `norm P`. The formal proof does not make
that invalid inference. `UniversalShiftedDilation` and
`UniversalFactorization` extend this argument to every nonzero complete
complex Hilbert-space representation. The coefficients and correction are
chosen before the representation is quantified.

The deterministic repeated shortening is now constructed in
`PolynomialReduction` and `ProductPolynomialReduction`. An actual polynomial
supported at degree at most `2^k` is recursively replaced by one with linear
support, with literal square matrix coefficients. Its coefficient dimension
is the original dimension multiplied by `dimensionCost`; its backward error
cost is exactly `3^k * dimensionCost`. The product-group construction gives
safe bounds

```
dimensionCost <= (2 * 3^k * max 1 support.card)^k
errorCost     <= (6 * 3^k * max 1 support.card)^k.
```

`PrescribedTest.exists_prescribed_test` constructs the normalized traceless
Hermitian observable with free norm `sqrt(2)*K^(-(n+1)/2)`.
`NetPolynomial.exists_net_polynomial` includes it in the actual symmetric
observable net, and forms the literal diagonal-coefficient regular polynomial.
Its norm is bounded below by that prescribed value and above by the exact
Collins--Youn constant. Self-adjointness, spectral symmetry, the exact
finite-block norm, and the positive-shift identity are also proved.
`NetPolynomialSupport.polynomial` collects repeated words into the actual
finite-support polynomial record consumed by shortening. Its
`polynomial_regularEval` and `polynomial_finiteEval_norm` theorems preserve
the regular operator and finite evaluation norm exactly, including the
finite tensor-coordinate identification.

The manuscript-specific structured construction is now complete through
Steps 1--3. `InitialNetReduction` constructs the initial Gram factor with the
required `J*K^n` coefficient size. `TensorPartitionReduction` uses balanced
coordinate partitions and actual support bounds
`B_j <= 1+2^(j+1)*K^ceil(n/2^j)`. `WordBallReduction` constructs and counts the
actual single-factor word balls, giving `C_i <= 2*n*3^ceil(ell/2^i)`.
`StructuredCostBounds` proves the finite geometric/logarithmic sums and the
literal product budgets at `n >= n₀(K)`, while `StructuredReductionCosts`
connects them to the constructed stages.

`StructuredLinearization.exists_net_linearization`, with only numeric
`K >= 2` and `n >= n₀(K)` hypotheses, supplies an actual self-adjoint linear
polynomial `H` with

```text
log(2*card(H.Index)) <= 2*K^(2*n)*log(1+2*n).
```

It proves that a relative finite-versus-regular comparison for `H` with
error `exp(-gamma_K*n)/n` transfers to the required net-polynomial bound
`(1+1/n)*c(K,n)`. The initial norm witness, short embedding, every support
count, and the exponential error product are discharged internally. These
are the manuscript's stated deterministic budgets, not merely safe general
substitutes. The separate proof in `HaarPrescribedBound.lean` now supplies the
finite-Haar expectation estimate consumed by this deterministic transfer.

## Unconditional prescribed-dimension realization

`StructuredHaarModel` constructs two independent Haar generators on each
tensor factor and evaluates the proved short words to obtain the required
`K` unitaries. The derived words within a factor are not assumed to be
independent Haar samples. The tensor-word identification, continuity,
integrability, and canonical basis transports are all proved.

The former analytic interface `StructuredHaarConsequences.ExplicitHaarExpectation K n`
is now discharged by `HaarPrescribedDimension.explicitHaarExpectation`.
At `N = ceil(exp(40*(7*ln(K)+2)*n))`, it bounds the actual expected norm of
every permitted self-adjoint linear coefficient polynomial by

```text
integral norm(H(sampleRepresentation omega)) d(sampleMeasure)
  <= norm(H.regularEval)
       * exp(haarLogMultiplier (ln K) n (ln(2*card(H.Index)))).
```

The proof starts with the actual Haar invariant-tensor projection and its
proved spanning family. The Weingarten Gram inverse, weighted inverse
estimate, and singleton-sensitive matching count give actual entry and path
weights. Exact trace expansions produce reduced closed paths; phase
invariance eliminates unsupported paths. Sparse exploration codes count
actual incidence classes, while endpoint-fixed chain permutations prove
invariance of the Haar weight on refined classes.

The refined fibre is proved to correspond exactly to injective vertex labels
and compatible reduced-word profile choices. Noncommutative coefficient
bounds and first/last occurrence contractions control the resulting actual
operator sum. The finite class and length sums give
`HaarPrescribedDimension.onePairLengthBounds` and `onePairTraceBound`.
Successive tensor replacement and exact canonical transport then give the
expectation inequality. Every premise at these interfaces is instantiated
from the actual paths and polynomials in the final theorem.

Two intermediate published counts are repaired, as detailed in
`PROOF_MAP.md`: exploration requires `#importantTimes <= delta+2` and retains
both endpoint color labels; first/last-marker decompositions use the valid
combined exponent `r-1+s <= 6*e-2` instead of the false `r <= 3*e`.
The corrected costs are included in the checked finite sums. Their required
moment condition holds at the original prescribed dimension, so that formula
is unchanged.

Finally, `HaarPrescribedDimension.exists_prescribed_channel` assumes only
`K >= 2` and `n >= Quantitative.n₀ K`. It returns an actual finite CPTP
channel with input dimension `2*N^n*K^(2*n)`, output dimension `K^n`, and,
writing `kappa=(n+1)/(n-1)`, the bounds in bits

```text
0 < chi(T) <= n*log2(1+9/K) + 2*log2(kappa)
n*log2(K)/K <= chi(T tensor T)
n*(log2(K)/K - 2*log2(1+9/K)) - 4*log2(kappa) <= gap(T).
```

The stronger `exists_prescribed_channel_with_lower_bound` includes
`2*n/K <= chi(T)` on the same prescribed channel witness. This lower bound
uses the actual undamped switch/Weyl construction.

The actual family in `HaarPrescribedConsequences.lean` also has the stated
finite regularized-Holevo gain and eventual ratio bounds. For positive
`deltaK`, its gap and regularized gain diverge. `HaarPrescribedScaling.lean`
proves the two-sided linear gap bounds and the gap liminf normalized by the
logarithm of its actual output dimension. The input-qubit expansion is proved
with a remainder tending to zero. These consequences introduce no new
analytic hypothesis. The independent operational coding theorem supplies
the capacity interpretation of the same regularized quantities.

Finite-net sample selection, the uniform adjoint certificate, the Bell
witness, and switch/Weyl conversion are part of this proved chain. No
random-matrix, counting, coefficient, or channel-existence assumption
remains in this theorem. It asserts the prescribed dimension, not its
optimality.

## Regularization and operational capacity

`RegularizedHolevo` constructs the supremum of normalized Holevo information
over all positive actual tensor powers and proves it finite.
`HolevoTensorSuperadditivity` proves superadditivity using actual product
ensembles. `HolevoRateLimit` proves, with no analytic hypotheses,

```lean
FiniteQuantumChannel.normalizedPowerHolevo_tendsto
-- chi(T^(n+1))/(n+1) tends to T.regularizedHolevo.
```

Operational capacity has a separate definition. `Operational.Code T M`
contains actual input density matrices and normalized POVM effects. Its
success is the uniform average Born probability and its error is one minus
success. `CodeSequence T` contains codes on every positive tensor power;
`AchievableRate T R` requires vanishing error and eventual rate at least
every number below `R`. `operationalCapacity` is the supremum of these
achievable rates. No Holevo quantity occurs in those definitions.

The HSW lower bound is proved in `QuantumCodingHSW.lean`. Actual tensor
spectra define global and conditional typical projectors; finite classical
probability estimates give their acceptance, rank, and spectral bounds.
`QuantumCodingUnion` and `QuantumCodingTraceUnion` prove the projective
union bound from Hilbert-space identities. `QuantumCodingSequential`
constructs the normalized filtered sequential POVM, and
`QuantumCodingDecoderBound` proves its error estimate. Exact independent
codebook averaging in `QuantumCodingSampling` and `QuantumCodingPacking`
then selects an actual codebook and POVM with

```text
average error <= 9*epsG + 8*epsQ + 4*(M-1)*a*b.
```

Here the assumptions are explicit projector masses, the average state's
spectral ceiling, and conditional projector rank bounds. Those assumptions
are discharged by the proved typical-projector construction. Integer
message counts and the vanishing-error limit yield
`QuantumCoding.ensemble_rate_achievable` and
`holevoBits_le_operationalCapacity`. `OperationalBlocking` physically
flattens codes for a fixed tensor block and pads unused positions, preserving
the error and scaling the rate by the number of elementary uses. Its scalar
argument covers every positive length, rather than only a block subsequence.

The weak converse is also proved for arbitrary actual codewords and POVMs.
`OperationalNaimark` constructs the decoder dilation;
`QuantumCodingGentle` bounds the disturbance caused by a successful
projection; the quantitative spectral entropy-continuity results control
the resulting information change. `OperationalWeakConverse` proves, in
nats and with output dimension `d`,

```text
log M <= chi(T) + 2*sqrt(2*error)*log(M*d) + 4*log 2.
```

The actual dimension packing bound removes the message-count dependence
from the normalized correction, which tends to zero for any vanishing-error
sequence. Thus the converse has no assumed coding or accessible-information
inequality. The final theorem

```lean
Operational.operationalCapacity_eq_regularizedHolevoSupremum
-- C(T) = sSup (Set.range (normalizedPowerHolevo T)).
```

in `OperationalCodingTheorem.lean` combines this converse with HSW and
physical blocking. For bundled channels,
`FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo` and
`normalizedPowerHolevo_tendsto_classicalCapacity` identify the previously
proved supremum and genuine tensor-power limit with operational capacity.

The full arbitrary-use Weyl identity is proved independently in
`WeylPowersEntropy.lean`. For every actual finite channel with output
`ZMod d`, and every positive `m=n+1`, it proves

```text
chi(W(T)^m) = m*log(d) - minimumEntropy(T^m).
```

The local Weyl twirl is proved on arbitrary joint matrices, including
entangled states. The tensor power of the measured-register extension is
identified with the corresponding joint extension by an exact Kraus
equality with explicit input and environment regrouping.
`WeylPowers.regularized_weylExtension_holevo` further proves the normalized
supremum-minus-infimum identity in bits. No minimizing state, twirling law,
entropy equality, or desired norm bound is supplied as a premise.

The operational scope is finite-dimensional, unassisted classical
communication over a memoryless channel, with arbitrary block input states
and joint POVM decoding. These results do not assert nonadditivity of
operational capacity across different channels, or a strong converse at
every rate above capacity. They also do not close the separately stated
generic Haar convergence interfaces or prove dimension optimality.

The dependency audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. It checks the dependencies of the statements present. The
qualitative and prescribed-dimension channel theorems have no analytic input
premise; older generic convergence interfaces retain their displayed
hypotheses. The coding theorem and arbitrary-use Weyl identities have no
additional analytic or coding hypothesis. This is a statement about the
listed checked results, not a claim that every manuscript assertion has
been formalized.

`RESOURCE_NOTES.md` records the primary mathematical sources, inspected Lean
libraries, and provenance. The deterministic and Gaussian alternatives remain
independent of the completed finite-Haar prescribed-dimension argument; none
of these results is presented as a proof of the older full strong-convergence
predicate.

## Additional completed manuscript claims

- `UniversalFactorization.exists_universal_factorization`: the same coefficients and scalar work in every nonzero complete complex Hilbert-space representation, including infinite dimension.
- `HaarSharpBound.onePairTraceBound`: the original numerical range `2^32*p^80 <= N+1`, using weighted chronological path-class counts.
- `HaarPrescribedRatio`, `HaarInputScaling`, and `HolevoPowerGap`: the exact ratio liminf, matching square-root input scaling, and vanishing normalized gap when regrouping a fixed channel.
- `HaarPrescribedProbability`: the explicit favorable probability fraction for the actual admissible Haar polynomial tests.
- `GapFractionAsymptotics`: the large-K expansion with an explicit remainder bounded by `162/(K^2*ln K)`.
- `PrescribedCostDimensions`, `PrescribedCostScaling`, and `PrescribedCostCapacity`: actual quadratic growing-family input cost and the matching information/capacity estimates in terms of that cost.

These are unconditional proofs of the stated endpoints. They do not assert the broader two-sided Haar strong-convergence predicates, or every background statement at arbitrary traced C*-algebra generality.
