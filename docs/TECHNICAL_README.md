> Technical description of the proof development. For current release commands, metadata,
> and verification status, start with the [repository README](../README.md).

# Nonadditivity: channel constructions and operational coding in Lean

This project formalizes the finite-dimensional quantum construction and
substantial analytic proof components of `nonadditivity.tex`. Channels are
actual rectangular Kraus families, states are actual complex PSD trace-one
matrices, and their entropy and Holevo quantities are defined explicitly.
Entropy concavity, mixture upper bounds, Schmidt equality, tensor additivity,
the local Bell estimate, and switch/Weyl conversion are proved internally.
The full arbitrary-use Weyl-extension identity and the finite-dimensional
operational classical coding theorem are also proved. Operational capacity
is defined independently through physical codes and vanishing decoding
error, then identified with the regularized Holevo supremum.

Unbounded additive and multiplicative nonadditivity are now proved without a
random-matrix hypothesis.
`DeterministicConsequences.exists_small_chi_large_gap_and_ratio` constructs
actual finite channels with arbitrarily small positive single-use Holevo
information, arbitrarily large additive gaps, and arbitrarily large two-use
ratios simultaneously. The corresponding regularized Holevo gain and ratio
are unbounded as well. The proof uses exact finite-group trace moments,
spectral damping, and dimension-independent Bell-output entropy stability.
The earlier rectangular-Gaussian proof remains available as an independent
one-block construction with its own explicit dimensions.

The general Collins--Youn regular-representation norm bound is proved for every
`K >= 2` and `n >= 1`. `ExactQualitative.exists_actual_channel_bounds_with_dimensions`
proves the exact Section 2 existence statement:
`chi <= n*aK + eta` and `chiTwo >= n*log2(K)/K` for every positive eta,
with input dimension `2*N^n*K^(2*n)`, output dimension `K^n`, and strictly
positive chi. Slightly nonuniform branch weights create a Bell entropy
reserve that absorbs the entire damping error. That deterministic construction
does not prove Haar convergence; the separate finite-Haar argument below now
proves the prescribed-dimension result.

The manuscript's prescribed-dimension channel theorem is now unconditional.
`HaarPrescribedDimension.exists_prescribed_channel` in `HaarPrescribedBound.lean`
proves the exact input/output dimensions and the stated one-use, two-use, and
additive-gap bounds, under only `K >= 2` and `n >= n₀(K)`. Its proof constructs
the actual Haar integrals, Weingarten estimates, path classes and coefficient
sums, then performs tensor replacement and the established structured
linearization. Two incorrect intermediate counts in the published reference
are repaired without changing the manuscript's prescribed dimension. No
optimality of that dimension is claimed. There are no placeholder proofs or project-specific axioms in the proof library.
The isolated Comparator expected statements are documented separately.

The revised manuscript is *Unbounded Holevo additivity gaps in finite
dimensions*, supplied on October 2, 2026 UTC. Its repository SHA-256 is
`3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98`.
It incorporates both counting repairs. Two repository clarifications align
the exploration encoding and verification status with the recorded Lean work;
[metadata/results.json](../metadata/results.json) retains the supplied-file hash
and adjustment provenance.

## Reproduce the verification

The toolchain is Lean `4.29.0-rc6`, with mathlib pinned to
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`.

With Lean/elan installed, restore dependencies once:

```sh
lake exe cache get
lake build All
./check.sh
```

The included `lake-manifest.json` records the exact dependency revisions.
Do not regenerate it during ordinary reproduction; dependency updates are a separate change.
On the machine used for verification, existing dependency caches were mounted
without modification. These local cache symlinks are not included in the
archive; a fresh checkout uses the commands above.

`check.sh` builds every proof-library module (excluding Comparator challenges) and then runs `Audit.lean`, writing
`.lake/check.log`. The archive also contains the successful verification log.
The axiom audit traverses every project declaration and its dependencies;
only Lean's usual `propext`, `Classical.choice`, and `Quot.sound` are permitted.
It rejects `sorryAx`, other axioms, and any local module omitted from the audit
import closure. Explicit theorem hypotheses are not axioms, and their
mathematical interpretation must still be checked by the reader.

To check one file with cached dependencies:

```sh
./lean.sh Nonadditivity/Entropy.lean
```

The wrapper serializes local compiler runs to limit memory use. Set
`NONADDITIVITY_LEAN` or `NONADDITIVITY_LEAN_PATH` if using a nonstandard
compiler/cache location.

## What is actually formalized

| File | Checked content | Boundary |
|---|---|---|
| `ExactQualitative.lean` | Exact Section 2 qualitative existence bounds, positive Holevo information, and input/output dimensions | Unconditional; this separate deterministic route does not bound its local dimension by the prescribed formula |
| `FiniteFreeModel.lean`, `FiniteRegularMatrix.lean`, `FiniteMomentMatching.lean`, `FiniteBlockModel.lean` | Actual finite groups and regular matrices; exact bounded-word trace moments; concrete block adjoint moment bound | No Haar or assumed moment estimate |
| `SpectralDamping.lean`, `DampedChannel.lean`, `DampingNet.lean`, `DampedRealization.lean` | Explicit invertible damping, complete Kraus family, finite-net certificate, and arbitrarily small normalized trace loss | Moment order is chosen before input dimension |
| `DampedBellStability.lean`, `EntropyContinuity.lean`, `EntropyStability.lean`, `CanonicalBlockBell.lean` | Canonical Bell identification and uniform entropy stability under damping | Threshold depends only on fixed output dimension |
| `WeightedBellScalar.lean`, `WeightedBell.lean`, `WeightedBlock.lean`, `WeightedBlockBell.lean`, `WeightedCertificate.lean`, `WeightedParameters.lean` | Actual weighted channels, strict Bell reserve, and perturbation certificate fitting any positive single-use tolerance | Eliminates the two-use error in the qualitative theorem |
| `StrictEntropy.lean`, `DampedPositivity.lean`, `WeightedPositivity.lean` | Nonuniform outputs imply strict entropy deficit; inverse damping preserves positive converted information | Does not assert the original undamped construction's numerical lower bound `2*n/K` |
| `DeterministicQualitative.lean`, `DeterministicConsequences.lean` | Unconditional finite-block realization with arbitrary slack and actual families with vanishing information, diverging additive gaps, and unbounded two-use/regularized ratios | The operational interpretation follows from the separately proved coding theorem |
| `Entropy.lean` | Finite distributions; actual complex PSD trace-one matrices; spectral entropy; entropy versus purity; centered trace identities; entropy invariance; Bell-vector invariance; exact Bell weight entropy | Natural-log entropy convention; no channel-existence assertion |
| `Channels.lean`, `ChannelReindex.lean` | Actual CPTP Kraus channels, adjoints, Stinespring matrices, tensor products, complements, conjugates, and basis/environment relabeling | Kraus completeness is part of the channel data and all claimed map properties are derived |
| `ComplementaryAdjoint.lean` | Actual complementary Gram entries and adjoints; normalized tensor words; the exact finite block adjoint polynomial in the manuscript coordinates | The polynomial identity is proved; the prescribed-dimension norm estimate is supplied by `HaarPrescribedBound.lean` |
| `AdjointPurity.lean`, `QuantumHolevo.lean` | Actual state expectation estimate; full channel adjoint-certificate-to-purity/entropy theorem; Holevo quantity over finite actual output ensembles | The generic entropy interface consumes an adjoint norm certificate, constructed in the final channel proofs |
| `EntropyProducts.lean`, `PureChannelEntropy.lean`, `TensorPowers.lean` | Actual tensor density matrices and finite channel blocks; entropy additivity; rectangular Gram/Schmidt entropy equality; rank-one entropy zero; pure-input channel/complement entropy equality | No tensor or complementary entropy law is assumed |
| `EntropyMixtures.lean` | Actual quantum entropy pinching and concavity; full finite mixed-state ensemble entropy upper bound | Derived through spectral amplitudes and proved Gram equality |
| `BellOutput.lean`, `BlockBell.lean` | Normalized Bell state; actual merged ensemble; local and finite-block complementary-channel Bell entropy bounds; explicit paired-block witness and input/output/Kraus regrouping | All entropy and output-factorization steps are derived internally |
| `StateEnsembles.lean`, `ConditionalStates.lean` | Actual normalized matrix mixtures and finite coding ensembles; conditional states, including zero-probability branches; output-family Holevo supremum and entropy infimum | No entropy minimizer is assumed |
| `Weyl.lean`, `WeylTensor.lean`, `WeylPowersIndex.lean`, `WeylPowersControl.lean`, `WeylPowersChannels.lean`, `WeylPowersTwirl.lean`, `WeylPowersEntropy.lean`, `WeylPowersRegularized.lean` | Actual shift/phase unitaries, every positive local tensor twirl, exact Kraus-register regrouping, finite orbit ensembles, and the full arbitrary-use Holevo/minimum-output-entropy equality | No concavity, twirling, minimizing-state, or desired-equality premise; the regularized supremum-minus-infimum identity is also proved |
| `ChannelExtensions.lean`, `ChannelEntropy.lean`, `SwitchChannel.lean`, `Conversion.lean` | Actual measured-register, switch, and Weyl channels; exact single-use Holevo/minimum-entropy equality; two-use lower bound and entropy-gap conversion on entangled inputs | The generic conversion takes an adjoint certificate and joint input; `BlockConstruction.lean` supplies the actual Bell input and `Qualitative.lean` realizes the certificate from norm inputs |
| `Net.lean`, `FiniteRealization.lean`, `FiniteChannelRealization.lean` | Compact unit-sphere nets; prescribed/symmetric tests; finite probability selection; concrete HS observable subspace and channel-adjoint transfer from convergence in probability | These reusable convergence-based interfaces retain that premise; the final prescribed-dimension proof uses a direct finite expectation estimate |
| `BlockConstruction.lean`, `Qualitative.lean` | Complete actual block-channel, Bell-witness, switch/Weyl, and finite-realization integration; exact output/input dimensions and final Holevo gap bounds | Their generic interfaces accept norm inputs; `HaarConsequences.lean` supplies the proved free bound and leaves only canonical Haar convergence |
| `HolevoBits.lean` | Base-two Holevo quantity on the same actual output ensembles; exact qualitative bounds in the manuscript's units | Inherits the analytic norm inputs of qualitative realization |
| `FreeModel.lean`, `FreeBridge.lean` | Actual product free group, bounded left-regular representation, normalized comparison polynomial, and exact trace/HS-preserving transport to the block output basis | `CollinsYounProduct.collinsYounBound` proves `CollinsYounBound K n` for every `K >= 2`, `n >= 1` |
| `HaarModel.lean` | Compact finite unitary groups, normalized Haar probability, independent product sampling, exact coordinate laws, polynomial continuity, measurable failure events, and specialized channel realization | The precise `HaarStrongConvergence` predicate remains unproved |
| `HaarMoments.lean`, `HaarFourthMoments.lean` | Zero entry means, exact second covariance, conjugation twirl, independent-product moments, exact fourth absolute moment and distinct-row same-column mixed square moment | Low-order identities; the growing-order path estimate is proved separately |
| `HaarMomentTail.lean` | Actual Hermitian trace powers dominate norm powers; trace-moment Markov bound; normalized version with the exact dimension factor; canonical Haar specialization with varying moment order | The vanishing high-trace-moment ratio remains a premise |
| `UpperHaarRealization.lean` | Finite-net realization, actual channel bounds, arbitrarily large additive gaps, and one-block arbitrarily large ratios from upper tails alone; direct realization from the explicit high-trace-moment criterion | `HaarUpperConvergence` and the sufficient `HaarTraceMomentControl` remain unproved; no lower spectral convergence is required |
| `PositiveHolevo.lean` | Actual normalized eigenvector, merged equal pure outputs, block entropy witness, and universal `chi_bits >= 2*n/K` | No Collins–Youn or convergence hypothesis is needed |
| `ActualConsequences.lean`, `HaarConsequences.lean` | Actual finite CPTP channel family with vanishing single-use information, diverging two-use information, additive gap, and genuine ratio with positive denominator | `HaarConsequences` discharges the global Collins--Youn input internally; only `AllHaarStrongConvergence` remains |
| `PositiveLinearization.lean`, `RegularCoefficientEnergy.lean`, `FiniteSetFactorization.lean`, `MatrixNormReindex.lean`, `RegularDilation.lean`, `RegularFactorization.lean` | Actual positive Gram assembly, square coefficients, norm identities for every finite unitary representation and the infinite left-regular representation, correction bound, and backward relative error transfer | Transfer uses its displayed factor norm comparison; the extension to arbitrary nonzero complete Hilbert-space representations is proved in `UniversalFactorization.lean` |
| `FreeEmbedding.lean`, `RegularRestriction.lean`, `ShortEmbeddingNorm.lean`, `MatrixRegularRestriction.lean`, `MatrixShortEmbedding.lean` | Actual logarithmic-length injective free embedding, subgroup coset decomposition, and exact regular polynomial norm preservation at every finite matrix size, with coordinate and total degree bounds | These construction, restriction, and amplification steps have no analytic norm hypotheses |
| `FreeCreation.lean`, `CollinsYoun.lean`, `CollinsYounOne.lean`, `CollinsYounTensor.lean`, `RegularFubini.lean`, `CollinsYounProduct.lean` | Actual cone projections, operator-valued three-term length-two estimate, product-Hilbert Fubini isometry, diagonal/off-diagonal energy induction, and exact general Collins--Youn bound | No analytic norm hypothesis remains in `CollinsYounProduct.collinsYounBound` |
| `OneBlockRealization.lean` | Actual one-block channel bounds, strict nonadditivity, and arbitrarily large two-use and regularized ratios | Only canonical one-block Haar strong convergence is assumed; the free bound is proved internally |
| `RegularizedHolevo.lean`, `HolevoTensorSuperadditivity.lean`, `HolevoRateLimit.lean` | Actual product ensembles, Holevo superadditivity, tensor reassociation, and convergence of all positive normalized tensor-power rates to their bounded supremum; unbounded regularized gain and ratio | `OperationalCodingTheorem.lean` proves equality with independently defined operational capacity |
| `Linearization.lean`, `PolynomialReduction.lean`, `ProductPolynomialReduction.lean` | Actual recursive coefficient polynomials reduce support of degree `2^k` to linear support in free groups and product free groups; exact dimension multiplier, backward error cost, and safe product-support cost bounds | The general reductions have safe costs; `StructuredLinearization.lean` proves the exact budgets used by the unconditional prescribed-dimension theorem |
| `Quantitative.lean` | Exact threshold, exponent and tolerance constants; scalar coefficient/error bounds; exponential tails; integer dimension and moment rounding; scalar Haar-error assembly | These scalar budgets are now connected to the proved finite-Haar estimates in `HaarPrescribedBound.lean` |
| `Holevo.lean`, `Purity.lean` | Reusable abstract variational and Hilbert-space witness arguments | These generic interfaces coexist with the concrete matrix/channel instantiations above |
| `Scalar.lean`, `BlockScalars.lean` | Base-two and natural-log constants; exact block purity corrections; gap and capacity algebra | Capacity/coding inputs remain explicit |
| `Asymptotics.lean` | Actual rounded block-length sequence; separation limits; finite-size correction; eventual linear gaps and ratios; liminf estimates; fixed-channel regrouping | `DeterministicConsequences.lean` supplies an unconditional actual family; the coding theorem gives the regularized quantities their operational meaning |
| `QuantitativeNet.lean`, `ObservableDimension.lean` | Volume packing, symmetric sphere nets containing a prescribed test and its negative with no cardinality overhead; exact real observable dimension `d^2-1`; radius-`1/n` net bound `(1+2*n)^(d^2-1)` | Combined with the proved quantitative Haar estimate in `HaarPrescribedBound.lean` |
| `ShiftNorm.lean`, `PrescribedTest.lean`, `NetPolynomial.lean` | Exact regular shift norm; an actual unit-HS traceless test of free norm `sqrt(2)*K^(-(n+1)/2)`; a symmetric observable net with the stated cardinality bound assembled into an actual matrix-coefficient polynomial, with exact block norms, spectral symmetry, and positive shift identity | The deterministic construction and its required Haar estimate are proved |
| `NetPolynomialSupport.lean` | Collects repeated words into an actual `PolynomialReduction.Polynomial`, preserving regular evaluation and finite evaluation norm exactly | Connects the literal observable-net polynomial to the constructed support-reduction API |
| `InitialNetReduction.lean`, `TensorPartitionReduction.lean`, `WordBallReduction.lean`, `StructuredLinearization.lean` | Actual initial Gram coefficients, balanced coordinate supports, finite reduced-word balls, repeated norm transfer, and final Hermitian linear polynomial; `exists_net_linearization` assembles the prescribed net and short embedding | Only numeric `K >= 2`, `n >= n₀(K)` hypotheses; the final Haar comparison is supplied by `HaarPrescribedDimension.explicitHaarExpectation` |
| `StructuredCostBounds.lean`, `StructuredReductionCosts.lean` | Literal support products and actual coefficient/error costs obey `T_n <= exp(gamma_K*n)` and `log(2*m_n) <= 2*K^(2*n)*log(1+2*n)` | The manuscript's exact deterministic budgets are proved; no support-count or summed-log hypothesis is left in the assembled theorem |
| `StructuredFiniteChannel.lean`, `StructuredHaarModel.lean`, `StructuredHaarConsequences.lean` | Actual independent Haar pairs, evaluation of the short generator words, polynomial integrability, finite-net certificate, exact input dimension, and converted channel bounds at `N = ceil(exp(b_K*n))` | These reusable interfaces accept `ExplicitHaarExpectation K n`; `HaarPrescribedDimension.explicitHaarExpectation` discharges it |
| `HaarInvariantSpanning.lean`, `HaarWeingartenGram.lean`, `HaarWeingartenInverse.lean`, `HaarEntryBound.lean`, `HaarPairEntryBound.lean` | Actual invariant-tensor spanning, inverse Gram formula, weighted inverse bounds, and singleton-sensitive entry moments | Derived from normalized Haar integration; no moment or matching estimate assumed |
| `HaarPathWeights.lean`, `HaarPathSupport.lean`, `HaarPathCounting.lean`, `HaarRefinedWeight.lean` | Literal path expectations, support vanishing, corrected class count, and refined-class weight invariance | Actual reduced closed paths, including loops and terminal tree edges |
| `HaarRefinedPaletteFibre.lean`, `HaarRefinedCoefficientBound.lean`, `HaarPathClassAssembly.lean` | Exact refined fibres, noncommutative coefficient sums, and full path-class summation | All counting, factorization, and coefficient premises discharged in the final assembly |
| `HaarTensorReplacement.lean`, `HaarIteratedMoments.lean`, `HaarCanonicalTransport.lean`, `HaarExpectationFromMoment.lean`, `HaarPrescribedBound.lean` | One-pair trace comparison, successive tensor replacement, exact canonical transport, expected norm bound, and actual prescribed-dimension channel | Unconditional under the displayed numerical thresholds; no dimension-optimality claim |
| `GaussianQuadratic.lean`, `GaussianCertificates.lean`, `QuadraticNet.lean` | Exact Gaussian quadratic integrals, spectral MGF and two-sided tail bounds, explicit union-bound budget, and actual input/observable nets | Concentration is proved internally, without a Haar convergence hypothesis |
| `GaussianRectangular.lean`, `ComplexRealTrace.lean`, `GaussianRectangularAlgebra.lean`, `GaussianSampleEvaluation.lean` | Actual complex rectangular Gaussian matrix, exact real quadratic-form norm/trace/variance, and identification with the sampled channel's quadratic forms | Uses the concrete Gaussian probability space and exact matrix identities |
| `GaussianNormalization.lean`, `GaussianNetRealization.lean`, `GaussianConstruction.lean` | Constructed inverse square root and normalized isometry; actual finite channel with uniform adjoint bound `512/K` | Existence is proved for `K >= 4096`, environment/input parameter `N >= K^2` |
| `GeneralBell.lean`, `GaussianChannelBounds.lean`, `GaussianScalar.lean`, `GaussianConsequences.lean` | Actual Bell overlap and entropy bounds, switch/Weyl conversion, positive information, unbounded two-use and regularized ratios, and arbitrarily small single-use information | This route supplies multiplicative separation; the deterministic route supplies unbounded additive gaps and the independent coding theorem identifies regularized information with capacity |
| `Dimensions.lean` | Exact input dimension and qubit formula; exponential-ceiling logarithm error; vanishing remainder in the stated quadratic input-size formula | The final channel theorem realizes these exact dimensions |
| `Main.lean` | Connects concrete density-matrix purity to the block entropy bound and its infimum; quantitative gap consequences | Numerical interface; the unconditional prescribed-dimension channel theorem is in `HaarPrescribedBound.lean` |
| `OperationalConverse.lean`, `OperationalCapacity.lean` | Actual input-state encoders, normalized POVM decoders, Born probabilities, average error, code sequences at every positive length, and operational capacity defined from achievable rates | The operational definition is independent of the Holevo supremum |
| `QuantumCodingTypicality.lean`, `QuantumCodingTypicalProjectors.lean`, `QuantumCodingEnsembleTypicality.lean`, `QuantumCodingTypicalTests.lean` | Actual tensor spectra, global and conditional typical projectors, quantitative acceptance probabilities, and averaged independent interference bounds | Derived from the actual ensemble and finite classical probability estimates |
| `QuantumCodingUnion.lean`, `QuantumCodingTraceUnion.lean`, `QuantumCodingSequential.lean`, `QuantumCodingDecoderBound.lean`, `QuantumCodingSampling.lean`, `QuantumCodingPacking.lean` | Projective union bound, complete sequential POVM, deterministic error estimate, exact independent-codebook averages, and existence of a physical decoder with error at most `9*epsG+8*epsQ+4*(M-1)*a*b` | No decoding-error inequality is assumed |
| `QuantumCodingChannelWords.lean`, `QuantumCodingRates.lean`, `QuantumCodingHSW.lean` | Actual channel-code lifting, rounded exponential message counts, vanishing error, and HSW achievability for every finite input ensemble | Proves `holevoBits <= operationalCapacity` for an arbitrary finite Kraus channel |
| `QuantumCodingContinuity.lean`, `QuantumCodingTraceDistance.lean`, `QuantumCodingGentle.lean`, `OperationalNaimark.lean`, `OperationalProjectedCode.lean`, `OperationalWeakConverse.lean` | Quantitative spectral entropy continuity, gentle projection, actual POVM dilation, and a finite-code weak converse whose normalized correction vanishes with decoding error | Applies to arbitrary codewords and POVMs; no accessible-information or coding-converse premise |
| `OperationalBlockingCodes.lean`, `OperationalBlockingFlatten.lean`, `OperationalBlockRates.lean`, `OperationalBlocking.lean` | Actual code flattening and padding, preserved error, and rate rescaling from a fixed block to every positive channel length | Does not restrict operational achievability to a subsequence |
| `OperationalCodingTheorem.lean` | Equality of independently defined operational capacity, the regularized Holevo supremum, and the actual tensor-power rate limit | Arbitrary finite Kraus channels with nonempty input/output spaces; no coding theorem is an assumption |

Matrix spectral entropies in `Entropy.lean` use natural logarithms.
`Scalar.log2` and the statements in `Main.lean`, `Dimensions.lean`, and the
information bounds in `Asymptotics.lean` convert to bits explicitly.
`HolevoBits.exists_block_channels_bits` supplies the qualitative channel
construction in bits: `chi(T) <= n*aK + eta`,
`chi(T tensor T) >= n*log2(K)/K`, and gap `>= n*deltaK - 2*eta`.
Its free-model comparison hypothesis is supplied by
`FreeBridge.outputFreeNorm_unit_bound (CollinsYounProduct.collinsYounBound hK hn)`.

For fixed `K >= 2`, `n >= 1`, and `epsilon > 0`, the checked
`Qualitative.qualitative_realization_of_CY_and_strong_convergence` supplies
an actual CPTP channel `T` with output dimension `K^n` satisfying

```text
chi(T) <= n * log(1 + 9/K) + epsilon
chi(T tensor T) >= n * log(K)/K
chi(T tensor T) - 2 * chi(T) >= n * gapCoefficient(K) - 2 * epsilon.
```

The specialization in `HaarModel` fixes the probability spaces and unitary
samples to the actual independent normalized Haar model. The newer
`HaarConsequences.exists_block_channel` supplies the general Collins--Youn bound
internally and states the resulting bounds in bits, with positive single-use
Holevo information proved. Its only analytic premise is
`HaarModel.HaarStrongConvergence K n` for that fixed block. The newer
`UpperHaarRealization.exists_block_channel` proves the same bounds from only
`HaarUpperConvergence K n`; `exists_block_channel_of_trace_moments` takes the
explicit sufficient high-trace-moment criterion instead.

The canonical Haar index `N` denotes local dimension `N+1`, so the selected
channel input dimension is exactly `2*(N+1)^n*K^(2*n)`. The generic sampling
interface instead denotes the local dimension directly by `N`. Neither
qualitative theorem gives a numerical upper bound on the selected dimension.
The existential realization uses a nontrivial filter.

`HaarConsequences.exists_separating_family` proves vanishing single-use
information, diverging two-use information, and unbounded additive and
multiplicative separation for actual finite channels from
`AllHaarStrongConvergence`. The corresponding regularized gain and ratio
statements use the genuine tensor-power rate limit: for every finite channel,
`FiniteQuantumChannel.normalizedPowerHolevo_tendsto` identifies that limit with
`regularizedHolevo`.

## Unconditional prescribed dimension

`HaarPrescribedDimension.exists_prescribed_channel` proves that, for
`K >= 2` and `n >= Quantitative.n₀ K`, where
`n₀(K)=ceil(256*(1+ln(K))^2)`, an actual finite CPTP channel exists with local dimension
`N = ceil(exp(40*(7*ln(K)+2)*n))`, input dimension `2*N^n*K^(2*n)`, and
output dimension `K^n`. With `kappa=(n+1)/(n-1)`, its bounds in bits are

```text
0 < chi(T) <= n*log2(1+9/K) + 2*log2(kappa)
chi(T tensor T) >= n*log2(K)/K
gap(T) >= n*(log2(K)/K - 2*log2(1+9/K)) - 4*log2(kappa).
```

`HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound` gives
these bounds and `2*n/K <= chi(T)` for the same channel, with the same exact
dimensions and numerical assumptions.

`HaarPrescribedConsequences.lean` and `HaarPrescribedScaling.lean` select one
actual prescribed channel family and prove its regularized-Holevo gain bound,
eventual ratio bounds, linear gap bounds when `deltaK > 0`, the output-normalized
gap liminf, and the quadratic input-qubit expansion with vanishing remainder.
The regularized quantity is the proved tensor-power Holevo rate.

`HaarPrescribedDimension.explicitHaarExpectation` proves the literal expected
operator-norm inequality previously supplied as an analytic hypothesis.
`onePairLengthBounds` and `onePairTraceBound` connect the actual path and
coefficient estimates to tensor replacement. The independent samples are two
Haar unitaries on each tensor factor; the derived `K` words are evaluated
exactly, without assuming that those words are independent Haar samples.

`PROOF_MAP.md` describes the full dependency chain and both corrected
published intermediate counts. Their costs are included in the checked
moment estimates and absorbed by the existing dimension budget. The
prescribed formula is unchanged; optimality is not proved.

## Operational classical coding and all-use Weyl conversion

`Operational.Code T M` consists of `M` actual input density matrices and a
normalized POVM. Its success probability is the uniform average of the
Born probabilities, and its error is one minus that success probability.
`CodeSequence T` supplies such codes on every actual positive tensor power.
`AchievableRate T R` requires error tending to zero and rate eventually at
least every real number below `R`. `operationalCapacity` is the supremum of
these achievable rates. These definitions do not mention Holevo information.

The HSW proof constructs global and conditional typical projectors from the
actual tensor spectra. A projective union bound controls an explicit
sequential POVM, and finite independent codebook averaging selects codes
with error at most `9*epsG+8*epsQ+4*(M-1)*a*b`. The spectral acceptance and
interference estimates, integer message counts, channel lifting, and
vanishing-error limit are all proved. `QuantumCoding.ensemble_rate_achievable`
and `holevoBits_le_operationalCapacity` are the resulting achievability
theorems. Physical tensor regrouping and padding in `OperationalBlocking`
then make every normalized block Holevo quantity a capacity lower bound at
all sufficiently large lengths.

The weak converse applies to arbitrary actual codes. It constructs a POVM
dilation, normalizes its successful projected states, and bounds their
disturbance and entropy changes. For an output space of dimension `d`,
`Operational.Code.log_messages_le_holevo_add_error` proves, in nats,

```text
log M <= chi(T) + 2*sqrt(2*error)*log(M*d) + 4*log 2.
```

The dimension packing bound removes `M` from the normalized correction;
that correction tends to zero on every vanishing-error code sequence.
Consequently `Operational.operationalCapacity_eq_regularizedHolevoSupremum`
proves

```text
C(T) = sup_n chi_bits(T^(n+1))/(n+1).
```

For bundled finite channels,
`FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo` and
`normalizedPowerHolevo_tendsto_classicalCapacity` identify the previously
formalized supremum and limit with this independently defined capacity.
The operational quantities concern ordinary finite-dimensional unassisted
classical communication over a memoryless channel. This theorem and the
channel constructions do not assert nonadditivity of `C(T)` across two
different channels or a strong converse at every rate above `C(T)`.

The arbitrary-use Weyl-extension equality is proved by
`WeylPowers.positiveTensorPower_weylExtension_holevo` and its version in bits.
For `m=n+1`, the actual tensor powers satisfy
`chi(W(T)^m)=m*log(d)-minimumEntropy(T^m)`. Independent local Weyl twirling
is proved for arbitrary joint matrices, and the measured input registers are
regrouped by an explicit Kraus equality. `regularized_weylExtension_holevo`
also identifies the all-use Holevo supremum with `log2(d)` minus the infimum
of normalized minimum output entropies in bits. The universal lower bound
`chi_bits(T) >= 2*n/K` for the original converted blocks remains the theorem
in `PositiveHolevo.lean`.


## Scope outside the proved channel theorem

The older predicates `HaarModel.HaarStrongConvergence`,
`HaarConsequences.AllHaarStrongConvergence`,
`UpperHaarRealization.HaarUpperConvergence`, and `HaarTraceMomentControl`
remain unproved in their stated generality. They describe separate
convergence interfaces and are not premises of the new prescribed-dimension
channel theorem. In particular, no lower spectral convergence theorem is
claimed.

The coding theorem identifies the actual tensor-power Holevo limit with
operational classical capacity. The remaining boundaries concern the
separately stated generic analytic interfaces and the precise scope of the
channel constructions, rather than an assumed coding theorem.


`OneBlockRealization.exists_arbitrarily_large_ratio` and
`exists_arbitrarily_large_regularized_ratio` retain the weaker assumption of
only one-block canonical Haar convergence. Their explicit ratio lower bound
is `log(K)/36`, with a positive denominator. The newer
`UpperHaarRealization.exists_arbitrarily_large_ratio` needs only one-block
upper tails; `exists_arbitrarily_large_gap_of_all_upper` needs upper tails
for all fixed blocks. Neither requires a lower norm estimate or an unproved
Collins--Youn bound. The older simultaneous separating-family interface
continues to use full strong convergence.

The separate Gaussian construction removes the analytic premise for
multiplicative separation: for every `epsilon > 0` and real `R`,
`GaussianConsequences.exists_small_chi_large_ratio` gives an actual channel
with `0 < chi(T) <= epsilon` and `R <= chi(T tensor T)/(2*chi(T))`.
`exists_small_chi_large_regularized_ratio` gives the corresponding ratio for
the proved regularized Holevo limit. For each `K >= 4096`,
`exists_channel_bounds` has input dimension `2*K^4`, output dimension `K`,
single-use upper bound `512^2/(K*ln(2))`, and two-use ratio lower bound
`(ln(K)-1)/(2*512^2)`. These bounds give strict nonadditivity but do not give
arbitrarily large additive gaps.

The final prescribed-dimension theorem has no analytic input premise. Older
generic convergence interfaces retain the hypotheses displayed in their
statements.
`PROOF_MAP.md` gives representative theorem names and manuscript locations.

## Dependency provenance

mathlib is used by import, at the revision above; its upstream license is
Apache 2.0. No external repository was modified, and no generated proof was
published to an external git repository. The deliverable does not bundle
mathlib or its binary cache.


`RESOURCE_NOTES.md` records the online sources and Lean repositories inspected,
including limitations of other libraries and the mathematical provenance of
the implemented Haar and Gaussian arguments. Attribution and license notices
for adapted external proof patterns remain in `THIRD_PARTY_NOTICES.md`.

## Additional completed manuscript claims

- `UniversalFactorization.exists_universal_factorization`: the same coefficients and scalar work in every nonzero complete complex Hilbert-space representation, including infinite dimension.
- `HaarSharpBound.onePairTraceBound`: the original numerical range `2^32*p^80 <= N+1`, using weighted chronological path-class counts.
- `HaarPrescribedRatio`, `HaarInputScaling`, and `HolevoPowerGap`: the exact ratio liminf, matching square-root input scaling, and vanishing normalized gap when regrouping a fixed channel.
- `HaarPrescribedProbability`: the explicit favorable probability fraction for the actual admissible Haar polynomial tests.
- `GapFractionAsymptotics`: the large-K expansion with an explicit remainder bounded by `162/(K^2*ln K)`.
- `PrescribedCostDimensions`, `PrescribedCostScaling`, and `PrescribedCostCapacity`: actual quadratic growing-family input cost and the matching information/capacity estimates in terms of that cost.

These are unconditional proofs of the stated endpoints. They do not assert the broader two-sided Haar strong-convergence predicates, or every background statement at arbitrary traced C*-algebra generality.
