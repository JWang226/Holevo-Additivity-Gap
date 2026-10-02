# A route through the Holevo additivity-gap proof

Start with the main statements below, then follow the prescribed-dimension route or the alternative qualitative route. Both produce actual finite Kraus CPTP channels. The operational coding theorem connects their information bounds to communication rates.

This is a **mathematical reading guide**, not a complete kernel dependency graph. Each landmark names an exact declaration and links its source; a source file can also contain conditional interfaces or other results. The theorem's type, its definitions, and its proof determine its assumptions. Use [metadata/results.json](metadata/results.json) for the full manuscript-label correspondence and [docs/PROOF_MAP.md](docs/PROOF_MAP.md) for finer detail.

## Main statements to inspect first

All information quantities below are in bits. For a channel `T`, `T.chi` is `χ(T)`, `T.chiTwo` is `χ(T ⊗ T)`, `T.gap` is `χ(T ⊗ T) − 2χ(T)`, and `T.twoUseRatio` is `χ(T ⊗ T)/(2χ(T))`. These quantities use actual channel outputs and density-matrix ensembles; they are defined in [ActualConsequences.lean](Nonadditivity/ActualConsequences.lean). Operational capacity has a separate definition through physical codes.

| Endpoint | Exact Lean declaration |
| --- | --- |
| Prescribed input/output dimensions and one-use/two-use bounds, including a positive same-witness lower bound | [`Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound`](Nonadditivity/HaarPrescribedBound.lean) |
| Classical capacity equals regularized Holevo information | [`Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum`](Nonadditivity/OperationalCodingTheorem.lean) |
| Arbitrarily small positive one-use information, arbitrarily large capacity gain, and arbitrarily large two-use ratio | [`Nonadditivity.OperationalConsequences.exists_small_chi_large_capacity_gain_and_two_use_ratio`](Nonadditivity/OperationalConsequences.lean) |
| Independent qualitative construction for every `K ≥ 2`, `n ≥ 1`, and positive tolerance | [`Nonadditivity.ExactQualitative.exists_actual_channel_bounds_with_dimensions`](Nonadditivity/ExactQualitative.lean) |
| Weyl-extension identity at every positive tensor power | [`Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits`](Nonadditivity/WeylPowersEntropy.lean) |
| Information and capacity lower bounds in terms of actual input-qubit cost | [`Nonadditivity.PrescribedCost.growingFamily_two_use_input_cost_lower`](Nonadditivity/PrescribedCostCapacity.lean) |

For the quantitative endpoint, let

\[
n_0(K)=\lceil256(1+\ln K)^2\rceil,
\quad N=\lceil\exp(40(7\ln K+2)n)\rceil,
\quad\kappa_n=\frac{n+1}{n-1},
\quad\delta_K=\frac{\log_2 K}{K}-2\log_2(1+9/K).
\]

For `K ≥ 2` and `n ≥ n₀(K)`, the theorem constructs a channel of input dimension `2NⁿK²ⁿ` and output dimension `Kⁿ` with

\[
\begin{aligned}
0<\frac{2n}{K}\le\chi(T)
&\le n\log_2(1+9/K)+2\log_2\kappa_n,\\
\chi(T\otimes T)&\ge\frac{n\log_2 K}{K},\\
\chi(T\otimes T)-2\chi(T)
&\ge n\delta_K-4\log_2\kappa_n.
\end{aligned}
\]

The numerical conditions are its only non-typeclass hypotheses. No Haar expectation or coding theorem is left as a premise. The dimensions are sufficient; no optimality of the input dimension is claimed.

## Prescribed-dimension route

Read the following stages in order. The operator estimates control every traceless Hermitian observable, giving a uniform single-use entropy bound. A specific entangled Bell input gives the complementary two-use bound. Switching between a channel and its conjugate and then applying a Weyl extension converts these entropy estimates into the Holevo gap.

| Stage | Mathematical role | Lean landmarks |
| --- | --- | --- |
| 1. Concrete channel and entropy objects | Rectangular Kraus matrices give CPTP maps; outputs are positive semidefinite, trace-one complex matrices. Entropy/purity inequalities handle zero eigenvalues. | [Channels.lean](Nonadditivity/Channels.lean), [Entropy.lean](Nonadditivity/Entropy.lean); `Nonadditivity.Entropy.DensityMatrix.vonNeumann_ge_neg_log_purity` |
| 2. Free-operator comparison | Creation/annihilation estimates and tensor induction prove the normalized Collins–Youn bound for all `K ≥ 2`, `n ≥ 1`. This supplies the comparison norm rather than assuming it. | [`Nonadditivity.CollinsYounProduct.collinsYounBound`](Nonadditivity/CollinsYounProduct.lean) |
| 3. Finite-net and polynomial reduction | A net of traceless Hermitian observables reduces the uniform norm question to finite tests; degree reduction and finite-set linearization track dimension and error costs. | [InitialNetReduction.lean](Nonadditivity/InitialNetReduction.lean), [StructuredLinearization.lean](Nonadditivity/StructuredLinearization.lean), [FiniteSetFactorization.lean](Nonadditivity/FiniteSetFactorization.lean) |
| 4. Corrected Haar counting and coefficients | Chronological path classes, marked positions, and operator coefficient estimates control literal Haar moments. Two intermediate manuscript counting claims are replaced by proved bounds. | [`Nonadditivity.HaarPathClasses.card_defectClass_weighted_le`](Nonadditivity/HaarSharpCounting.lean); [`Nonadditivity.HaarOperatorPathBridge.coefficient_bound`](Nonadditivity/HaarRefinedCoefficientBound.lean) |
| 5. Haar expectation and finite realization | The actual specialized Haar integral meets the tracked moment/error budgets. The expectation bound supplies a favorable finite-dimensional realization and the adjoint certificate. | [`Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation`](Nonadditivity/HaarPrescribedBound.lean); [`Nonadditivity.StructuredHaarConsequences.exists_explicit_certificate`](Nonadditivity/StructuredHaarConsequences.lean) |
| 6. Single-use entropy | The adjoint norm certificate bounds centered output Hilbert–Schmidt length, hence purity and output entropy. The certificate is supplied by stage 5. | [`Nonadditivity.Channels.KrausChannel.output_purity_and_entropy_of_certificate`](Nonadditivity/QuantumHolevo.lean) |
| 7. Entangled two-use witness | The concrete Bell state and tensor regrouping yield a low-entropy complementary output. | [`Nonadditivity.BellOutput.complementary_bell_entropy_le`](Nonadditivity/BellOutput.lean); [`Nonadditivity.BlockBell.block_complementary_bell_entropy_le`](Nonadditivity/BlockBell.lean) |
| 8. Holevo conversion and assembly | The switch/Weyl construction gives the single-use equality and two-use lower bound for the same actual channel. Assembly supplies the exact dimensions and positivity. | [Conversion.lean](Nonadditivity/Conversion.lean); [`Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound`](Nonadditivity/HaarPrescribedBound.lean) |

Stage 5's assembly theorem has an explicit `ExplicitHaarExpectation` premise; `explicitHaarExpectation` proves that premise under the same `K,n` conditions. The completed endpoint therefore does not depend on an unproved Haar-convergence predicate.

The Haar model uses `Fin (N+1)` indices for a true matrix dimension `D=N+1`. The separate sharper theorem [`Nonadditivity.HaarSharpBound.onePairTraceBound`](Nonadditivity/HaarSharpBound.lean) proves the one-pair estimate at `D ≥ 2³²p⁸⁰`. The prescribed channel assembly already meets the stronger sufficient estimate in [HaarPrescribedBound.lean](Nonadditivity/HaarPrescribedBound.lean). Review the exact dimension variables rather than treating the two source indices as different claims.

## Alternative qualitative route

The qualitative theorem uses a different finite construction. It gives the same dimension *form* with some positive integer `N`, without the quantitative Haar route's prescribed value of `N`. It does not prove the manuscript's broader assertion of an undamped realization in every sufficiently large dimension.

| Stage | Mathematical role | Lean landmarks |
| --- | --- | --- |
| Finite free-group moments | Finite permutations detect words through a chosen radius. Their regular unitary matrices match the required moments of the free model exactly. | [FiniteFreeModel.lean](Nonadditivity/FiniteFreeModel.lean), [FiniteRegularMatrix.lean](Nonadditivity/FiniteRegularMatrix.lean); `Nonadditivity.FiniteBlockModel.block_adjoint_normalized_moment_le` in [FiniteBlockModel.lean](Nonadditivity/FiniteBlockModel.lean) |
| Spectral damping | An invertible Hermitian contraction suppresses the finite observable net while controlling trace loss. The resulting complete Kraus family implements damping and maximally mixed replacement. | [SpectralDamping.lean](Nonadditivity/SpectralDamping.lean), [DampedChannel.lean](Nonadditivity/DampedChannel.lean) |
| Branch-weight perturbation | A small nonuniform weight change supplies a strict Bell entropy margin. Norm continuity fits its single-use cost within the requested tolerance. | [WeightedBell.lean](Nonadditivity/WeightedBell.lean), [WeightedParameters.lean](Nonadditivity/WeightedParameters.lean), [WeightedCertificate.lean](Nonadditivity/WeightedCertificate.lean) |
| Entropy stability and exact endpoint | The margin absorbs damping's Bell entropy error; inverse damping preserves a nonuniform output and hence positive one-use Holevo information. | [`Nonadditivity.ExactQualitative.exists_actual_channel_bounds_with_dimensions`](Nonadditivity/ExactQualitative.lean) |

The result is `0 < χ(T) ≤ n log₂(1+9/K)+η` and the exact bound `χ(T ⊗ T) ≥ n log₂(K)/K`, for every `η > 0`. Selecting parameters gives vanishing single-use information with diverging two-use information in [`Nonadditivity.DeterministicConsequences.actual_vanishing_diverging`](Nonadditivity/DeterministicConsequences.lean).

## From information bounds to physical communication

Capacity is defined through actual density-matrix codewords, normalized POVM decoders, Born probabilities, and vanishing average error. The development then proves achievability, the converse, and physical blocking/padding, rather than defining capacity as regularized Holevo information.

| Step | Source and exact endpoint |
| --- | --- |
| Finite-channel HSW achievability | [QuantumCodingHSW.lean](Nonadditivity/QuantumCodingHSW.lean) |
| Converse for actual code sequences | [OperationalWeakConverse.lean](Nonadditivity/OperationalWeakConverse.lean) |
| Block regrouping and padding | [OperationalBlocking.lean](Nonadditivity/OperationalBlocking.lean) |
| Coding equality and tensor-power limit | [`Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum`](Nonadditivity/OperationalCodingTheorem.lean); `Nonadditivity.ActualConsequences.FiniteQuantumChannel.normalizedPowerHolevo_tendsto_classicalCapacity` in the same module |
| Prescribed-family capacity gain | [`Nonadditivity.OperationalConsequences.exists_prescribed_channel_with_capacity_gain`](Nonadditivity/OperationalConsequences.lean) |
| Vanishing one-use information, diverging capacity | [`Nonadditivity.OperationalConsequences.actual_vanishing_chi_diverging_capacity`](Nonadditivity/OperationalConsequences.lean) |

The conclusions describe the difference `C(T) − χ(T)` for one channel and its repeated uses. No theorem here states that `C(S ⊗ T) > C(S)+C(T)` for distinct channels, or establishes a strong converse at every rate above capacity.

## Scaling and additional endpoints

The prescribed family retains the dimensions of the channel just constructed, including the integer ceiling in `N`. For fixed `K` with `δ_K > 0`, [`Nonadditivity.HaarPrescribedDimension.prescribedFamily_gap_linear_bounds`](Nonadditivity/HaarPrescribedScaling.lean) and [`Nonadditivity.HaarPrescribedDimension.prescribed_gap_sqrt_input_bounds`](Nonadditivity/HaarInputScaling.lean) give two-sided linear-in-block-length and square-root-in-input-qubits gap bounds.

For the growing family with `n_K=⌈K/√ln K⌉`, [`Nonadditivity.PrescribedCost.growingFamily_input_qubits_div_sq_tendsto`](Nonadditivity/PrescribedCostDimensions.lean) proves `q_in/K² → 280/ln 2`. [`Nonadditivity.PrescribedCost.growingFamily_chi_input_cost_bounds`](Nonadditivity/PrescribedCostScaling.lean) bounds one-use information at order `1/√log₂ q_in`; [`Nonadditivity.PrescribedCost.growingFamily_two_use_input_cost_lower`](Nonadditivity/PrescribedCostCapacity.lean) supplies positive lower bounds at order `√log₂ q_in` for two-use information per use and capacity. These rounded parameters meet the construction threshold eventually.

Two further results have broader roles than the main channel assembly:

- [`Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits`](Nonadditivity/WeylPowersEntropy.lean) proves the Weyl-extension Holevo identity at every positive power, permitting entangled inputs. The Lean index `n` represents `n+1` uses. Entropy is expressed as an infimum; pure-input attainment is not assumed.
- [`Nonadditivity.UniversalFactorization.exists_universal_factorization`](Nonadditivity/UniversalFactorization.lean) chooses the scalar and finite-set coefficients before the representation, with the same choice working on every nonzero complete complex Hilbert space, including infinite dimension. The nonzero-space hypothesis is explicit and necessary for its additive scalar norm identity.

## Repairs, remaining scope, and verification

The manuscript's important-time bound `δ+1` is false; the formalized replacement is `δ+2`. The old middle-run count also fails; marked-position accounting repairs its coefficient estimate. The release contains formal counterexamples to both old claims and proves the corrected estimates. The final prescribed dimension formula remains the same. [CORRECTIONS.md](docs/CORRECTIONS.md) identifies the exact manuscript paragraphs to change; the included manuscript has not yet been edited.

Generic Haar strong-convergence interfaces remain unproved at their stated generality, and the one-pair Haar estimate is formalized for the matrix/free-factor coefficient representations needed here rather than every abstract traced C*-algebra. Other background generalizations remain outside the completed endpoints. [FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md) records them explicitly.

A successful Lean build and transitive audit establish the formal declarations under the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. They do not verify the intended meaning of every definition or the manuscript translation. [README.md](README.md#verify-with-lean) supplies the reproducer commands. Local challenge/type checks passed; end-to-end Comparator and independent-kernel checks remain pending. Challenge statements import selected lower-level project definitions and lemmas, so review their [trust assumptions](ComparatorChallenges/README.md) as part of checking the correspondence.
