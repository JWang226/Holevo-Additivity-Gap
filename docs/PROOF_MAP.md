# Manuscript-to-Lean map

The source is identified by LaTeX labels, which stay useful when theorem
numbers change. The finite-dimensional quantum steps below use actual complex
positive semidefinite trace-one matrices and actual finite Kraus channels.
They no longer assume entropy concavity, pure-mixture bounds, Schmidt entropy
equality, or Weyl conversion. The general Collins--Youn bound and the
manuscript's structured coefficient/error budgets are proved. A deterministic
finite-group moment construction with small branch-weight perturbations and
invertible damping now proves the exact Section 2 qualitative existence
bounds, including the two-use lower bound without an error term. Unbounded
additive gaps, vanishing positive single-use information with diverging
two-use information, and unbounded ratios are also unconditional. The
prescribed-dimension theorem is now also unconditional:
`HaarPrescribedDimension.exists_prescribed_channel` proves the exact
dimensions and information bounds through actual Haar integration, path
classes, coefficient estimates, and tensor replacement. The separate
Gaussian multiplicative construction remains available. The older general
Haar convergence predicates are not proved or used by the new theorem.
The full arbitrary-use Weyl-extension equality is now proved as well. The
operational classical coding theorem starts from actual codewords and POVMs
and identifies independently defined capacity with the regularized Holevo
supremum. These additions do not constitute a claim that every assertion in
the manuscript or every generic analytic interface has been formalized.

Quantum entropy and the basic Holevo quantity use natural logarithms.
`HolevoBits.lean` supplies the qualitative construction in the manuscript's
base-two convention; `Scalar.lean`, `Dimensions.lean`, and the original
numerical `Main.lean` also use `Scalar.log2`.

| Manuscript label or claim | Representative Lean theorem | Status |
|---|---|---|
| Concrete CPTP channels | `Nonadditivity.Channels.KrausChannel.map_posSemidef`, `trace_map`, `amplify_posSemidef` | Checked from rectangular Kraus matrices and their completeness equation, including all finite ancillas |
| `eq:gram`, `eq:gamma-free`: finite block polynomial | `Nonadditivity.Channels.KrausChannel.uniform_complementary_output_entry`, `blockChannel_adjoint_eq_tensor_polynomial` | Actual complementary Gram channel and its block adjoint equal the stated normalized tensor-word polynomial, with the output-coordinate pullback proved |
| `lem:cy`: finite tests to uniform norm | `Nonadditivity.opNorm_le_of_unitSphereNet`, `FiniteRealization.eventually_exists_kraus_certificate` | Checked on the actual real subspace of traceless Hermitian HS observables and actual adjoints; canonical Haar convergence remains an input to the original sampled realization, while the damped route uses proved finite moments |
| `lem:cy`: free-group comparison model | `Nonadditivity.FreeModel.leftRegular`, `gamma`, `freeNorm`, `CollinsYounBound` | Actual bounded left-regular representation and comparison polynomial; the displayed predicate is proved for every `K >= 2`, `n >= 1` by `CollinsYounProduct.collinsYounBound` |
| One-block Collins–Youn inequality | `Nonadditivity.CollinsYoun.local_polynomial_norm_le_three_hs`, `Nonadditivity.CollinsYounOne.collinsYounBound_one` | Unconditional actual free operator estimate: three creation/annihilation components each bounded by HS, diagonal trace cancellation, and exact normalization `c(K,1)=3/K` |
| General Collins--Youn inequality | `Nonadditivity.CollinsYounTensor.local_polynomial_norm_le_three_coeff`, `Nonadditivity.CollinsYounProduct.traceless_polynomial_norm_sq_le`, `collinsYounBound` | Actual Hilbert-valued creation operators, exact product Fubini identification, and diagonal/off-diagonal induction prove the unnormalized squared constant `(K+9)^n-K^n`, then the exact normalized bound; no analytic hypothesis |
| Free model to actual block output coordinates | `Nonadditivity.FreeBridge.outputFreeNorm_unit_bound`, `outputObservable_hsLength`, `outputObservable_trace` | Actual ordered branch tuples and block basis are related by a proved equivalence; trace, Hermitian symmetry, and HS length are preserved |
| `lem:cy`: normalized Collins--Youn constant | `Nonadditivity.CollinsYounProduct.constant_normalization`, `collinsYounBound` | Exact identity `c(K,n)^2*K^(2*n)=(K+9)^n-K^n` and the full normalized inequality are proved |
| Finite free-group model | `Nonadditivity.FiniteFreeModel.model_eq_one_iff`, `productModel_eq_one_iff` | Actual finite permutations extend translations on word balls and detect nonidentity words through any fixed radius; no residual-finiteness premise |
| Finite regular unitaries and exact moments | `Nonadditivity.FiniteRegularMatrix.regularUnitaryHom`, `regularHom_trace`; `Nonadditivity.FiniteMomentMatching.trace_pow_eq_regular_vacuum`, `gamma_trace_pow_re_le` | Genuine finite unitaries and their exact characters match finite trace moments to free vacuum moments, bounded by the proved free norm |
| Actual block moment adapter | `Nonadditivity.FiniteBlockModel.finiteEval_eq_block_adjoint`, `block_adjoint_normalized_moment_le` | The finite polynomial is the concrete block adjoint; a word radius `4*p` supplies the normalized `2*p` moment bound `c(K,n)^(2*p)` |
| Simultaneous spectral damping | `Nonadditivity.SpectralDamping.exists_damping`; `Nonadditivity.DampedRealization.exists_moment_order` | Constructs a Hermitian invertible contraction, suppresses every finite-net observable, and controls normalized trace loss using a fixed finite moment order |
| Actual damped channel | `Nonadditivity.DampedChannel.damped`, `damped_map`, `damped_adjointMap_traceless` | A complete finite Kraus family implements input damping and maximally mixed replacement; its traceless adjoint is exactly `F*T.adjointMap(A)*F` |
| Bell entropy survives damping | `Nonadditivity.CanonicalBlockBell.block_channel_canonical_entropy_le`; `Nonadditivity.DampedBellStability.damped_pair_entry_sub_norm_le`; `Nonadditivity.EntropyStability.exists_damped_bell_entropy_modulus` | Canonical Bell identification, matrix-entry stability, and proved entropy continuity control the actual paired output uniformly in the input dimension |
| Strict positivity after damping | `Nonadditivity.Entropy.DensityMatrix.vonNeumann_lt_log_card_of_ne_maximallyMixed`; `Nonadditivity.DampedPositivity.converted_damped_block_holevoBits_pos` | Strict entropy maximality and an inverse-filter pullback preserve a nonuniform output, giving a positive Holevo denominator despite the additional Kraus branches |
| Strict weighted Bell margin | `Nonadditivity.WeightedBellScalar.perturbedWeights_sum_sq`; `Nonadditivity.WeightedBell.complementary_bell_entropy_le_with_margin`; `Nonadditivity.WeightedBlock.weightedBlock_canonical_entropy_le_with_margin` | Positive branch probabilities differing from uniform by `+s,-s` give squared mass `1/K+2*s^2` and a strict block Bell entropy margin `2*n*s^2*ln(K)` |
| Weighted norm certificate and parameter selection | `Nonadditivity.WeightedBlock.weightedBlock_eq_weighted`; `Nonadditivity.WeightedCertificate.damped_weighted_certificate`; `Nonadditivity.WeightedParameters.exists_small_perturbation` | Exact output scaling, norm continuity, and error `delta*(2+delta)` per unit HS test allow a nonzero perturbation inside the single-use tolerance; subsequent damping fits entirely within the Bell margin |
| Positive weighted and damped channel | `Nonadditivity.WeightedPositivity.weightedBlock_product_output_diagonal`, `converted_damped_weightedBlock_holevoBits_pos` | The actual product-input diagonal `p_i^n` differs from uniform; inverse damping preserves a nonuniform output and strictly positive converted Holevo information |
| `lem:purity`: state expectation and centered witness | `Nonadditivity.AdjointPurity.norm_state_expectation_le_opNorm`, `centered_hsLength_le_of_adjoint_certificate` | Checked for actual density matrices and the Euclidean operator norm, with Hilbert--Schmidt length defined independently by matrix trace |
| `lem:purity`: complete channel statement | `Nonadditivity.Channels.KrausChannel.output_purity_and_entropy_of_certificate` | Checked for actual Kraus channels; trace duality and Hermitian preservation are derived from their Kraus operators, leaving only the displayed adjoint norm certificate |
| `lem:purity`: trace and spectral entropy | `Nonadditivity.Entropy.DensityMatrix.trace_square_eq_purity`, `vonNeumann_ge_neg_log_purity`, `centered_trace_square` | Checked for actual finite density matrices, including zero eigenvalues |
| `eq:single-entropy` | `Nonadditivity.Main.block_entropy_of_purity`, `minimum_block_entropy_of_purity` | Checked from a concrete uniform purity certificate; the completed Haar and alternative weighted/damped constructions each supply that certificate |
| `lem:bell`: Bell invariance | `Nonadditivity.Entropy.unitary_kronecker_conjugate_fixes_bell` | Checked for actual complex unitary matrices |
| Quantum entropy concavity and mixture upper bound | `Nonadditivity.EntropyMixtures.densityMatrix_mixture_entropy_concave`, `densityMatrix_mixture_entropy_upper` | Checked on actual density matrices; the upper bound is derived from an explicit rectangular ensemble amplitude, Gram entropy equality, and pinching |
| Pure inputs and complementary outputs | `Nonadditivity.Entropy.bipartite_entropy_eq`, `Nonadditivity.Channels.KrausChannel.pure_output_complementary_entropy_eq` | Checked for arbitrary rectangular coefficient matrices and actual Kraus channels, including unequal dimensions and zero Schmidt coefficients |
| Entropy tensor additivity | `Nonadditivity.Entropy.DensityMatrix.tensor_entropy`, `tensorChain_entropy`, `Nonadditivity.Channels.KrausChannel.tensorChain_output_entropy` | Actual tensor states and channels are constructed; binary and finite-family entropy identities are proved |
| `lem:bell`: local quantum entropy estimate | `Nonadditivity.BellOutput.pairedChannel_bell_entropy_le`, `complementary_bell_entropy_le` | Checked for arbitrary nonempty finite unitary families and the normalized Bell input; diagonal branches are merged into the actual weight list |
| `lem:bell`: block estimate | `Nonadditivity.BlockBell.pairedTensorChain_output_entropy`, `block_complementary_bell_entropy_le` | Checked for actual tensor-channel blocks and an explicitly constructed entangled Bell tensor witness; all input/output/Kraus regrouping identities are proved |
| Conjugate-channel entropy invariance | `Nonadditivity.Channels.KrausChannel.conjugate_output_entropy_all`, `minimumEntropy_conjugate` | Checked for actual conjugate Kraus channels and all input states |
| Weyl twirling | `Nonadditivity.Weyl.uniform_average_eq`, `Nonadditivity.WeylTensor.uniform_average_eq` | Actual shift/phase unitaries and their single-output and independent two-output twirls are checked |
| `eq:chi-extension`, single use | `Nonadditivity.Channels.KrausChannel.weylExtension_holevo` | Complete equality for an actual measured-register Weyl extension; no assumed concavity, twirling law, or minimizing input |
| `eq:chi-extension`, every positive use count | `Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevo`, `positiveTensorPower_weylExtension_holevoBits` | Exact equality on the actual tensor powers; explicit control-register regrouping and the full local Weyl orbit work for entangled inputs |
| Regularized Weyl identity | `Nonadditivity.WeylPowers.regularized_weylExtension_holevo` | The all-use normalized Holevo supremum equals `log2(d)` minus the all-use minimum-output-entropy infimum in bits |
| Switch minimum output entropy | `Nonadditivity.Channels.KrausChannel.switch_minimumEntropy` | Checked for the actual original/conjugate switch with its input flag discarded |
| Entropy-gap to Holevo-gap conversion | `Nonadditivity.Conversion.converted_holevo`, `converted_tensor_holevo_lower`, `converted_gap_lower` | Complete concrete single-use equality and two-use lower bound, including arbitrary entangled joint inputs |
| `eq:certificate-holevo`, `eq:certificate-gap` | `Nonadditivity.Conversion.converted_bounds_of_certificate`, `Nonadditivity.BlockConstruction.block_converted_bounds_of_certificate`, `Nonadditivity.BlockScalars.gap_of_converted_bounds` | Concrete channel conversion and the actual block Bell witness are checked; the block theorem needs only the base adjoint norm certificate |
| `lem:linear`: positive block and norms | `Nonadditivity.Linearization.modulus_block_posSemidef`, `constant_correction_posSemidef`, `shifted_dilation_norm`, `factor_norm_sq_of_shifted_gram` | Actual moduli, unconditional positive polar block and correction, dilation spectrum/norm, and finite-matrix Gram norm identities are proved; the full finite coefficient assembly is supplied by FiniteSetFactorization |
| `eq:linear-id`, finite representations | `Nonadditivity.FiniteSetFactorization.exists_finite_factorization`, `paddedPolynomial_dilation_norm_identity` | Actual representation-independent square coefficients of the exact dimension `2*m*B` give `norm(P_pi)=norm(Q_pi)^2-theta` for every nonempty finite unitary representation; positivity, Gram construction, dilation and padding are conclusions, not premises |
| `eq:linear-id`, actual infinite regular representation | `Nonadditivity.RegularFactorization.padded_dilation_norm_identity`, `exists_factorization` | The same explicit square coefficients and correction work on the actual infinite regular Hilbert space and every finite unitary representation; the extension to arbitrary nonzero complete Hilbert-space representations is proved in `UniversalFactorization.lean` |
| `eq:theta` | `Nonadditivity.RegularCoefficientEnergy.coefficient_gram_le`, `Nonadditivity.FiniteSetFactorization.theta_dilation_le_card_mul_regularNorm` | Identity-vector energy plus actual infinite regular-dilation norm equality prove the exact correction bound for the original polynomial; no coefficient-energy or dilation-norm premise remains |
| Backward relative error | `Nonadditivity.RegularFactorization.finite_regular_error_transfer`, `relative_error_transfer`; `Nonadditivity.Linearization.backward_error_chain` | Actual finite-versus-regular factor comparison implies the exact `6B` error bound; the constructed repeated reduction composes these identities with exact recursive error costs |
| Constructed free-group repeated shortening | `Nonadditivity.PolynomialReduction.Polynomial.constructed_linear_reduction` | Actual square coefficient polynomials reduce support degree `2^k` to degree one, with exact coefficient-dimension multiplier and backward norm transfer; no intermediate-polynomial existence premise |
| Constructed product-group repeated shortening | `Nonadditivity.ProductPolynomialReduction.constructed_linear_reduction`, `dimensionCost_le`, `errorCost_le` | Actual coordinate words and total degree are used; safe costs are `(2*3^k*max 1 support.card)^k` and `(6*3^k*max 1 support.card)^k`. The manuscript-specific exact budgets are supplied separately by `StructuredLinearization.exists_net_linearization` |
| Short-generator free embedding | `Nonadditivity.FreeEmbedding.exists_short_embedding`, `logarithmicEmbedding_injective`, `norm_logarithmicEmbedding_of_le` | Actual injective homomorphism into the two-generator free group with exact length bound `2*Nat.log 2(K-1)+1`, built from a completed binary covering graph |
| Amplified short substitution | `Nonadditivity.MatrixShortEmbedding.product_matrix_logarithmic_substitution`, `product_matrix_total_degree_substitution` | Exact norm preservation for the actual matrix-coefficient vector-valued regular polynomial and logarithmic support-degree control, at every finite coefficient size |
| Regular norm under subgroup inclusion | `Nonadditivity.RegularRestriction.regularPolynomial_injective_norm_eq`, `gammaInfinite_norm_eq` | Actual coset decomposition and zero extension prove equality of operator norms, including the finite-generator Collins–Youn specialization |
| `eq:word-counts` | `Nonadditivity.WordBallReduction.mem_wordBall_of_bound`, `bound_of_mem_wordBall`, `card_wordBall_le` | Actual finite single-factor word balls contain exactly the required bounded words and have card at most `2*n*3^r`; the reduced-word enumeration is connected to the free group |
| Symmetric net cardinality bound | `Nonadditivity.QuantitativeNet.card_le_of_separated`, `exists_symmetric_inverse_nat_net` | Volume packing proves `(1+2*n)^D` points at radius `1/n`, with a prescribed unit test and its negative included without extra cardinality |
| Exact observable-space dimension | `Nonadditivity.ObservableDimension.observableSpace_finrank`, `exists_symmetric_observable_net_for_matrix` | The actual real traceless Hermitian HS space has dimension `d^2-1`; the net bound is `(1+2*n)^(d^2-1)` |
| Prescribed quantitative witness | `Nonadditivity.ShiftNorm.norm_shift_add_inverse`, `Nonadditivity.PrescribedTest.exists_prescribed_test` | Actual orbit-vector proof of shift norm two, then a traceless Hermitian unit-HS test with exact free norm `sqrt(2)*K^(-(n+1)/2)`; no analytic premise |
| Literal combined observable-net polynomial | `Nonadditivity.NetPolynomial.exists_net_polynomial`, `finitePolynomial_norm`, `netRegularPolynomial_shifted_norm` | Actual diagonal matrix coefficients combine the symmetric net; exact block norms, prescribed lower norm, CY upper norm, self-adjointness, spectral symmetry, and positive shift identity are proved |
| Collected-word support bridge | `Nonadditivity.NetPolynomialSupport.polynomial`, `polynomial_regularEval`, `polynomial_finiteEval_norm` | Collects duplicate words into the actual support-reduction polynomial record, with exact regular evaluation and finite evaluation norm; no analytic premise |
| Initial undoubled Gram reduction | `Nonadditivity.InitialNetReduction.exists_initial_net_polynomial`, `initial_relative_transfer` | Actual `J*K^n` coefficient space, shifted norm identity, and factor `3*(1+rho^-1)` for the symmetric net polynomial |
| Balanced tensor-factor shortening | `Nonadditivity.TensorPartitionReduction.stageSupport_card`, `constructed_tensor_reduction` | Actual residue-class partitions and signed supports meet `1+2^(j+1)*K^ceil(n/2^j)`; exactly `Nat.clog 2 n` stages leave one active factor |
| Single-factor word shortening | `Nonadditivity.WordBallReduction.stage_error_transfer`, `stage_clog_linear` | Actual counted word balls shorten each factor to individual letters, with literal coefficient and error products |
| Complete deterministic Steps 1--3 | `Nonadditivity.StructuredLinearization.exists_net_linearization` | Only numeric hypotheses; supplies the actual prescribed net, short substitution and Hermitian linear `H`, the exact logarithmic coefficient budget, and transfer from relative error `exp(-gamma_K*n)/n` |
| `eq:threshold-absorption` | `Nonadditivity.Quantitative.threshold_absorption`, `threshold_consequences` | Checked with the exact ceiling threshold and constants |
| `eq:error-size` | `Nonadditivity.StructuredCostBounds.errorProduct_bound`, `coefficientBound_log_bound`; `Nonadditivity.StructuredReductionCosts.actual_error_bound`, `actual_coefficient_bound` | Literal products and actual structured stages satisfy the manuscript's exact budgets at `n >= n₀(K)`; no separate support-count or summed-log premise remains |
| `prop:finite`, actual prescribed-dimension realization | `Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation`, `exists_prescribed_channel` in `HaarPrescribedBound.lean` | Unconditional actual finite channel at `N=ceil(exp(b_K*n))`, exact input/output dimensions, positive single-use information, and all three channel bounds in bits; only numerical `K,n` hypotheses |
| `eq:En-bound` | `Nonadditivity.Quantitative.final_three_tails_lt`, `explicit_haar_error_bound`, `explicit_haar_log_comparison` | Checked scalar estimates including exact dimension/moment rounding; connected to the proved Haar expectation theorem |
| `eq:positive-probability` existence part | `Nonadditivity.Probability.positive_measure_sublevel`, `favorable_realization` | Checked from an actual integrable expectation estimate; the paper's exact probability fraction is not proved here |
| Canonical Haar model | `Nonadditivity.HaarModel.independent_coordinates`, `coordinate_law`; `Nonadditivity.HaarConsequences.exists_block_channel` | Actual normalized Haar probability, independent samples, polynomial continuity, and measurable failure events; the final block theorem assumes only the specified canonical Haar convergence |
| Actual Haar first/second moments and twirl | `Nonadditivity.HaarMoments.integral_entry`, `integral_entry_product`, `integral_twirl_entry`, `integral_sample_entry_product_ne` | Exact canonical integrals are derived from Haar invariance and unitary orthogonality, including independent-coordinate covariance |
| Actual Haar fourth entry moments | `Nonadditivity.HaarFourthMoments.integral_entry_norm_four`, `integral_entry_norm_sq_mul_norm_sq` | Proved `E norm(U_ij)^4=2/(d*(d+1))` and distinct-row same-column mixed square moment `1/(d*(d+1))`, with `d=N+1`; no higher-moment hypothesis |
| High trace moments imply norm upper tails | `Nonadditivity.HaarMomentTail.measure_norm_ge_le_trace_moment`, `measure_norm_ge_le_normalized_trace_moment`, `canonical_upper_tail_of_trace_moments` | Actual spectral trace/norm inequality and Markov bound; normalized trace exposes the exact dimension cost. The required vanishing moment ratio is still a premise |
| Weaker analytic boundary | `Nonadditivity.UpperHaarRealization.upper_of_strong`, `upper_of_trace_moments`, `exists_block_channel_of_trace_moments` | Full convergence or explicit `HaarTraceMomentControl` implies the one-sided `HaarUpperConvergence` consumed by realization; neither random-matrix input is proved |
| Upper-tail-only channel separation | `Nonadditivity.UpperHaarRealization.exists_block_channel`, `exists_arbitrarily_large_gap_of_all_upper`, `exists_arbitrarily_large_ratio` | Actual channels and arbitrary gaps/ratios follow from the specified upper tails, with only `n=1` tails needed for the ratio theorem |
| Universal positive Holevo bound for undamped blocks | `Nonadditivity.PositiveHolevo.block_converted_holevoBits_lower`, `block_converted_holevoBits_pos` | Checked `chi_bits >= 2n/K` for the original converted block channels, through actual normalized eigenvectors and merged equal pure outputs; damping retains strict positivity without this numerical claim |
| Unconditional fixed-block approximation | `Nonadditivity.DeterministicQualitative.exists_actual_channel_bounds_with_dimensions`, `exists_actual_channel_bounds_positive` | For every `K >= 2`, `n >= 1`, `eta > 0`: actual channel with `0 < chi(T) <= n*aK + eta` and `chi(T tensor T) >= n*log2(K)/K - eta`; exact dimensions `2*N^n*K^(2*n)` and `K^n` for some finite `N > 0`, without the prescribed upper bound on `N` |
| `prop:qualitative`, `eq:qualitative-bounds` | `Nonadditivity.ExactQualitative.exists_actual_channel_bounds_with_dimensions`, `exists_actual_channel_bounds_positive` | Unconditional exact Section 2 existence bounds: `0 < chi(T) <= n*aK + eta` and `chi(T tensor T) >= n*log2(K)/K`; exact dimensions `2*N^n*K^(2*n)` and `K^n` for some finite `N > 0`, without the prescribed upper bound on `N` |
| Exact qualitative additive bound in manuscript units | `Nonadditivity.ExactQualitative.exists_actual_channel_gap` | Unconditional `gap(T) >= n*deltaK - 2*eta`, with positive single-use information; the alternative proof changes the base channel by weighting and damping |
| Qualitative finite-net realization | `Nonadditivity.FiniteRealization.eventually_exists_kraus_entropy_and_holevo`, `Nonadditivity.Qualitative.eventually_exists_block_channels`, `exists_block_channels` | Checked for arbitrary sampled finite unitary families and a pointwise limiting-norm bound; the explicit free model is instantiated in the preceding theorem |
| `thm:main`, `cor:capacity` numeric subtraction | `Nonadditivity.Main.quantitative_gap_of_bounds`, `Nonadditivity.Scalar.capacity_gap` | Numerical consequences and the prescribed-dimension channel theorem are unconditional; `OperationalCodingTheorem` now supplies the independent operational capacity identification |
| `eq:input-size` | `Nonadditivity.Dimensions.input_qubits_formula`, `input_size_remainder_tendsto` | Checked exact integer dimension and vanishing ceiling remainder |
| Fixed-K extensive gaps/ratios | `Nonadditivity.Asymptotics.gap_tendsto_atTop`, `eventually_ratio_of_holevo_bounds`, `output_normalized_gap_liminf` | Checked consequences of explicit numerical bounds, with required boundedness for real liminf |
| `cor:separation`, unbounded additive and two-use ratios | `Nonadditivity.DeterministicConsequences.actual_vanishing_diverging`, `actual_gap_tendsto_atTop`, `actual_ratio_tendsto_atTop`, `exists_small_chi_large_gap_and_ratio` | Unconditional actual finite CPTP channels, positive denominator, vanishing single-use information, diverging two-use information, and unbounded additive gap and ratio; finite-block errors vanish in the chosen family |
| Regularized Holevo limit and supremum | `Nonadditivity.ActualConsequences.FiniteQuantumChannel.normalizedPowerHolevo_tendsto`; `Nonadditivity.DeterministicConsequences.exists_small_chi_large_regularized_gain_and_ratio` | Actual tensor-power rates converge to their bounded supremum; small positive single-use information and unbounded regularized gain/ratio are unconditional; the coding theorem identifies these with operational quantities |
| One-block nonadditive channel | `Nonadditivity.OneBlockRealization.exists_nonadditive_channel` | Actual finite CPTP channel with positive additive gap, from only the canonical one-block Haar strong-convergence input; no free-operator hypothesis remains |
| Gaussian quadratic concentration | `Nonadditivity.GaussianQuadratic.integral_exp_trace_centered_le`, `measure_abs_quadratic_ge_le`; `Nonadditivity.GaussianCertificates.exists_isometry_and_observable_tests` | Exact Gaussian integration, spectral diagonalization, two-sided concentration, and the explicit simultaneous-net budget are proved internally |
| Actual Gaussian matrix algebra | `Nonadditivity.GaussianRectangular.quadraticOperator_norm_le`, `quadraticOperator_trace`, `quadraticOperator_trace_square`, `quadraticOperator_quadratic` | Exact pullback, real trace/variance and sampled matrix evaluation; the measure and all normalization factors are concrete |
| Gaussian finite channel realization | `Nonadditivity.GaussianConstruction.exists_channel` | Unconditional actual channel with traceless HS-to-operator adjoint certificate `512/K`, for `K >= 4096`, `N >= K^2` |
| General-channel Bell estimate | `Nonadditivity.GeneralBell.paired_bell_overlap_lower`, `paired_bell_entropy_le` | Proved overlap and entropy inequalities for actual Kraus channels, used by the Gaussian construction |
| Unconditional multiplicative separation | `Nonadditivity.GaussianConsequences.exists_small_chi_large_ratio`, `exists_arbitrarily_large_ratio`, `exists_nonadditive_channel` | Actual channels with arbitrarily small positive single-use information and arbitrarily large two-use ratio; also strict nonadditivity. No unbounded-additive-gap claim |
| Unconditional regularized ratio | `Nonadditivity.GaussianConsequences.exists_small_chi_large_regularized_ratio` | Arbitrarily large ratio of the genuine regularized Holevo limit to positive single-use Holevo information; the independently proved coding theorem gives the operational interpretation |
| Fixed-channel regrouping is sublinear | `Nonadditivity.Asymptotics.regrouping_gap_div_tendsto_zero`; `Nonadditivity.ActualConsequences.FiniteQuantumChannel.normalizedPowerHolevo_tendsto` | Scalar regrouping and actual normalized Holevo convergence are proved; `normalizedPowerHolevo_tendsto_classicalCapacity` identifies the limit operationally |

No unproved mathematical input is installed as a global axiom. Check theorem
statements to distinguish numerical parameter restrictions from additional
analytic premises.

## New concrete quantum modules

- `Channels.lean`: finite rectangular Kraus channels, completeness, positivity,
  trace preservation, complete positivity through arbitrary finite ancillas,
  adjoints, tensor products, conjugation, complements, and Stinespring matrices.
- `ComplementaryAdjoint.lean`: exact complementary Gram entries and adjoint
  polynomials, actual normalized tensor words, and the precise finite block
  polynomial in the manuscript's output coordinates.
- `AdjointPurity.lean`, `QuantumHolevo.lean`, `FiniteRealization.lean`: the actual
  state expectation estimate, operator/HS certificate, output entropy, finite
  output ensembles, and the finite-net theorem on concrete HS observables.
- `EntropyProducts.lean`, `PureChannelEntropy.lean`, `TensorPowers.lean`: actual
  tensor states, Schmidt/Gram entropy equality, rank-one entropy zero, pure-input
  channel/complement equality, and finite tensor-block state/channel laws.
- `EntropyMixtures.lean`: entropy pinching, quantum entropy concavity, and the
  complete finite mixed-state ensemble entropy upper bound.
- `BellOutput.lean`: normalized Bell states, exact merged diagonal/off-diagonal
  ensemble, and the complete local complementary-channel Bell entropy bound.
- `BlockBell.lean`: actual finite complementary-channel blocks, explicit paired
  Bell tensor witnesses, and proved input/output/Kraus coordinate regrouping.
- `BlockConstruction.lean`, `Qualitative.lean`: the actual block output is
  relabeled to `ZMod (K^n)`, the input dimension is proved, and the complete
  qualitative Holevo-gap construction is derived from analytic norm inputs.
- `FreeModel.lean`, `FreeBridge.lean`: the actual left-regular comparison
  operator is constructed, its branch labels are transported to the concrete
  block output, and `CollinsYounProduct.collinsYounBound` supplies the exact
  comparison bound for qualitative realization.
- `HolevoBits.lean`: the actual output-ensemble Holevo quantity is converted to
  bits, yielding all three qualitative bounds in the manuscript's convention.
- `ChannelExtensions.lean`, `ChannelEntropy.lean`, `SwitchChannel.lean`,
  `Weyl.lean`, `WeylTensor.lean`, `Conversion.lean`: actual measured-register,
  switch, and Weyl channels and the concrete entropy-gap/Holevo-gap conversion.
- `ChannelReindex.lean`, `ConjugateChannel.lean`: basis and environment
  relabeling, tensor/complement identities, and conjugate-channel entropy laws.
- `WeylPowersIndex.lean`, `WeylPowersControl.lean`, `WeylPowersChannels.lean`,
  `WeylPowersTwirl.lean`, `WeylPowersEntropy.lean`, `WeylPowersRegularized.lean`:
  arbitrary positive tensor powers of the actual Weyl extension, exact local
  twirling on joint matrices, normalized finite orbit ensembles, and both
  the all-use and regularized Holevo/minimum-output-entropy equalities.
- `FiniteFreeModel.lean`, `FiniteRegularMatrix.lean`, `FiniteMomentMatching.lean`,
  `FiniteBlockModel.lean`: finite word-ball permutations, actual finite regular
  unitaries, exact free-to-finite trace moments, and their identification with
  the existing block-channel adjoint.
- `SpectralDamping.lean`, `DampedRealization.lean`, `DampedChannel.lean`: fixed
  moment selection, a common invertible filter for all net tests, its trace
  loss, and a genuine trace-preserving channel including replacement branches.
- `CanonicalBlockBell.lean`, `DampedBellStability.lean`,
  `EntropyContinuity.lean`, `EntropyStability.lean`: the original Bell witness
  at canonical coordinates and stability of its actual output entropy under
  damping, with no dependence on input dimension in the continuity step.
- `StrictEntropy.lean`, `DampedPositivity.lean`: strict entropy maximality at
  the uniform state and strictly positive converted Holevo information after
  invertible damping.
- `WeightedBellScalar.lean`, `WeightedBell.lean`, `WeightedBlockBell.lean`:
  actual nonuniform branch probabilities and a strict Bell entropy margin
  for their genuine complementary block channels.
- `WeightedBlock.lean`, `WeightedCertificate.lean`, `WeightedParameters.lean`,
  `WeightedPositivity.lean`: exact output scaling, a uniform bound on the
  resulting adjoint error, admissible small perturbations, and positive
  converted Holevo information after damping the weighted channel.
- `DeterministicQualitative.lean`, `DeterministicConsequences.lean`: the
  earlier unconditional finite-block theorem with arbitrarily small
  two-use error, and the vanishing/diverging, additive, ratio, and regularized
  conclusions for actual channels. These theorems remain valid.
- `ExactQualitative.lean`: the exact Section 2 existence bounds and additive
  lower bound with no two-use error, including exact input/output dimensions
  for some finite local input dimension.

For every fixed `K >= 2`, `n >= 1`, and `eta > 0`,
`ExactQualitative.exists_actual_channel_bounds_with_dimensions`
constructs an actual finite channel `T` and `N > 0` with, in bits,

```text
input dimension  = 2*N^n*K^(2*n)
output dimension = K^n
0 < chi(T) <= n*log2(1 + 9/K) + eta
n*log2(K)/K <= chi(T tensor T).
```

`ExactQualitative.exists_actual_channel_gap` gives the corresponding exact
gap `chi(T tensor T) - 2*chi(T) >= n*deltaK - 2*eta`. These theorems have only
the displayed numerical hypotheses. The channel is built from finite group
representations, slightly nonuniform branch probabilities, invertible input
damping, and the switch/Weyl conversion. The strict weighted Bell entropy
margin absorbs the entire damping error, so the Section 2 existence result
has no remaining qualitative gap. This separate construction does not
control `N` by the prescribed formula; the Haar theorem below does.

This alternate construction does not prove norm convergence for the original
unitary family or a Haar convergence predicate. It proves strict positivity;
the supplementary bound `chi_bits >= 2*n/K` still pertains only to the
original undamped block construction. The earlier `DeterministicQualitative`
statement with arbitrarily small two-use error remains available and supplies
the family used by `DeterministicConsequences`.

## The original Haar route and prescribed dimension

For every fixed `K >= 2`, `n >= 1`, and `epsilon > 0`,
`Qualitative.qualitative_realization_of_CY_and_strong_convergence` constructs
a channel `T` with output dimension `K^n` such that, in natural-log units,

```text
chi(T) <= n * log(1 + 9/K) + epsilon
chi(T tensor T) >= n * log(K)/K
chi(T tensor T) - 2 * chi(T) >= n * gapCoefficient(K) - 2 * epsilon.
```

The generic theorem retains its explicit norm hypotheses for reuse.
`HaarConsequences.exists_block_channel` specializes it to the fixed normalized
Haar spaces and supplies the full free-group bound internally. Its only
analytic premise is `HaarModel.HaarStrongConvergence K n`. The sampling index
`N` gives local dimension `N+1`, and the selected input dimension is exactly
`2*(N+1)^n*K^(2*n)`. No numerical upper bound on this selected dimension is
claimed. The generic interface uses the actual local dimension directly and
requires a nontrivial filter. The newer
`UpperHaarRealization.exists_block_channel` has the weaker one-sided premise,
and `exists_block_channel_of_trace_moments` takes the explicit sufficient
high-trace-moment criterion.

These original Haar interfaces remain conditional. Their hypotheses are no
longer needed for the same exact qualitative existence bounds, now supplied
by `ExactQualitative` through a different base channel.

The quantitative chain is closed by
`HaarPrescribedDimension.exists_prescribed_channel` in `HaarPrescribedBound.lean`.
It assumes only `K >= 2` and `n >= Quantitative.n₀ K`. The local dimension
is exactly `N=ceil(exp(40*(7*ln(K)+2)*n))`, the input dimension is
`2*N^n*K^(2*n)`, and the output dimension is `K^n`. With
`kappa=(n+1)/(n-1)`, the single-use correction is `2*log2(kappa)` and the
gap correction is `4*log2(kappa)`. The actual finite channel has positive
single-use information and the manuscript's one-use, two-use, and gap bounds.

`HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound` also
includes the supplementary bound `2*n/K <= chi(T)` for this same witness.

| Prescribed-family consequence | Checked theorem in `HaarPrescribedDimension` |
|---|---|
| Same-witness supplementary lower bound | `prescribedFamily_chi_lower` |
| Finite regularized-Holevo gain | `prescribedFamily_regularizedGain_lower` |
| Divergence for positive gap coefficient | `prescribedFamily_gap_tendsto_atTop_of_delta_pos`, `prescribedFamily_regularizedGain_tendsto_atTop_of_delta_pos` |
| Asymptotic ratio thresholds | `prescribedFamily_ratio_eventually`, `prescribedFamily_regularizedRatio_eventually` |
| Exact output-qubit count | `prescribedFamily_output_qubits` |
| Matching linear gap bounds | `prescribedFamily_gap_linear_bounds` |
| Output-normalized gap liminf | `prescribedFamily_output_normalized_gap_liminf` |
| Quadratic input-qubit expansion, vanishing remainder | `prescribedFamily_input_size_remainder_tendsto` |

These theorems are in `HaarPrescribedConsequences.lean` and
`HaarPrescribedScaling.lean`, on actual finite channels rather than abstract
real sequences supplied with channel bounds.

## Complete Haar dependency chain

| Stage | Checked modules or theorem | Content |
| --- | --- | --- |
| Haar integration | `HaarAveraging`, `HaarInvariantCommutant`, `HaarInvariantSpanning` | The actual Haar average is the invariant-tensor projection, with a proved spanning family. |
| Weingarten estimates | `HaarWeingartenGram`, `HaarWeingartenInverse`, `HaarEntryBound`, `HaarPairEntryBound` | The Gram inverse and matching counts give singleton-sensitive entry-integral estimates for actual independent Haar pairs. |
| Literal paths | `HaarPathExpansion`, `HaarOperatorPathBridge`, `HaarPathWeights`, `HaarPathSupport` | Exact trace-to-path expansion, quantitative weights, phase vanishing, and the vertex-support restriction. |
| Actual classes | `HaarPathCounting`, `HaarPathRefinedCounting`, `HaarRefinedWeight` | Sparse reconstruction counts genuine incidence classes; refined profiles preserve the actual Haar integral through endpoint-fixed dart permutations and row/column invariance. |
| Coefficient fibres | `HaarRefinedPaletteFibre`, `HaarRefinedCoefficientFibre`, `HaarOperatorPathBridge.coefficient_bound` in `HaarRefinedCoefficientBound.lean` | Exact vertex-label and reduced-word palette parametrizations connect literal class sums to operator coefficient sums, first/last occurrence contractions, and the corrected composition budget. |
| One-pair estimate | `HaarPathClassAssembly`, `HaarOnePairAssembly`, `HaarPrescribedDimension.onePairLengthBounds`, `onePairTraceBound` | Finite class and length sums discharge every combinatorial and operator estimate. |
| Tensor expectation | `HaarTensorReplacement`, `HaarIteratedMoments`, `HaarCanonicalTransport`, `HaarExpectationFromMoment` | Successive replacement on distinct tensor legs, exact basis transport to the canonical sample space, and the expected operator-norm comparison. |
| Channel theorem | `HaarPrescribedDimension.explicitHaarExpectation`, `exists_prescribed_channel` | The proved expectation bound feeds the exact structured linearization, finite-net sample selection, Bell witness, and switch/Weyl conversion. |

### Two repaired intermediate counts

The proof follows Bordenave--Collins, arXiv:2304.05714v2, with two explicit
combinatorial corrections. These concern intermediate statements, not
counterexamples to the paper's final norm theorem.

1. In the exploration argument for Lemma 5.3, the final traversal can be a
   discovery-tree edge. `HaarPathExplorationCounterexample` gives a literal
   balanced reduced closed path where the smaller important-time bound
   fails. For integer defect `delta=2*chi`, the checked bound is
   `#importantTimes <= delta+2`. Reconstruction also retains the independent
   endpoint-color labels, giving the actual two-generator coarse-class bound
   `128^(delta+2)*m^(3*delta+6)` in `HaarPathClasses.card_defectClass_le`
   (`HaarPathCounting.lean`).
2. The block count `r <= 3*e` used in Lemma 5.9 fails for first/last-marker
   decompositions, where `e` counts distinct unoriented core edges. If `s`
   positions are marked, there are at most `s-1`
   middle runs and `s <= 2*e`. Only marked factors incur a length factor, so
   the needed combined exponent still obeys `r-1+s <= 6*e-2`.
   `HaarPathRuns`, `HaarPathRunCounterexample`, and `HaarMarkedCompositions`
   prove the counterexample and repaired bound. The resulting actual
   coefficient estimate is
   `D^v * 2^singletons * p^(9*delta+11) * norm(regular(A))^p`, where `v` is
   the number of visited vertices and `D` is the local matrix dimension.

`HaarEncodingSlack` supplies an earlier valid route with
`D >= 2^80*p^80`. `HaarSharpCounting`, `HaarSharpSummation`, and
`HaarSharpBound.onePairTraceBound` now recover the original
`D >= 2^32*p^80` range through weighted chronological encoding. Both use
the corrected operator coefficient estimate. No enlargement of the final
prescribed dimension or claim of dimension optimality is made.

## Separate interfaces and scope limits

The generic predicates `HaarModel.HaarStrongConvergence`,
`HaarConsequences.AllHaarStrongConvergence`,
`UpperHaarRealization.HaarUpperConvergence`, and `HaarTraceMomentControl`
remain unproved in their stated generality. Their older implication theorems
are retained, but none is a premise of `exists_prescribed_channel`.
The finite-Haar expectation inequality used by that theorem is fully proved;
this does not assert the paper's full two-sided strong-convergence theorem.

`HolevoRateLimit.lean` proves convergence of actual tensor-power Holevo rates
to their supremum. `OperationalCodingTheorem.lean` identifies both with
independently defined operational classical capacity. The arbitrary-use
version of `eq:chi-extension` is proved in `WeylPowersEntropy.lean`, with its
regularized supremum-minus-infimum form in `WeylPowersRegularized.lean`.
These results do not prove nonadditivity of operational capacity across
different channels, or a strong converse at every rate above capacity.

## Operational coding proof chain

The code definition is separate from Holevo information: a code contains
actual input density matrices and a normalized POVM, with its average error
computed from the Born probabilities. A code sequence supplies every
positive tensor-power length. An achievable rate has vanishing error and
eventually exceeds every smaller rate; operational capacity is the supremum
of such rates.

| Step | Main checked endpoints | Concrete content |
|---|---|---|
| Physical coding definitions | `Operational.Code`, `CodeSequence`, `AchievableRate`, `operationalCapacity` | Arbitrary input density matrices, complete POVM effects, uniform-message success, and vanishing actual error; capacity is not defined as a Holevo regularization |
| Spectral typicality | `QuantumCodingTypicalProjectors.lean`, `QuantumCodingConditionalTypicality.lean`, `QuantumCodingEnsembleTypicality.lean`, `QuantumCodingTypicalTests.lean` | Tensor spectra and actual global/conditional projectors; probability, rank, spectral ceiling, and independent interference estimates |
| Sequential decoder | `QuantumCoding.trace_union_bound_amplitude`; `ProjectiveTest.finite_filteredDecoder_error_bound` | Derived projective union bound and physical filtered POVM; per-message error at most nine global failures plus eight conditional failures plus four times competing-message interference |
| Random packing | `QuantumCoding.exists_projective_packing`, `exists_spectral_packing` | Exact finite product probabilities and one-/two-coordinate marginals select an actual codebook and normalized POVM; no decoding inequality is assumed |
| HSW achievability | `QuantumCoding.finite_ensemble_codes`, `ensemble_rate_achievable`, `holevoBits_le_operationalCapacity` | Actual channel-word encoders, integer message counts, vanishing packing error, and optimization over all finite output ensembles |
| All-length block conversion | `Operational.achievableRate_of_block`, `operationalCapacity_block_le` | Explicit Kraus-coordinate flattening, input padding, decoder transport, preserved error, and the rate factor `1/(k+1)` at every sufficiently large length |
| Quantitative weak converse | `Operational.Code.log_messages_le_holevo_add_error`; `CodeSequence.holevoCorrection_tendsto_zero`; `operationalCapacity_le_regularizedHolevoSupremum` | Actual POVM dilation, successful projection, spectral entropy continuity, and a vanishing finite-code correction, applicable to arbitrary encoders and decoders |
| Capacity equality | `Operational.operationalCapacity_eq_regularizedHolevoSupremum`; `FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo`; `normalizedPowerHolevo_tendsto_classicalCapacity` | Equality of independent operational and regularized definitions, and convergence of all actual normalized tensor-power Holevo quantities to capacity |

The finite-code converse in nats is
`log M <= chi(T)+2*sqrt(2*error)*log(M*d)+4*log 2`, where `d` is output
dimension. A separate dimension packing estimate eliminates the message
count from the normalized continuity correction. This supplies the weak
converse needed for the coding theorem without postulating a coding law or
an accessible-information bound.

## Unconditional actual realization and asymptotics

`DeterministicConsequences.separatingFamily` selects actual finite channels
from the deterministic theorem. `actual_vanishing_diverging` proves that
their single-use Holevo information tends to zero while half their two-use
information tends to infinity. The denominator is positive for every
`K >= 2`. Theorems `actual_gap_tendsto_atTop` and
`actual_ratio_tendsto_atTop` prove divergence of both separation measures.
`exists_small_chi_large_gap_and_ratio` simultaneously obtains any prescribed
small positive single-use upper bound, additive gap, and two-use ratio.

The regularized Holevo information, gain, and ratio also diverge, by
`actual_regularizedHolevo_tendsto_atTop`,
`actual_regularizedGain_tendsto_atTop`, and
`actual_regularizedRatio_tendsto_atTop`.
`exists_small_chi_large_regularized_gain_and_ratio` gives the simultaneous
existence result. They are statements about the genuine normalized
tensor-power limit and its equal supremum, now identified with independently
defined operational capacity by the coding theorem. None of these
deterministic theorems has an analytic input premise.

The older `HaarConsequences.exists_separating_family`,
`exists_large_gap_and_ratio`, and `exists_large_regularized_gain_and_ratio`
remain proved implications from `AllHaarStrongConvergence`. Likewise the
one-block Haar route and the weaker `UpperHaarRealization` route retain their
explicit convergence assumptions. Their predicates have not been proved by
the deterministic construction. The independent Gaussian route supplies
unconditional multiplicative and regularized-ratio separation, with explicit
polynomial dimensions, but does not itself give unbounded additive gaps.
The online-source review and provenance are recorded separately in
`RESOURCE_NOTES.md`.

## Additional completed manuscript claims

- `UniversalFactorization.exists_universal_factorization`: the same coefficients and scalar work in every nonzero complete complex Hilbert-space representation, including infinite dimension.
- `HaarSharpBound.onePairTraceBound`: the original numerical range `2^32*p^80 <= N+1`, using weighted chronological path-class counts.
- `HaarPrescribedRatio`, `HaarInputScaling`, and `HolevoPowerGap`: the exact ratio liminf, matching square-root input scaling, and vanishing normalized gap when regrouping a fixed channel.
- `HaarPrescribedProbability`: the explicit favorable probability fraction for the actual admissible Haar polynomial tests.
- `GapFractionAsymptotics`: the large-K expansion with an explicit remainder bounded by `162/(K^2*ln K)`.
- `PrescribedCostDimensions`, `PrescribedCostScaling`, and `PrescribedCostCapacity`: actual quadratic growing-family input cost and the matching information/capacity estimates in terms of that cost.

These are unconditional proofs of the stated endpoints. They do not assert the broader two-sided Haar strong-convergence predicates, or every background statement at arbitrary traced C*-algebra generality.
