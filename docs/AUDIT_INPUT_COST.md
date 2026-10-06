<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# AI source-to-Lean audit: growing-family input cost

Date: 2026-10-06. Targets: both exports in `ComparatorChallenges/E_InputCost.json`; result ID `growing-family-cost`. This is a fresh AI review by a separate reviewer agent, followed by a separate integration review. It is not a human review or a machine proof of equivalence between prose and Lean.

**Scoped declaration-fidelity verdict: PASS.** The two exports express the two asymptotic information bounds in the input-cost remark, with explicit positive constants, on the same selected family of genuine finite channels. The capacity conjunct additionally uses the proved operational coding theorem. The family agrees with the prescribed construction parameters eventually; the finite-prefix completion is not a claim about the manuscript's construction at invalid indices.

The selected `lean-statement-audit` method was read from [the pinned upstream skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/601fe274276d93052ef645f0ff2c1a355e8e5b16/skills/lean-statement-audit/SKILL.md), upstream revision `601fe274276d93052ef645f0ff2c1a355e8e5b16`, SHA-256 `2c315ad231e93a198ef2960dadc67234c263a0f4a4adf858aeb2d9270007dfab`. It is applied to an already proved release: there are no new freezes, draft declarations, or proof/module changes. The source's existential choice of channels does not impose a uniqueness requirement. The skill's checks for uniquely characterized objects therefore do not turn an existential channel construction into a unique-channel assertion.

## Identity and evidence boundary

The reviewed checkout started at `5aa9c82f86a6d91bee0ddf773500086e85d5d592`. The declaration inventory records proof-source commit `141f355a841cbf56fd1715750eebb9d2bcc488cb`, Lean `4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`. These are distinct provenance fields, not interchangeable commit claims.

The reviewer recomputed the following hashes and checked them against `verification/release-manifest.json`. Both production Lean files also match `metadata/declarations.json`'s source hashes.

| File | SHA-256 |
|---|---|
| `paper/nonadditivity.tex` | `3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98` |
| `ComparatorChallenges/E_InputCost.lean` | `c6fa18619310fe829efd9d8aaf14e3d219b854d14757983d6a6d3dba397fd1ec` |
| `ComparatorChallenges/E_InputCost.json` | `8e2f1a97e5f3051f3ebab7e543dc4515799c0748e3e4f9790b84d74c3f324d91` |
| `metadata/declarations.json` | `9e42707d1781901fe0e4f39e7b9340626832409329aa5c485e4f614ffb70b201` |
| `Nonadditivity/PrescribedCostScaling.lean` | `85f8fc8124fd4fe1058b739cc7b9fab40f2c7ef55bb5375f09e55a16c7985dc9` |
| `Nonadditivity/PrescribedCostCapacity.lean` | `5aa525f5d069898d108bc334dfe340436190669a53a8532cf54fbcbd65bb7fd5` |

The inventory's complete compressed kernel-expression types were decoded, their lengths and SHA-256 values recomputed, and their binder structure inspected. They have no universe parameters and no `forallE` nodes. Each has one ordinary lambda binding `K : Nat` as the predicate supplied to `Filter.Eventually`; neither has any explicit, implicit, or instance theorem parameter. Their kernel-type hashes are:

| Fully qualified export | Defining file and lines | Kernel-type SHA-256 |
|---|---|---|
| `Nonadditivity.PrescribedCost.growingFamily_chi_input_cost_bounds` | `Nonadditivity/PrescribedCostScaling.lean:84-99` | `5f0c9f932599a9f0a60d5fbd06d5cdcd4c793601af9f1c115234b916b8ad2ddc` |
| `Nonadditivity.PrescribedCost.growingFamily_two_use_input_cost_lower` | `Nonadditivity/PrescribedCostCapacity.lean:15-52` | `500f17e3879eaff13b65379013d29dcdd6e431fc15a28c49068ec58c92f84300` |

The readable types were compared with those full types and the actual declarations, not treated as complete evidence by themselves. The challenge statements at `ComparatorChallenges/E_InputCost.lean:14-29` repeat the concrete scale and match these production statement texts. Their `sorry` bodies are expected-statement fixtures, not the production proofs. This report does not use those fixtures as proof evidence.

Root-owned compiled exact-application and axiom checks are recorded separately in `verification/statement-audit-20261006/checks.json`. This reviewer inspected source and exported type evidence; it did not independently run a Lean kernel or Comparator. In particular, hash agreement establishes identity, not mathematical fidelity.

## Independent source reconstruction

This section was reconstructed from the raw manuscript before reading the challenge, implementation, or earlier reports.

The conventions are `log = log₂`, `ln = log_e`, and `q_in = log₂(dim A)`; these are real qubit counts, without rounding to an integer (`paper/nonadditivity.tex:240-243`). The information quantities use von Neumann entropy in bits (`paper/nonadditivity.tex:88-109`). For each integer `K ≥ 2`, set

\[
b_K=40(7\ln K+2),\qquad n_0(K)=\lceil256(1+\ln K)^2\rceil.
\]

For each integer `n ≥ n₀(K)`, the main construction selects a channel with `N = ceil(exp(b_K n))`, input dimension `2 N^n K^(2n)`, output dimension `K^n`, and joint bounds on that same channel (`paper/nonadditivity.tex:256-278`, `eq:dimension-constant`, `eq:main-holevo`). The explicit map measures the Weyl and switch labels, applies the block complementary channel or its conjugate, and conjugates the output by the Weyl unitary (`paper/nonadditivity.tex:934-959`, `eq:channel-T`). Its supplementary single-use lower bound is `χ(T) ≥ 2n/K` (`paper/nonadditivity.tex:1019-1024`, `eq:constructed-holevo-lower`).

For the input-cost remark (`paper/nonadditivity.tex:426-451`, `rem:separation-cost`, the numbered remark referenced as Remark 1.4), the quantifier order is: choose the family of quantitative-construction channels, then let the integer `K` tend to infinity, using the prescribed `n_K = ceil(K/sqrt(ln K))`. There is a sufficiently large integer threshold beyond which `n_K ≥ n₀(K)` and the construction is available. No caller supplies a favorable channel, entropy certificate, probability estimate, rate, or asymptotic hypothesis.

Writing `T_K` for this selected family and `q_K = log₂ dim Input(T_K)`, the source claims are:

1. Eventually, `2n_K/K ≤ χ(T_K) ≤ 9n_K/(K ln 2) + 2 log₂((n_K+1)/(n_K−1))`.
2. The correction is `O(1/n_K) = o(n_K/K)` and `n_K/K ~ 1/sqrt(ln K)`. Thus `χ(T_K) → 0` with a matching positive scale.
3. The same two-use estimate gives `χ(T_K ⊗ T_K)/2 ≥ n_K log₂ K/(2K)`, hence this per-use quantity and capacity diverge.
4. The exact input dimension gives `q_K/K² → 280/ln 2`.
5. With constants uniform in sufficiently large `K`, `χ(T_K) = Θ(1/sqrt(log₂ q_K))` and `χ(T_K ⊗ T_K)/2 = Ω(sqrt(log₂ q_K))`.

The general small/large existence statement and sequence are at `paper/nonadditivity.tex:390-424` (`cor:separation`, `eq:small-large`, `eq:vanishing-diverging`). That proof uses a qualitative channel with error `η_K = K⁻¹`. The input-cost remark deliberately chooses the quantitative family instead. The audited targets use that quantitative family, not the earlier qualitative family.

The unnumbered fixed-`K` scaling remark (`paper/nonadditivity.tex:281-314`, `eq:scaling`, `eq:input-size`) is different: fix `K` with `δ_K > 0`, then send `n → ∞`; its implicit constants may depend on `K`, and its gap is `Θ_K(sqrt(q_in))`. Neither E target makes a fixed-`K` claim or silently exchanges those limits. The growing-`K` input-cost conclusion concerns `χ` and half the two-use information at a further logarithmic scale, not that fixed-`K` gap statement.

## Exact conclusions and quantifier accounting

Put `L = sqrt(2/ln 2)`, `T_K = growingFamily K`, and `q_K = inputQubits K`. The first target says

\[
\exists K_0\in\mathbb N\;\forall K\ge K_0:\quad
\frac L2\le\chi(T_K)\sqrt{\log_2 q_K}
\le(9/\ln2+1)\,2L.
\]

The second says

\[
\exists K_1\in\mathbb N\;\forall K\ge K_1:\quad
\frac1{8\ln2\,L}\le
\frac{\chi(T_K\otimes T_K)/2}{\sqrt{\log_2q_K}}
\quad\land\quad
\frac1{8\ln2\,L}\le
\frac{C(T_K)}{\sqrt{\log_2q_K}}.
\]

These are the ordinary expansions of `∀ᶠ K : ℕ in atTop`. The thresholds can be increased or combined by taking their maximum. Both theorems refer to the same already selected `growingFamily`; their separate thresholds do not authorize separate channel witnesses.

### Five-bin input test

| Export | Explicit premise binders | Implicit premise binders | Instance premise binders | SOURCE | STANDING | TYPING | RULED | EXCESS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `growingFamily_chi_input_cost_bounds` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `growingFamily_two_use_input_cost_lower` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

There are zero rows of actual theorem-input binders to classify. In particular, `atTop`, the real order/arithmetic instances, and the selected channel's stored finite instances are concrete arguments inside the closed expression, not quantified assumptions. There is no hidden project-owned Prop/structure/typeclass premise.

For completeness, the actual non-input binders and the logical expansion of each conclusion are recorded individually:

| Export | Binder | Kind and scope | Classification | Source |
|---|---|---|---|---|
| χ bounds | `K : ℕ` | Ordinary lambda in the `Eventually` predicate | SOURCE conclusion index; not an input | `rem:separation-cost`, paper lines 428-449 |
| two-use/capacity bounds | `K : ℕ` | Ordinary lambda in the `Eventually` predicate | SOURCE conclusion index; not an input | Same lines 428-449; capacity relation lines 104-109 |
| χ bounds, expanded | `K₀ : ℕ` | Existential threshold witness | SOURCE eventual-conclusion witness | Paper lines 432-433 |
| χ bounds, expanded | `K : ℕ` | Universal index following the threshold | SOURCE conclusion index | Paper lines 428-449 |
| χ bounds, expanded | `h : K₀ ≤ K` | Domain implication under that universal | SOURCE eventual-domain restriction | Paper lines 432-433 |
| two-use/capacity bounds, expanded | `K₁ : ℕ` | Existential threshold witness | SOURCE eventual-conclusion witness | Paper lines 432-433 |
| two-use/capacity bounds, expanded | `K : ℕ` | Universal index following the threshold | SOURCE conclusion index | Paper lines 428-449 |
| two-use/capacity bounds, expanded | `h : K₁ ≤ K` | Domain implication under that universal | SOURCE eventual-domain restriction | Paper lines 432-433 |

The actual-lambda tally is SOURCE 1 per target and zero in every other bin; the alternative expanded-conclusion tally is SOURCE 3 per target and zero in every other bin. These are separate views, not extra caller premises and not to be added to the zero-input tally.

The selected witness producer was also checked for hidden logical inputs. Its full source-facing binder inventory is:

| Declaration | Binder, in order | Binder kind | Bin | Source |
|---|---|---|---|---|
| `exists_prescribed_channel_with_lower_bound` | `K : ℕ` | implicit | SOURCE | Main theorem, paper line 257 |
| same | `n : ℕ` | implicit | SOURCE | Main theorem, paper line 263 |
| same | `hK : 2 ≤ K` | explicit | SOURCE | Paper line 257 |
| same | `hn : Quantitative.n₀ K ≤ n` | explicit | SOURCE | Paper lines 260, 263 |

Producer counts: SOURCE 4, STANDING 0, TYPING 0, RULED 0, EXCESS 0. The local `NeZero K` is constructed from `hK`, and `explicitHaarExpectation hK hn` is supplied in the proof (`Nonadditivity/HaarPrescribedBound.lean:65-96`). Neither is an extra exported premise. The conditional helper in `Nonadditivity/HaarPrescribedDimension.lean:39-51` is not the producer used by `prescribedFamily`.

## Definition and carrier closure

All project constants directly named in either exported type were expanded. The following table records the semantic closure inspected, including the selected witness and normalizations. Routine Mathlib real arithmetic, logarithms, finite cardinalities, and filter definitions are the library boundary. This is not a new audit of all transitive analytic proofs in the release.

| Definition / bundle | Actual body and mathematical meaning | File/line citation; source comparison |
|---|---|---|
| `Asymptotics.blockLength` | Natural ceiling of `(K:ℝ)/sqrt(ln K)`. On `K ≥ 2` this is exactly the source integer `n_K`. | `Nonadditivity/Asymptotics.lean:31-32`; paper 410, 429 |
| `Quantitative.n₀` | `ceil(256(1+ln K)²)` in `ℕ`. | `Nonadditivity/Quantitative.lean:347-348`; paper 259-260 |
| `dimensionExponent`, `dimensionChoice`, `localDimension`, `matrixDimension` | `40(7h+2)`, `ceil(exp(dimensionExponent h · n))`, specialization at `h=ln K`, and the same general ceiling respectively. `sampleSize=N−1` is reconciled by `sampleSize_add_one`, not a replacement dimension. | `Nonadditivity/Quantitative.lean:85-87`; `Nonadditivity/StructuredHaarConsequences.lean:26-36`; `Nonadditivity/Dimensions.lean:25`; paper 259-266 |
| `prescribedFamily` | `Classical.choose` from the **joint** proved existence theorem at `max(n₀(K),n)`. Its explicit parameters are `{K:ℕ}`, `hK:2≤K`, `n:ℕ`; there is no analytic certificate parameter. | `Nonadditivity/HaarPrescribedConsequences.lean:21-48`; paper 263-273, 1019-1024 |
| `growingFamily` | For `K≥2`, `prescribedFamily hK (blockLength K)`; for `K=0,1`, the prescribed `K=2` family at index 1. It is a total sequence of genuine channels. | `Nonadditivity/PrescribedCostDimensions.lean:90-101`; eventual source domain paper 432-433 |
| `inputQubits` | `Scalar.log2 (Fintype.card (growingFamily K).Input)`. The quantity is computed from this actual channel's stored input carrier. | `Nonadditivity/PrescribedCostLogarithms.lean:13`; paper 241-243 |
| `scalarInputQubits`, `Dimensions.inputDimension`, `Dimensions.inputQubits` | Auxiliary literal dimension expression `log₂(2N^nK^(2n))` with `n=n_K`, `N=ceil(exp(b_Kn_K))`; eventually proved equal to the actual channel count. | `Nonadditivity/PrescribedCostDimensions.lean:15-17,96-110`; `Nonadditivity/Dimensions.lean:24-29`; paper 443-444 |
| `Scalar.log2`, `Scalar.aK` | `ln x/ln2`, and `log₂(1+9/K)`. | `Nonadditivity/Scalar.lean:26-27`; paper 241,246 |
| `inputLogScale` | The fixed positive real `sqrt(2/ln2)`. It has no hidden dependence on `K`, a channel, or a threshold. | `Nonadditivity/PrescribedCostScaling.lean:63-67`; derived from paper 444 and its logarithmic scale, not a quoted source constant |
| `finiteSizeCorrection`, `kappa` | `4 log₂((n+1)/(n−1))` and `(n+1)/(n−1)`. The one-use upper bound uses half the correction, hence the required factor **2**, not 4. | `Nonadditivity/Asymptotics.lean:158-159`; `Nonadditivity/StructuredHaarConsequences.lean:55`; `Nonadditivity/HaarPrescribedConsequences.lean:50-53`; paper 437-438 |
| `separationLower` | `n_K ln K/(2K ln2)`: already a lower bound on **half** the two-use information. | `Nonadditivity/Asymptotics.lean:38-40`; paper 417-419 |
| `FiniteQuantumChannel` and `ofKraus` | Stores input, output, environment types, their finite instances, nonempty input/output, and an actual Kraus channel. `ofKraus` copies those carriers and the map; it does not store arbitrary information numbers or bounds. | `Nonadditivity/ActualConsequences.lean:34-68`; paper 88-92,264-267 |
| `KrausChannel`, `map`, `output` | Kraus matrices `A_k` with `ΣA_k* A_k=I`; map `X↦ΣA_k X A_k*`; output bundles the resulting positive trace-one matrix. | `Nonadditivity/Channels.lean:29-40,78-82`; paper 88-92 |
| `chi`, `chiTwo`, `holevoBits` | Actual channel Holevo information divided by `ln2`; `chiTwo` applies it to `T.channel.tensor T.channel`. It is total information of two uses before the explicit `/2` in E. | `Nonadditivity/ActualConsequences.lean:70-72`; `Nonadditivity/HolevoBits.lean:24`; paper 95-101,417-419 |
| `KrausChannel.tensor` | Kronecker products of the two Kraus families on product input/output/environment types. All joint input states are allowed; no product-state restriction is introduced. | `Nonadditivity/Channels.lean:279-294`; paper 397,403,448 |
| `outputs`, `holevo`, `StateEnsembles.quantity` | Range of actual output states; supremum of entropy-of-average minus average entropy over arbitrary finite ensembles in that range. Finite output ensembles can be lifted to input ensembles by selecting preimages. | `Nonadditivity/QuantumHolevo.lean:27-32`; `Nonadditivity/StateEnsembles.lean:90-109`; paper 95-101 |
| `DensityMatrix`, `weights`, `vonNeumann`, `shannon`, `mixture` | Positive trace-one complex matrix; Hermitian eigenvalues; natural-log spectral entropy `−Σp ln p`; actual convex matrix combination. Dividing by `ln2` supplies the source's bit convention, with zero spectral terms contributing zero. | `Nonadditivity/Entropy.lean:32-33,142-164`; `Nonadditivity/StateEnsembles.lean:33-42`; paper 95-101 |
| Producer's `converted (blockChannel U n)` | Complementary channels of uniform unitary mixtures, tensored and reindexed to output `ZMod(K^n)`, followed by the switch and Weyl extension. The existential witness is built from these actual maps. | `Nonadditivity/HaarPrescribedBound.lean:76-93`; `Nonadditivity/BlockConstruction.lean:116-123`; `Nonadditivity/BlockBell.lean:146-150`; `Nonadditivity/Channels.lean:155-157,182-190`; paper 147-169,934-959 |
| `tensorChain`, `reindex` | Recursive channel tensor products; basis relabeling by an equivalence. The base tensor object is the one-dimensional empty product, not a default substituted for a nonzero block. | `Nonadditivity/TensorPowers.lean:172-178`; `Nonadditivity/ChannelReindex.lean:68-79`; source block construction |
| `converted`, `switch`, `conjugate` | `T.switch.weylExtension`; controlled original/conjugated Kraus matrices with Boolean input label. | `Nonadditivity/Conversion.lean:27`; `Nonadditivity/SwitchChannel.lean:30-31`; `Nonadditivity/Channels.lean:319-320`; paper 939-943 |
| `weylExtension`, `covariantExtension`, `controlled`, `selector`, `outputUnitary`, `Weyl.family` | Precisely `d²` Weyl labels; measure label, apply the branch, conjugate output by phase/shift unitary. Kraus entries are literal matrices and label selectors. | `Nonadditivity/ChannelEntropy.lean:118-120`; `Nonadditivity/ChannelExtensions.lean:28-29,76-77,103-105,125-127`; `Nonadditivity/Weyl.lean:30-34,62-64,155-156`; paper 934-947 |
| `derivedUnitary` | Evaluate the selected short free-group word in the sampled local pair of unitaries; finite matrix carrier `Fin(sampleSize+1)` gives the prescribed `N`. | `Nonadditivity/StructuredHaarModel.lean:96-109`; `Nonadditivity/InitialNetReduction.lean:547-561`; paper 1230-1241 |
| `classicalCapacity` | `Operational.operationalCapacity T.channel`, the supremum of rates achieved by physical code sequences with vanishing average decoding error. | `Nonadditivity/OperationalCodingTheorem.lean:62-69`; `Nonadditivity/OperationalCapacity.lean:140-146`; paper 104-109 |
| `CodeSequence`, `rate`, `VanishingError`, `HasRate`, `Code`, `POVM`, `success`, `error` | Positive message counts at every positive block length; `log₂(messages)/(n+1)`; eventual lower rates and actual Born error tending to zero. Encodings are arbitrary density matrices and decoders are normalized positive effects, with average success over uniform messages. | `Nonadditivity/OperationalCapacity.lean:29-46`; `Nonadditivity/OperationalConverse.lean:29-40,82-84,129-133`; separately reviewed in `docs/AUDIT_CODING.md` |
| `positiveTensorPower`, `normalizedPowerHolevo`, `regularizedHolevo` | Index `n` means `n+1` uses, divided by `n+1`, and then supremum over all such indices. The independently defined operational capacity is proved equal to this supremum. | `Nonadditivity/RegularizedHolevo.lean:68-88,129-130`; `Nonadditivity/OperationalCodingTheorem.lean:50-53,67-80`; paper 104-109 |

The stored finite/decidable/nonempty fields of `FiniteQuantumChannel` and positivity/normalization fields of density matrices and POVMs are concrete mathematical carriers and validity conditions. In E they are supplied by the closed selected object; none becomes a new premise of either theorem. No `AnalyticInputs` object from the older conditional API is a parameter of the selected family.

### Choice and finite-prefix checks

`prescribedFamily_spec` and `prescribedFamily_chi_lower` both project `Classical.choose_spec` of the identical proposition `exists_prescribed_channel_with_lower_bound hK (le_max_left (n₀ K) n)` (`Nonadditivity/HaarPrescribedConsequences.lean:23-48`). The producer includes input/output dimensions, positivity, the `2n/K` lower bound, the one-use upper bound, the two-use lower bound, and the gap bound in one conjunction. It constructs its witness using the actual conversion map (`Nonadditivity/HaarPrescribedBound.lean:65-96`). Therefore the lower estimate cannot belong to one selected channel and the upper estimate or input dimension to another.

The source does not define a unique channel or a witness-independent value of `χ`. Classical selection from proved joint existence is legitimate here. The source properties hold for every witness satisfying that conjunction, and hence for the selected witness. This audit does not claim that `Classical.choose` is definitionally equal to the producer's syntactically displayed witness, nor that all valid channel witnesses are equal.

The two finite-prefix completions deserve a qualified verdict. `prescribedFamily` replaces too-small `n` by `max(n₀(K),n)`; `growingFamily` handles `K=0,1` by another genuine channel. They are not literal source constructions at those indices. `threshold_le_blockLength_eventually` is a proved theorem (`Nonadditivity/PrescribedCostScalars.lean:78-85`), using the unchanged `n_K`, and the actual information/dimension proofs intersect it with `K ≥ 2` (`Nonadditivity/PrescribedCostDimensions.lean:96-101`; `Nonadditivity/PrescribedCostInformation.lean:15-31`). Thus both completions disappear before every claimed eventual source formula. They do not supply a surrogate dimension or fabricate an entropy bound outside a still-unproved valid locus.

Definition verdicts, at the stated source scope:

| Semantic unit | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|
| Literal numerical and information definitions above | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `prescribedFamily` plus joint producer and both specifications | OK (existential selection) | OK (source parameters once `n≥n₀`) | OK (proved existence) | OK (all required joint properties) | N/A (source does not require uniqueness) | PASS for source domain |
| `growingFamily` plus eventual threshold, information, and dimension theorems | OK (eventual construction) | OK (total channel sequence; eventual source correspondence) | OK | OK (eventual joint properties) | N/A (existential family) | PASS for eventual claims |

The last two rows do **not** certify unrestricted pointwise equality to a paper-defined unique object. No such object is claimed by the manuscript or by these E statements.

## Consumption, scales, and threshold checks

The inspected proof chain supplies every source-specific bound internally:

| Obligation | Evidence and interpretation |
|---|---|
| Unmodified rounded `n_K` eventually admissible | `normalized_blockLength_tendsto_one` proves `n_K sqrt(ln K)/K→1` (`Nonadditivity/PrescribedCostScalars.lean:29-51`); `threshold_div_sqrt_tendsto_zero` and `threshold_le_blockLength_eventually` discharge the construction domain (`:59-85`). No `n_K≥n₀(K)` premise remains in E. The source's stronger ratio observation motivates this; E requires and proves the eventual inequality. |
| Same-channel χ and two-use bounds | `growingFamily_bounds_eventually` (`Nonadditivity/PrescribedCostInformation.lean:15-31`) consumes the same-family specifications. The displayed upper bound is first `n_K a_K + correction/2`; the proof then uses `a_K ≤ 9/(K ln2)`, as in the paper. |
| Exact qubit cost | `scalarInputQubits_div_sq_tendsto` and eventual equality to actual input cardinality prove `q_K/K²→280/ln2` (`Nonadditivity/PrescribedCostDimensions.lean:24-110`). The main term is `(280 lnK+80)n_K²/ln2`; the `ceil(exp(...))` error and the `2n_K log₂K+1` terms are controlled and vanish after division by `K²`. |
| Correct logarithmic conversion constant | `log_inputQubits_div_log_tendsto` proves `ln(q_K)/lnK→2`, then `log2_inputQubits_div_log_tendsto` gives `log₂(q_K)/lnK→2/ln2`, then square roots give `L` (`Nonadditivity/PrescribedCostLogarithms.lean:28-57`). There is no missing factor of `ln2`. |
| Vanishing correction at the needed scale | `finiteSizeCorrection_le_inverse` gives the `O(1/n_K)` bound (`Nonadditivity/PrescribedCostInformation.lean:72-88`); `correction_sqrt_log_tendsto_zero` gives the negligible correction after multiplication by `sqrt(lnK)` (`Nonadditivity/PrescribedCostScaling.lean:14-26`). Combined with normalized `n_K`, this supports the paper's `o(n_K/K)` observation, without pretending E itself is a named little-o theorem. |
| Two-sided χ scale | `growingFamily_chi_scaled_bounds` proves eventually `1≤χ(T_K)sqrt(lnK)≤9/ln2+1` (`Nonadditivity/PrescribedCostScaling.lean:28-61`). `input_sqrt_ratio_bounds` supplies `L/2≤sqrt(log₂q_K)/sqrt(lnK)≤2L` (`:69-80`). The exact target multiplies those inequalities (`:89-99`). |
| Positive denominators | `inputLogScale_pos`, `log_nat_pos` at `K≥2`, and the lower square-root ratio imply `sqrt(log₂q_K)>0`. The second target proves this explicitly (`Nonadditivity/PrescribedCostCapacity.lean:25-31`). Totalized real logarithms or division at zero are not used to justify the asymptotic conclusion. |
| Correct two-use per-use factor | `separationLower K` is `n_K log₂K/(2K)≤χ(T_K⊗T_K)/2`; the two factors of 2 are consistent. Combining normalized `n_K>1/2` with the upper square-root ratio gives the deliberately nonoptimal positive constant `1/(8 ln2 L)` (`Nonadditivity/PrescribedCostCapacity.lean:21-50`). The theorem does not claim equality, a matching upper bound, or an optimal leading constant. |
| Capacity on the same scale | `half_chiTwo_le_classicalCapacity` is applied for the same `growingFamily K`, then divided by the positive denominator (`Nonadditivity/PrescribedCostCapacity.lean:50-52`; `Nonadditivity/OperationalCodingTheorem.lean:77-80`). The operational meaning and coding equality receive the separate review in `docs/AUDIT_CODING.md`. |

In particular, `inputQubits` is already `log₂` of input **dimension**. E then takes `sqrt(log₂(inputQubits))`, exactly the paper's `sqrt(log q_in)`. It is not `sqrt(log₂ dimension)` and is not an auxiliary dimension sequence detached from `T_K`.

The first target's positive upper/lower constants and eventual positive square root give the claimed Θ statement by division. The first conjunct of the second target gives the claimed Ω statement; its capacity conjunct is the corresponding consequence of `C(T)≥χ(T⊗T)/2`. These are quantitative realizations of the manuscript's asymptotic claims, with constants fixed before `K`; no extra assumption is paid for them.

## Coverage and limitations

This review covers the two E exported statements, their full inventory types, source premises and quantifier scope, all project-owned constants directly appearing in those types, the relevant numerical and information-definition closure, the joint selected-witness mechanism, the concrete channel construction route, and consumption of the scalar and channel bounds in the two proofs. It also checked the accompanying exact-cost and vanishing/diverging statements where needed to interpret the source remark. The fixed-`K` scaling remark was read to disambiguate limits; its separate Lean endpoints are not certified by this report.

This is a bounded source-to-formalization review, not a line-by-line reproof of Haar integration, refined path enumeration, free-group embedding, every entropy theorem, or the HSW coding proof. The concrete construction route and the fact that its analytic obligations are internally supplied were inspected; those large mathematical dependencies retain their separate release and audit evidence. The operational definitions were inspected here, with full coding-target review delegated to the independently written `docs/AUDIT_CODING.md`.

No declaration mismatch, missing source premise, excess target hypothesis, detached input-cost proxy, witness split, logarithm-base error, or two-use normalization error was found. Finite-prefix totalization is an explicit scope qualification, not a finding that the construction is paper-exact for every natural index. The source-fidelity conclusion remains an AI judgment. Compiled application, axiom closure, and final integration status must be read from the [retained verification evidence](../verification/statement-audit-20261006/checks.json) rather than inferred from this prose.
