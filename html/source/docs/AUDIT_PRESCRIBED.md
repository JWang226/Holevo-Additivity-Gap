<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# Independent AI statement audit: prescribed dimensions

This is an independent AI source-correspondence review dated 2026-10-06. It is not a machine proof that English and Lean are equivalent, and it is not a replacement for kernel checking or human mathematical review. I read the manuscript passages below before inspecting the challenge, exported type, or implementation. No earlier proof-map summary supplied the mathematical reconstruction.

**Verdict: qualified correspondence; no excess premise or mathematical mismatch identified in the target statement.** The qualification is that the target combines Theorem `thm:main` with its separately stated constructed-channel lower bound and the resulting positivity. It is therefore a source-supported strengthening of the printed theorem, not a word-for-word transcription of that theorem alone. Finite basis indices and a finite Kraus realization represent the manuscript's full matrix algebras and CPTP channel. Verification of compilation, axiom closure, and hashes belongs to the accompanying release checks; I did not run builds or change proofs.

The review method adapts the [pinned lean-statement-audit skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/601fe274276d93052ef645f0ff2c1a355e8e5b16/skills/lean-statement-audit/SKILL.md). This is an audit of an existing solved release, not a new statement-freezing or draft workflow. The authorized adaptation permits classical selection of existential witnesses; uniqueness is required only when the source asserts a uniquely characterized object, which it does not here.

## 1. Source-first reconstruction

The source is `paper/nonadditivity.tex`.

| Source location | Independently reconstructed content |
| --- | --- |
| Lines 88–101; `eq:def-chi` | A channel is a complex-linear completely positive trace-preserving map on the **full** complex matrix algebra. Holevo information is the supremum over finite probability ensembles of output entropy minus average output entropy. States are positive semidefinite trace-one matrices. Entropy is von Neumann entropy in bits. |
| Lines 111–115; `eq:def-gap` | The two-use gap is `chi(T tensor T) - 2 chi(T)`, on two uses of the **same** channel. |
| Lines 240–253; `eq:delta` | `log` means base two and `ln` means natural logarithm. For integer `K >= 2`, `a_K = log2(1+9/K)` and `delta_K = log2(K)/K - 2 a_K`. Positivity of `delta_K` is discussed separately and is **not** a premise of Theorem 1. |
| Lines 256–279; `thm:main`, `eq:dimension-constant`, `eq:main-holevo`, `eq:main-gap` | For each integer `K >= 2`, set `b_K = 40(7 ln K + 2)` and `n0(K) = ceil(256(1+ln K)^2)`. For every integer `n >= n0(K)`, set `N = ceil(exp(b_K n))`. There exists a channel from matrices of size `2 N^n K^(2n)` to matrices of size `K^n`, satisfying the one-use upper bound, two-use lower bound, and gap lower bound. |
| Lines 525–565; `eq:gram`, `eq:tensor-words` | The base channel is the tensor product of local complements of uniformly mixed unitary channels, on input dimension `N^n` and output dimension `K^n`. The source allows arbitrary unitary tuples satisfying the subsequently proved estimate. |
| Lines 854–867 and 893–916; `eq:extension`, `eq:twirl` | The switch measures a bit, applies the channel or its complex conjugate, and discards the bit. The Weyl extension measures a label of size `L^2`, conjugates the output, and discards this label too. Neither operation keeps an output flag. |
| Lines 934–968; `eq:channel-T`, `eq:certificate-holevo`, `eq:certificate-gap` | The same converted channel has input dimension `2 N^n K^(2n)`, output dimension `K^n`, and all three estimates. Only its one-use upper estimate and gap estimate require the norm certificate; the two-use lower estimate holds for all unitary tuples. |
| Lines 970–1025; `eq:constructed-holevo-lower` | **Every channel constructed by `eq:channel-T`** satisfies `chi(T) >= 2n/K`. This is not an extra restriction on which unitaries may be chosen. The source obtains it by merging the first two local branch weights using an eigenvector and then using a product input. |
| Lines 1811–1819; proof of `thm:main` | The theorem's channel is precisely this construction, with the prescribed `N` and `kappa = (n+1)/(n-1)`. Thus the supplementary lower bound holds on its same witness. |

The quantifier order is

`forall K in N, K >= 2 -> forall n in N, n >= n0(K) -> exists T, P(K,n,T)`.

The source says integers, but both lower bounds force nonnegative integers; naturals cover exactly this domain. `b_K` depends only on `K`; `n0` depends only on `K`; `N` and the existential channel may depend on both `K` and `n`. There is no single channel required to serve different `n`. Within each fixed pair `(K,n)`, one channel must satisfy **all** seven Lean conjuncts. There is no separately chosen witness for positivity, the single-use lower estimate, or the two-use estimate.

Writing `kappa_n = (n+1)/(n-1)`, the reconstructed combined conclusion is

`dim_in(T) = 2 N^n K^(2n)`, `dim_out(T) = K^n`,

`0 < chi(T)`, `2n/K <= chi(T) <= n a_K + 2 log2(kappa_n)`,

`n log2(K)/K <= chi(T tensor T)`,

`n delta_K - 4 log2(kappa_n) <= chi(T tensor T) - 2 chi(T)`.

Strict positivity follows from the supplementary lower bound and `n >= n0(K) > 0`, `K >= 2`. No positive-gap premise is present or needed.

## 2. Exact target and exported type

- Challenge: `ComparatorChallenges/A_PrescribedDimensions.lean:13–22`.
- Actual theorem: `Nonadditivity/HaarPrescribedBound.lean:65–96`.
- Fully qualified export: `Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound`.
- Challenge mapping and axiom policy: `ComparatorChallenges/A_PrescribedDimensions.json:1–13`.
- Export record: `metadata/declarations.json:464870–464978`, declaration of that exact name; module `Nonadditivity.HaarPrescribedBound`, kind `theorem`, no universe parameters. Its `type_sha256` is `9f95991a877e0b93dd83adc1013a36920cb49d522ade89be39819871ea483bff`.
- Result association: `prescribed-dimensions` in `metadata/results.json`. I used this association only after reconstructing and comparing the source.

The challenge and actual theorem have the same source-level type, apart from whitespace. The exported `type_readable` independently exposes two implicit natural-number binders followed by the two inequalities and the same nested existential/conjunction. It contains no analytical input, typeclass assumption, hidden family parameter, convergence certificate, or positive-gap hypothesis. The pretty-printed export omits the annotation on existential `T`, but its typed projections are those of `ActualConsequences.FiniteQuantumChannel`; the source declaration supplies the annotation explicitly.

The intentional `sorry` in the expected-statement challenge is not the solution. The solution is the theorem at the actual file above; the challenge configuration names that solution module. I do not infer proof validity from the challenge.

## 3. Five-bin binder audit

These are **all four outer binders** of the actual target. Each explicit, implicit, and instance binder is accounted for; there are no instance binders or universe binders to add.

| Binder | Binder information and Lean type | Bin | Source justification |
| --- | --- | --- | --- |
| `K` | Implicit, `K : Nat` | SOURCE | Integer channel parameter in `thm:main`, lines 257–263; the lower bound restricts it to positive integers. |
| `n` | Implicit, `n : Nat` | SOURCE | Integer block length in `thm:main`, line 263; the threshold restricts it to positive integers. |
| `hK` | Explicit proof, `2 <= K` | SOURCE | Exactly line 257. |
| `hn` | Explicit proof, `Quantitative.n₀ K <= n` | SOURCE | Exactly lines 259–263, after the literal definition expansion below. |

**Outer-input counts:** SOURCE 4; STANDING 0; TYPING 0; RULED 0; EXCESS 0. The mathematical parameters `K` and `n` are SOURCE because the manuscript explicitly quantifies them; finite basis carriers and implementation instances below remain TYPING. No input package needs to be expanded. In particular, `[NeZero K]` is constructed inside the proof at `HaarPrescribedBound.lean:75`, not required from the caller. The conditional path-bound theorem at `HaarPrescribedDimension.lean:39–51` is a different declaration and is not the audited target.

The existential binder is `T : ActualConsequences.FiniteQuantumChannel`, classified SOURCE as a **returned witness**, with scope over all seven conjuncts (`thm:main:264–278`, `eq:constructed-holevo-lower:1021–1025`). Adding this output binder gives SOURCE 5, TYPING 0, STANDING/RULED/EXCESS 0. It is not counted as a premise.

The carrier expansion below checks that the existential does not hide an assumption package. These fields are data or properties of the **returned** object, not hypotheses imposed on the user. Every field is listed, including its nested Kraus proof field.

| Expanded field | Lean type | Bin | Meaning and source justification |
| --- | --- | --- | --- |
| `T.Input` | `Type` | TYPING | Basis labels for the source full input matrix algebra, lines 88–92, 266. |
| `T.Output` | `Type` | TYPING | Basis labels for the source full output matrix algebra, same source. |
| `T.Environment` | `Type` | TYPING | Kraus index carrier for a finite realization, consistent with the explicit finite Stinespring construction, lines 525–548. |
| `T.inputFinite` | `Fintype T.Input` | TYPING | Finite input dimension, lines 266 and 947. |
| `T.inputDecidable` | `DecidableEq T.Input` | TYPING | Equality implementation for finite matrix indices; no mathematical estimate. |
| `T.inputNonempty` | `Nonempty T.Input` | TYPING | Positive input dimension follows from `K >= 2`, the positive exponential ceiling, and the dimension formula. |
| `T.outputFinite` | `Fintype T.Output` | TYPING | Finite output dimension `K^n`. |
| `T.outputDecidable` | `DecidableEq T.Output` | TYPING | Equality implementation for finite matrix indices. |
| `T.outputNonempty` | `Nonempty T.Output` | TYPING | `K^n > 0` on the source domain. |
| `T.environmentFinite` | `Fintype T.Environment` | TYPING | A finite Kraus family, as in the source's finite construction. No bound on environment size is imposed. |
| `T.channel` | `@KrausChannel T.Input T.Output T.Environment T.inputFinite T.inputDecidable T.outputFinite T.environmentFinite` | SOURCE | The returned actual channel, as required in lines 88–92 and 264–267. |
| `T.channel.kraus` | `T.Environment -> Matrix T.Output T.Input Complex` | TYPING | Rectangular Kraus matrices representing its linear map. |
| `T.channel.complete` | `sum k, (kraus k).conjTranspose * kraus k = 1` | SOURCE | Trace preservation of the returned Kraus map; positivity at every amplification follows from the Kraus form. |

**Returned channel field counts:** SOURCE 2; TYPING 11; STANDING/RULED/EXCESS 0. The two SOURCE rows express channel structure, not new channel-information inequalities. There are no entropy, gap, Haar, or norm-bound fields in this structure (`ActualConsequences.lean:34–45`; `Channels.lean:29–32`).

For completeness, the nested state and ensemble predicates that define Holevo information also contain proof fields. They constrain the states and ensembles **over which the quantity is defined**, not the theorem caller:

| Semantic carrier field | Lean type | Bin | Source justification |
| --- | --- | --- | --- |
| Density matrix `matrix` | `Matrix i i Complex` | TYPING | State on the finite Hilbert space, source lines 88–101. |
| Density matrix `positive` | `matrix.PosSemidef` | SOURCE | Positivity of a quantum state, same source convention. |
| Density matrix `normalized` | `matrix.trace = 1` | SOURCE | Trace-one normalization, same source convention. |
| Ensemble `size` | `Nat` | TYPING | Finite ensemble index length, `eq:def-chi`. |
| Ensemble `weight` | `Fin size -> Real` | TYPING | Ensemble probabilities, `eq:def-chi`. |
| Ensemble `weight_nonneg` | `forall i : Fin size, 0 <= weight i` | SOURCE | Probability nonnegativity. The inner `i` only indexes these required inequalities. |
| Ensemble `weight_sum` | `sum i, weight i = 1` | SOURCE | Probability normalization. |
| Ensemble `state` | `Fin size -> DensityMatrix i` | TYPING | Output state for each finite label. |
| Ensemble `state_mem` | `forall j : Fin size, state j in outputs` | SOURCE | Each output state is in the actual channel range. Expanding membership gives `exists rho : DensityMatrix Input, output rho = state j`; this is a preimage condition, not a promised estimate. |

**State/ensemble field counts:** SOURCE 5; TYPING 4; STANDING/RULED/EXCESS 0. Generic finite index types, their `Fintype` and `DecidableEq` instances in these definitions supply type formation only. The internal `forall i`/`forall j` binders range over `Fin size` (TYPING), and the range preimage `exists rho` is a returned state witness (SOURCE). None is an additional outer premise. An empty ensemble is impossible because its weights would have sum zero instead of one; arbitrary positive finite ensemble sizes are included.

## 4. Meaning-carrying definitions

The following is the semantic expansion used in the comparison. The first five rows cover the project definitions controlling the theorem's scalar constants and dimensions, including its intermediate natural-log gap coefficient.

| Definition and implementation location | Expanded mathematical meaning and judgment |
| --- | --- |
| `Scalar.log2`, `aK`, `deltaK`; `Nonadditivity/Scalar.lean:26–28` | `ln(x)/ln(2)`, `log2(1+9/K)`, and `log2(K)/K-2 aK(K)`. These match `eq:delta` and the source bits convention, without an extra factor of `ln(2)`. |
| Internal `BlockScalars.gapCoefficient`; `Nonadditivity/BlockScalars.lean:77–78` | The natural-log version `ln(K)/K - 2 ln(1+9/K)` used in the intermediate bound; it is not substituted for the bits-valued `deltaK` in the endpoint. |
| `Quantitative.dimensionExponent`, `dimensionChoice`; `Nonadditivity/Quantitative.lean:85–87` | `40(7h+2)` and the natural ceiling of `exp(dimensionExponent(h)*n)`. Substitution `h=ln K` gives exactly `b_K` and `N`. Natural ceiling agrees with the source integer ceiling because the argument is positive. |
| `Quantitative.n₀`; `Nonadditivity/Quantitative.lean:347–348` | Exactly the natural ceiling of `256(1+ln K)^2`. The source argument is nonnegative, so this is the stated threshold. The proved consequence `n >= 64` at lines 350–364 confirms that denominator `n-1` is positive on the audited domain. |
| `StructuredHaarConsequences.localDimension`, `sampleSize`, `kappa`; `Nonadditivity/StructuredHaarConsequences.lean:26–35,54–55` | `localDimension=N`, sample index `N-1`, and real quotient `(n+1)/(n-1)`. `sampleSize+1=N` is proved. There is no mistaken local dimension `N+1`, floor in place of ceiling, or natural-number subtraction in the real denominator. |
| `FiniteQuantumChannel`, `ofKraus`; `Nonadditivity/ActualConsequences.lean:34–68` | Packages actual finite basis carriers, instances, and a Kraus map. `ofKraus` retains the exact channel and index types. It does not return a record of chosen scalar information values. |
| `KrausChannel`, `map`, `linearMap`, `output`; `Nonadditivity/Channels.lean:29–82` | Matrices `A_k` with `sum A_k* A_k=I`; full-matrix map `X -> sum A_k X A_k*`. Additivity, complex linearity, positivity, and trace preservation are proved. The map acts on unnormalized and non-Hermitian matrices too, as the source explicitly requires. `output` restricts it to density matrices and proves positivity and normalization. |
| `tensor`, `amplify`; `Nonadditivity/Channels.lean:280–316` | Tensor Kraus matrices are Kronecker products, on product input and output indices. Arbitrary finite identity-channel amplification preserves positive semidefiniteness, establishing actual complete positivity. `tensor_map` checks product inputs, but `tensor` is defined on **all** joint matrices, so entangled inputs are not excluded. |
| `DensityMatrix`, `weights`, `vonNeumann`, `shannon`; `Nonadditivity/Entropy.lean:32–33,142–164` | Positive semidefinite trace-one complex matrices; real Hermitian eigenvalues; entropy `-sum lambda ln lambda`. Eigenvalues are proved nonnegative and sum to one. Zero eigenvalues contribute zero because the product contains their zero weight. The spectral formula is the usual von Neumann entropy in nats. |
| `DensityMatrix.mixture`; `Nonadditivity/StateEnsembles.lean:32–47` | Matrix convex combination with proof that it is a density matrix, including zero-weight terms. |
| `StateEnsembles.Ensemble`, `average`, `information`, `quantity`; `Nonadditivity/StateEnsembles.lean:90–109` | All finite probability ensembles in the specified output set; entropy of the average minus average entropy; real supremum of their information values. No fixed ensemble length or restricted product-state family occurs. |
| `outputs`, `holevo`; `Nonadditivity/QuantumHolevo.lean:27–38` | Output set is the range of the actual channel on all density matrices. Holevo is the preceding supremum. Output-state ensembles are equivalent to input-state ensembles here: each finite collection of range elements has preimages, and applying the channel to their mixture gives the output mixture by linearity. |
| `holevoBits`; `Nonadditivity/HolevoBits.lean:24–35` | Divides the natural-log Holevo quantity by the positive constant `ln 2`. The gap conversion and upper/lower conversion lemmas at lines 46–63 preserve the displayed constants. |
| `FiniteQuantumChannel.chi`, `chiTwo`, `gap`; `Nonadditivity/ActualConsequences.lean:70–74` | Actual Holevo bits, actual Holevo bits of `T.channel.tensor T.channel`, and their difference `chiTwo - 2 chi`. No regularized capacity is substituted. |

The supremum is mathematically meaningful on the target carrier: the input space is nonempty, so the maximally mixed input supplies an output (`QuantumHolevo.lean:34–35`); singleton ensembles give information zero (`StateEnsembles.lean:111–128`); information is bounded above by logarithmic output dimension (`StateEnsembles.lean:141–166`). Thus the use of real `sSup` is not relying on an empty or unbounded-set convention. The totalized definitions of logarithm or division outside the source domain likewise do not weaken this theorem: all `K`, `n-1`, and logarithm arguments in its bounds are positive under its two stated premises.

## 5. The constructed witness and choice

The proof at `HaarPrescribedBound.lean:75–96` first obtains one sample `omega` from `exists_explicit_channel`, defines its unitary family `U`, and defines a single `T` by `FiniteQuantumChannel.ofKraus (Conversion.converted (BlockConstruction.blockChannel U n))`. Its returned tuple at line 93 contains the dimensions, positivity, lower single-use bound, upper single-use bound, and two-use bound of this very `T`; the gap is then algebraically deduced. This is the required common witness.

| Witness construction definition | Body inspected and source meaning |
| --- | --- |
| `HaarModel.LocalUnitary`, `Sample`, `sampleUnitary`; `Nonadditivity/HaarModel.lean:29–30,57–62,80–87` | Actual unitary matrices on `Fin (N+1)` and a finite tuple of them. The supplied sample parameter is `localDimension-1`, giving the intended `N`. The identity branch for `j >= n` extends a finite tuple to a natural-index family; tensor recursion consumes only `j < n`. It is not a replacement for missing unitaries in the source block. |
| `StructuredHaarModel.localRepresentation`, `derivedUnitary`; `Nonadditivity/StructuredHaarModel.lean:95–109` | Evaluates short free-group words in the sampled unitary pairs. Every result is an actual unitary of the intended local dimension. The theorem needs existence of suitable tuples, not uniqueness or independent Haar distribution of all derived `K` words. |
| `InitialNetReduction.shortEmbedding`, `shortWord`; `Nonadditivity/InitialNetReduction.lean:545–561`; `FreeEmbedding.logarithmicEmbedding`; `Nonadditivity/FreeEmbedding.lean:402–446` | Renames generators of an injective finite free-group embedding and evaluates its generator images. The implementation chooses finite edge indices for a covering construction and proves injectivity and the logarithmic word-length estimate. This is an allowed choice of an embedding, not a purported uniquely determined source object. |
| `TensorChainIndex`, its finite/decidable instances, `emptyTensorChannel`, `tensorChain`; `Nonadditivity/TensorPowers.lean:25–44,152–178` | Iterated product basis with a one-dimensional empty tensor, recursively tensoring factors indexed `0` through `n-1`. The empty channel has one Kraus coefficient equal to one, not zero. Cardinality is `card(i)^n` (`BlockConstruction.lean:27–43`). |
| `randomUnitary`, `uniformUnitary`, `complementary`; `Nonadditivity/Channels.lean:154–204` | Kraus matrices `sqrt(p_k) U_k`, uniform weights `1/K`, then exchange output/environment indices. The complement entries are the required branch overlaps, agreeing with `eq:gram` and its local specialization. |
| `BlockBell.blockComplementary`; `Nonadditivity/BlockBell.lean:145–150` | Tensor product of those local complementary channels; this is `F_n`, not a channel on a restricted input-state carrier. |
| `blockOutputEquiv`, `blockChannel`; `Nonadditivity/BlockConstruction.lean:115–132`; `KrausChannel.reindex`; `Nonadditivity/ChannelReindex.lean:68–85` | Relabel output basis to `ZMod(K^n)`. The equivalence is selected from equal finite cardinalities; `reindex` substitutes inverse basis labels in the actual Kraus matrices. Basis choice is arbitrary and permitted for an existential channel theorem. |
| `selector`, `controlled`, `outputUnitary`, `covariantExtension`; `Nonadditivity/ChannelExtensions.lean:27–29,76–93,103–127` | Select a classical input block, apply its channel, and sum outputs; its Kraus formula includes the selector. The codomain keeps no label. Output unitary conjugation acts by left multiplying every Kraus matrix. All required completeness fields are proved using the constituent completeness and unitary identities. |
| `conjugate`, `switch`; `Nonadditivity/Channels.lean:319–326`; `Nonadditivity/SwitchChannel.lean:29–40` | Entrywise complex conjugation of the Kraus matrices, selected with the original by a discarded Boolean input. This matches source lines 854–867. The `if` here implements the two genuine physical branches rather than a default substitute. |
| `Weyl.phase`, `shift`, `unitaryMatrix`, `family`; `Nonadditivity/Weyl.lean:30–34,62–64,155–156` | Standard character phase and cyclic shift on `ZMod d`, indexed by all `d^2` label pairs. The implementation writes phase before shift, whereas the source writes shift before phase; these differ by a scalar phase (and the cyclic shift parameter can be renamed), which cancels in conjugation. For this existential construction the full family gives the same Weyl orbit. The exact normalized twirl is proved at lines 134–153. |
| `weylExtension`, `Conversion.converted`; `Nonadditivity/ChannelEntropy.lean:117–120`; `Nonadditivity/Conversion.lean:26–31,56–62` | Apply the Weyl controlled extension after the conjugate switch. Input indices are `(ZMod L x ZMod L) x (Bool x blockInput)`; output is `ZMod L`. Hence `2 L^2 N^n = 2 N^n K^(2n)` and `L=K^n`. The cardinality proof is `StructuredHaarConsequences.lean:108–114`. |

The internal conditional helper `exists_explicit_channel` (`StructuredHaarConsequences.lean:117–142`) takes a Haar expectation premise. The actual target supplies it with the **proved** theorem `explicitHaarExpectation hK hn` (`HaarPrescribedBound.lean:49–61,76–77`). That helper premise is not smuggled into the target as a structure or an instance. I inspected the literal expectation predicate at `StructuredHaarConsequences.lean:41–52`; it is a norm-integral assertion about actual sampled polynomial evaluations, not a bundle of the desired channel conclusions. This report does not separately re-prove the entire random-matrix/path-counting argument behind that theorem.

The supplementary source lower bound is applied to this same `U` and same converted channel at `HaarPrescribedBound.lean:83–85`. Its implementation is `PositiveHolevo.exists_block_entropy_le`, `block_converted_holevo_lower`, and `block_converted_holevoBits_lower` at `Nonadditivity/PositiveHolevo.lean:225–298`: product input states supply the block bound, the exact conversion identity supplies the Holevo lower bound, and division by `ln 2` gives `2n/K` in bits. Neither this estimate nor positivity is assumed.

The later `prescribedFamily` at `Nonadditivity/HaarPrescribedConsequences.lean:21–48` uses `Classical.choose` on this proved existential at index `max(n0(K),n)`. Its specification and supplementary lower-bound lemma both use `Classical.choose_spec` of the same existence theorem, so they retain the same selected channel. No unique or canonical channel is asserted. For `n >= n0(K)`, `max` reduces to `n`; smaller indices merely give a total extension by an already existing channel at the threshold. This audit does not assert the theorem's original dimension formula at those smaller indices. The existential statement and its asymptotic uses permit this choice; demanding uniqueness here would change the source problem.

## 6. Definition and closure conclusions

For the source-facing quantities and carriers reached from the target type:

```text
BODY_MATCH: OK on the source domain
PUBLIC_CARRIER: OK (full finite matrix channels, all density inputs)
WELL_DEFINEDNESS: N/A_LITERAL; finite-state supremum domain checked above
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A for existential channel and basis/embedding selection
DEFINITION_VERDICT: PASS for the reviewed endpoint semantics
```

The source formula for the channel construction is implemented through actual Kraus operations rather than a numerical surrogate. The scalar error is exactly `2 log2(kappa)` for the single-use bound and `4 log2(kappa)` for the gap. No positive-gap assumption, asymptotic threshold enlargement, unspecified multiplicative constant, alternate witness, or channel-information certificate occurs in the target type.

This is a statement and semantic-carrier review, not an independent reconstruction of every imported proof or every definition used by those proofs. The endpoint's numerical quantities, finite channel/state/ensemble carriers, nested proof fields, and witness construction were directly inspected. The enormous analytic proof dependency graph remains subject to the separate build, allowed-axiom, comparator, and application-probe evidence. I make no new claim of having run those checks here.

The `prescribed` entry in the [audit manifest](../verification/statement-audit.json) lists the repository files substantively read for this review, including the manuscript, exact challenge, actual theorem, exported metadata, semantic definitions, and the supplementary lower-bound and choice consumers.
