<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# Independent AI source audit: all positive Weyl powers (D)

Review date: 2026-10-06. Reviewer: a fresh independent AI review agent, separate from the declaration author; a second independent read-only AI agent crosschecked minimum/infimum, channel carriers, the measured construction, and entangled-input coverage. This is **not machine certification of English–Lean equivalence** and not independent human certification.

**Verdict: QUALIFIED.** The exported theorem matches its challenge and correctly states the Holevo identity for every positive self-power of a finite Kraus channel, with arbitrary joint inputs and the actual measured Weyl extension. There are no EXCESS binders. The strict source-definition bridge from the manuscript's attained minimum to Lean's entropy infimum is not supplied. The literal universal statement over abstract CPTP linear maps also lacks a formal converse Kraus-representation bridge. The broader distinct-channel identity is outside this export. These are formal coverage limits, not counterexamples to the proved numerical equality. Current exact-application and axiom checks are documented in the separate [verification record](../verification/statement-audit-20261006/checks.json).

The selected `lean-statement-audit` guidance at revision `601fe274276d93052ef645f0ff2c1a355e8e5b16` was adapted to the release rather than imposing a new freeze/provider workflow. The audit proceeded from raw source to exact type to definition bodies and proof applications. No Lean build or proof edit was performed by this reviewer. Source equality is not inferred merely from matching pretty-printed types or file hashes.

## Source reconstruction before implementation

The release manuscript is `paper/nonadditivity.tex`, the path in `metadata/results.json`, SHA-256 `3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98`.

- `paper/nonadditivity.tex:88–103`, labels `eq:def-smin`, `eq:def-chi`: channels are CPTP complex linear maps on full finite matrix algebras; S uses log base two; Smin is written as a **minimum** over all density matrices, and the following sentence asserts reduction to pure inputs. χ is the supremum of the entropy difference over finite input ensembles.
- `paper/nonadditivity.tex:893–904`, label `eq:twirl`: for a positive output dimension L, shifts/phases on the basis indexed by Z/L give L² Weyl labels, V_(p,q)=X^p Z^q, with uniform average `(Tr Y) I/L` on **every matrix Y**.
- `paper/nonadditivity.tex:905–916`, label `eq:extension`: for any channel Φ:M_d→M_L, the extension has input M_(L²)⊗M_d and output M_L. It measures the label, applies Φ to its unnormalized diagonal block, conjugates by the selected Weyl unitary, sums, and discards the label. Coherent off-diagonal blocks do not become an output flag.
- `paper/nonadditivity.tex:918–932`, label `eq:chi-extension`: **for the same arbitrary channel Φ and every integer m≥1**, independent labels in each factor give Smin(Φ̃^⊗m)=Smin(Φ^⊗m) and χ(Φ̃^⊗m)=m log₂L−Smin(Φ^⊗m). Inputs to Φ^⊗m are arbitrary joint states; no product-state restriction or minimizing-state premise is present. The proof describes fixing a minimizing joint input and uniformly varying the labels.
- `paper/nonadditivity.tex:121–131,931–932`, scope: additional distinct-channel statement. For arbitrary Φ and Ψ, potentially with different input/output dimensions, their Weyl extensions satisfy χ(Φ̃⊗Ψ̃)−χ(Φ̃)−χ(Ψ̃)=Smin(Φ)+Smin(Ψ)−Smin(Φ⊗Ψ). This is a separate broader generality claim, not identical to the self-power formula.

Thus the source quantifier order is positive finite dimensions, arbitrary Φ, then every positive use count m. The entire statement refers to that same Φ. There is no assumed twirl estimate, entropy-concavity gate, product input, optimizer, or already constructed orbit ensemble among its premises.

The target is `Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits`, `Nonadditivity/WeylPowersEntropy.lean:85–91`; result ID `weyl-all-uses`. Its source-file SHA-256 is `2ee550b865e89cecb11986bbfbecb9971424a06a3f93bc5769af08229d848866`. Decoding its kernel-type data from `metadata/declarations.json` and recomputing the checksum gave `cf60254869fd259c7e153d06e0f31b72f872eb3018613dd01c8868fad35e6e06` (8365 bytes), matching the record. Its static type agrees with `ComparatorChallenges/D_WeylAllUses.lean:13–21`. The metadata/source declaration was inspected after the source reconstruction.

## Every binder and recursive bundle

Universe parameters `u_1,u_2` are type levels, not mathematical hypotheses. The exact elaborated declaration has ten term binders in this order. SOURCE includes mathematical objects/parameters in the source; finite-index implementation data are TYPING.

| Order | Binder | Kind | Bin | Source/scope |
|---|---|---|---|---|
| 1 | `ι : Type u_1` | implicit | TYPING | basis of the finite input matrix algebra, 88–90,907 |
| 2 | `κ : Type u_2` | implicit | TYPING | finite Kraus/environment index for the represented channel |
| 3 | `[Fintype ι]` | instance | TYPING | finite input dimension, 88–90 |
| 4 | `[DecidableEq ι]` | instance | TYPING | equality of matrix indices |
| 5 | `[Nonempty ι]` | instance | TYPING | positive input dimension; nonempty density-state domain |
| 6 | `[Fintype κ]` | instance | TYPING | finite Kraus sum |
| 7 | `d : ℕ` | implicit | SOURCE | source's output dimension L, 893–916 |
| 8 | `[NeZero d]` | instance | TYPING | positive finite output dimension; `d≠0` for natural d |
| 9 | `T : KrausChannel ι (ZMod d) κ` | explicit | SOURCE | arbitrary channel in this concrete representation, 887–927 |
| 10 | `n : ℕ` | explicit | SOURCE | source's arbitrary m≥1 reindexed as m=n+1, 926 |

Top-level counts: **SOURCE 3, STANDING 0, TYPING 7, RULED 0, EXCESS 0; total 10.** The standard instances `Fintype` (enumeration/completeness), `DecidableEq`, `Nonempty`, and `NeZero` have only the advertised typing content. `ZMod d` supplies its own finite/decidable/nonempty output instances. Neither an additional `Nonempty κ` nor a second channel is a hidden binder.

The only project-owned input bundle is T:

| Expanded leaf replacing T | Bin | Definition/source correspondence |
|---|---|---|
| `T.kraus : κ → Matrix (ZMod d) ι ℂ` | SOURCE | finite complex matrices representing the channel, `Channels.lean:31` |
| `T.complete : ∑k (T.kraus k)* T.kraus k = 1` | SOURCE | trace-preserving channel premise, source 88–90; `Channels.lean:32` |

Fully expanded input-leaf counts: **SOURCE 4, STANDING 0, TYPING 7, RULED 0, EXCESS 0; total 11** (T replaced by two leaves). Kraus positivity is proved rather than an additional field. These data represent genuine source channels: `Channels.lean:52–75` gives complex linearity and trace preservation for all matrices, and 308–316 proves positivity under arbitrary finite ancilla amplification. However, no converse theorem constructing a finite Kraus realization from an independently specified abstract CPTP map was found. The formal carrier is all supplied finite Kraus realizations, not literally a type of all abstract CPTP linear maps.

The exact conclusion is

```lean
(positiveTensorPower T.weylExtension n).holevoBits =
  ((n + 1 : ℕ) : ℝ) * Scalar.log2 d -
    (positiveTensorPower T n).minimumEntropy / Real.log 2
```

Both sides use the same T and n. No inequality replaces the equality. No positive length is excluded: n=0 is one use, n=1 is two uses, and m≥1 is obtained with n=m−1. The result neither claims a zero-use entropy formula nor quantifies only over powers of two.

## Semantic definitions, with source scope

| Lean definition/body and location | Source scope | Assessment |
|---|---|---|
| `KrausChannel`, `.map`, `.output`, `Channels.lean:29–40,78–82` | 88–92, full-algebra CPTP channel | sum AₖXAₖ* for every matrix; PSD/trace-one output; forward CPTP semantics proved |
| `DensityMatrix`, `weights`, `vonNeumann`, `Entropy.lean:142–164`; `shannon`, 32–33 | 93–103, all density matrices and entropy | matrix/PSD/trace-one fields; spectral `−Σλ ln λ`; zero-log contribution is zero |
| `outputs`, `minimumEntropy`, `holevo`, `QuantumHolevo.lean:27–32` | `eq:def-smin`, `eq:def-chi` | output range of all density inputs; entropy infimum and finite-ensemble supremum |
| `Ensemble`, `average`, `information`, `quantity`, `StateEnsembles.lean:90–109` | 97–99, Holevo expression | six fields: size, weight, nonnegative weights, weights sum one, states, membership in actual outputs; formula is the source entropy difference |
| `minimumEntropy`, `StateEnsembles.lean:105–106` | 96 and 929–931, attained minimum | `sInf (vonNeumann '' outputs)`; no minimizer or attainment characterization supplied; strict source-definition closure incomplete |
| `holevoBits`, `HolevoBits.lean:24`; `Scalar.log2`, `Scalar.lean:26` | 101,926, base-two units | divide natural-log entropy/Holevo by positive ln 2; no extra factor per use |
| `selector`, `ChannelExtensions.lean:28–29` | 909–914, measured blocks | rectangular basis selector; extracts the unnormalized diagonal block |
| `controlled`, `controlled_map`, `ChannelExtensions.lean:76–91` | 905–916, measured/discarded register | Kraus `(T_z).kraus k * selector z`; full map is Σ_z T_z(selector_z X selector_z*) on every matrix |
| `outputUnitary`, `outputUnitary_map`, `ChannelExtensions.lean:103–120` | 909–911, output conjugation | U Aₖ Kraus matrices, map U T(X) U* |
| `covariantExtension`, `ChannelExtensions.lean:125–127` | `eq:extension` | controlled family of output conjugations; label absent from output type |
| `weylExtension`, `ChannelEntropy.lean:118–120` | 899,905–916 | input `(ZMod d×ZMod d)×ι`, output `ZMod d`; exactly d² labels |
| `phase`, `shift`, `unitaryMatrix`, `Weyl.lean:30–34,62–64` | 893–900, Weyl convention | uses phase t times a permutation shift s; convention differs by label sign/order and a scalar phase from source X^p Z^q |
| `PositiveTensorIndex`, its instances/cardinality, `RegularizedHolevo.lean:29–65` | 918–926, m-fold spaces | recursive product of n+1 basis indices; cardinality `(card ι)^(n+1)` |
| `tensor`, `Channels.lean:280–294`; `positiveTensorPower`, `RegularizedHolevo.lean:68–74` | 918–926, actual channel tensors | Kronecker Kraus matrices on full joint matrix algebra; recursion tensors T rather than inventing unrelated channels |
| `positivePairEquiv`, `positiveUnitaryPower`, `WeylPowersIndex.lean:21–25,38–43` | 918–919, independent local labels | reorders `(label,input)^m` to `label^m×input^m`; tensor product of independent unitaries |
| `Basis`, `Label`, `tensorFamily`, `uniformWeight`, `orbitIndex`, `orbitEnsemble`, `WeylPowersTwirl.lean:17–23,109–155` | 918–930, uniform joint orbit | all local label tuples, total d^(2m) labels, positive normalized uniform weights, actual unitary-conjugated joint output states |
| `inputBlock`, `inputWeight`, `conditionalInput`, `ChannelEntropy.lean:29–60` | 913–914, conditional measured inputs | block and its trace; normalized conditional states used only to prove the exact output mixture |
| `normalizePositive`, `ConditionalStates.lean:33–51` | zero-weight branches of the conditional argument | chooses maximally mixed at trace zero, but proves `(Tr A) normalized(A)=A` including zero; exported extension remains the literal unnormalized block sum |

The only internal ensemble witness schema used in the Holevo definition expands as follows. These are defining constraints inside a supremum, not additional universal inputs to D.

| Recursive ensemble leaf | Bin | Source/Lean scope |
|---|---|---|
| `size` | TYPING | finite ensemble indexing; source 97; `StateEnsembles.lean:91` |
| `weight` | SOURCE | probabilities; source 97–99; 92 |
| `weight_nonneg` | SOURCE | nonnegative probabilities; source 97–99; 93 |
| `weight_sum` | SOURCE | total probability one; source 97–99; 94 |
| `state(i).matrix` | SOURCE | arbitrary output state matrix; source 97–101; `Entropy.lean:143` |
| `state(i).positive` | SOURCE | positive-semidefinite state; source 97–101; 144 |
| `state(i).normalized` | SOURCE | trace-one state; source 97–101; 145 |
| `state_mem(i)` | SOURCE | in the actual output range; source 97–99; `StateEnsembles.lean:96` |

Internal schema counts: **SOURCE 7, STANDING 0, TYPING 1, RULED 0, EXCESS 0; total 8.** The separate density-matrix input carrier has the same three state leaves without the membership field. No bundle hides an optimizer or product-state condition.

The recursive density-state fields are exactly `matrix`, `positive`, `normalized`; the ensemble fields above range over arbitrary such states and finite weights. No field asserts separability, a product factorization, minimum attainment, or a Holevo estimate. `orbitEnsemble`'s membership proof is constructed by `labelledState q ρ` in the target proof; it is not a target input assumption. Finitely selecting indices/preimages is legitimate and introduces no uniqueness requirement.

For `weylExtension` and actual tensor powers, **BODY_MATCH OK up to the explicit Weyl label convention; PUBLIC_CARRIER OK for finite Kraus channels and positive dimensions; WELL_DEFINEDNESS OK; CHARACTERIZATION OK (full matrix/Kraus identities); CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS for that stated scope.** Register selectors contain ordinary matrix-entry conditionals, not fallback channel behavior. Zero-probability normalization is an auxiliary representation of a zero term, with the full weighted identity proved, not missing mathematics hidden by default output semantics.

For `minimumEntropy` **as the literal attained source minimum**, the strict assessment is **BODY_MATCH FAIL (infimum replaces minimum without an attainment bridge); PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK for the infimum; CHARACTERIZATION FAIL for the attained-minimum property; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT FAIL for complete source-definition closure.** For the explicitly documented infimum formulation, its body is correct: the output set is nonempty (`QuantumHolevo.lean:34–35`) and entropy is bounded below (`StateEnsembles.lean:130–139`). This qualification does not invalidate the infimum identity, and does not mean an optimizer cannot exist mathematically. It means optimizer existence and pure-input attainment have not been formally connected to this definition.

For the universal abstract channel carrier, **PUBLIC_CARRIER is complete for supplied Kraus realizations, but the converse representation bridge to the paper's abstract CPTP definition remains unverified/not located.** Existence of that standard mathematical correspondence should not be mistaken for a theorem already proved in this repository.

## Measured construction, dimensions, and entangled inputs

The extension maps the full input matrix to a sum of conjugated block images (`controlled_map`, `outputUnitary_map`), so it measures and discards the classical label. Its dimension is d²·card ι in and d out. For m=n+1 uses, these become `(d²·card ι)^m` and `d^m`; the regrouped label register has d^(2m) values. The coefficient `m log₂ d` follows from the actual output dimension `d^m`, using `positiveTensorIndex_card` and `Real.log_pow` in `WeylPowersEntropy.lean:59`. No output-label entropy term is included.

Source and Lean Weyl labels are not literally identical. `Weyl.shifted_conjugation_apply` (66–78) gives A(i+s,j+s); the paper's X^p gives A(i−p,j−p). Together with Lean's phase-first product, the source conjugation is recovered by p=−s, q=t, with any scalar commutation phase canceling. This is the same projective Weyl family under a bijection of the measured labels. Holevo information is invariant under such input reindexing, and `ChannelReindex.lean:68–109`, `HolevoTensorSuperadditivity.lean:215–241`, and `WeylPowersChannels` supply the general invariance machinery. No named theorem explicitly equating the paper's X^p Z^q convention to this implementation was identified, so exact formula identity with unchanged label names is not claimed.

Entangled inputs are genuinely covered at three places: `outputs` ranges over **all** `DensityMatrix (PositiveTensorIndex ι n)`; `positiveTensorPower_covariant` (`WeylPowersChannels.lean:61–72`) identifies reindexed Kraus channels on all matrices, not just product states; and `WeylPowersTwirl.uniform_average_eq` (120–137) applies to every joint matrix A. The local twirl factors over independent labels, but the twirled A need not factor. `tensorWeylExtension_holevo` even accepts an arbitrary joint channel with output `PositiveTensorIndex (ZMod d) n`, not necessarily a tensor channel.

## Actual proof consumption

The exact bits export (`WeylPowersEntropy.lean:89–91`) rewrites `holevoBits` and **applies** `positiveTensorPower_weylExtension_holevo`, then unfolds log₂ and performs ring algebra. The natural-log theorem (78–82) applies `positiveTensorPower_covariant_holevo` and `tensorWeylExtension_holevo`.

`positiveTensorPower_covariant_holevo` (`WeylPowersChannels.lean:74–79`) consumes the actual Kraus-channel equality (61–72) plus invariance under input/environment reindexing. It does not assume a covariance theorem. The equality is proved by induction over the actual Kronecker Kraus formulas (23–57).

`tensorWeylExtension_holevo` (`WeylPowersEntropy.lean:51–74`) proves both directions. The upper direction consumes the full measured-output entropy lower bound (`ChannelEntropy.lean:107–115`), which follows from the exact conditional output mixture and entropy concavity (67–94). The lower direction takes **every input ρ**, constructs the complete orbit using `labelledState`, applies the product-orbit entropy information bound, and passes to the infimum with `le_csInf`. Thus the optimizer is neither assumed nor constructed. `WeylPowersTwirl.lean:143–197` constructs the actual finite ensemble and proves the maximally mixed average and the exact equal-entropy orbit properties from the arbitrary-matrix twirl.

The nearby general `covariantExtension_minimumEntropy` (`WeylPowersEntropy.lean:23–38`) proves infimum preservation for a measured unitary extension. It is a separate result, not a conjunct in D. Applying it to a regrouped power gives the ingredients for the source's accompanying entropy identity, but D alone does not export that second equation or an attaining input.

## Findings and limits

1. **D1 — All positive self-powers and arbitrary entangled inputs: supported.** Correct n+1 indexing, genuine Kronecker channel powers, full input-state carrier, and actual local measured registers.
2. **D2 — Minimum versus infimum: incomplete formal source bridge.** Source 96,102–103,929–931 speaks of a minimum/pure optimizer; Lean's definition and proof establish only the entropy infimum and its numerical Holevo identity. A search of `Nonadditivity/*.lean` found no attainment/pure-input-minimum theorem. `EntropyContinuity.exists_vonNeumann_opNorm_modulus` (`EntropyContinuity.lean:101–103`) is continuity evidence, not an attainment theorem. This prevents an unqualified source-definition PASS.
3. **D3 — Abstract CPTP generality: representation qualification.** Forward Kraus→CPTP semantics are concrete and proved; the reverse finite Kraus representation theorem was not found. The exported theorem covers every supplied finite Kraus channel and all positive dimensions, including d=1.
4. **D4 — Different-channel identity: outside this export.** D has one channel T and one output dimension d. The paper additionally asserts an identity for two distinct channels, possibly of different output dimensions. General measured-channel tensor regrouping (`WeylPowersControl.lean:78–86`) does not itself prove that full entropy/Holevo identity. `metadata/results.json` already records this broader generalization as not formalized.
5. **D5 — Weyl convention: equivalent family, not literal label match.** Sign/order differences are harmless to the numerical identity under a label permutation and scalar phase, but that source-convention bridge is not a named formal result in the inspected closure.
6. **D6 — Metadata wording needs care.** `weyl-all-uses` correctly notes the entropy endpoint is an infimum, but its `exact_endpoint` label must be read with D2–D3. Its note says it extends a one-use displayed equality; the current manuscript's `eq:chi-extension` already explicitly quantifies over all m≥1. The separate `background-generality` entry records pure-input attainment and distinct-channel scope limits.

The final status is therefore a qualified source audit of a substantive proved infimum identity, with no hidden premise failure. The mathematical facts needed to close the minimum/representation bridges are standard; this report does not count them as existing formal certificates. Separate current kernel acceptance and axiom closure are necessary and do not, by themselves, resolve these source-semantic qualifications.
