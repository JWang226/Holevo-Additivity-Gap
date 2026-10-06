<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# Independent AI source audit: simultaneous separation (C)

Review date: 2026-10-06. Reviewer: a fresh independent AI review agent, separate from the declaration author; a second independent read-only AI agent crosschecked the shared channel/entropy definitions. This is a source-to-declaration review, **not machine certification of English–Lean equivalence** and not independent human certification.

**Verdict: PASS for the strengthened existential endpoint and the inspected semantic definitions/direct proof composition, subject to the separately recorded current kernel/axiom checks.** It does not certify every assertion in `cor:capacity` or `cor:separation`, or re-audit every analytic proof underlying the deterministic construction. No EXCESS input was found. The alternative construction, stronger quantifiers, common witness, and positivity are substantive, not assumed.

The selected `lean-statement-audit` guidance (revision `601fe274276d93052ef645f0ff2c1a355e8e5b16`) was adapted to this existing release: source first; five-bin binders; expanded bundles; definition bodies; actual composition. No draft/freeze/provider workflow was imposed, and selecting a witness from a proved existential is legitimate here. No Lean build or proof edit was performed by this reviewer. Exact applications and axiom probes are documented in the separate [current verification record](../verification/statement-audit-20261006/checks.json).

## Identity and independently reconstructed source

The manuscript is `paper/nonadditivity.tex`, also the path named by `metadata/results.json`; its SHA-256 is `3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98`. This source was read before the target, challenge, implementation, or result descriptions.

- `paper/nonadditivity.tex:88–109`, scope: standing definitions. A finite channel is a completely positive trace-preserving complex linear map on full matrix algebras. Entropy and Holevo information use base-two logarithms. Holevo information is the supremum of the average-output entropy minus the average output entropy over finite ensembles. Unassisted classical capacity equals the supremum/limit of normalized Holevo information over every positive tensor power.
- `paper/nonadditivity.tex:325–350`, labels `cor:capacity`, `eq:capacity-gap`, `eq:ratio`. The earlier parameterized assertions fix an admissible K and choose a family for all sufficiently large n. The final existence assertion is `∀ A>0, ∀ R>0, ∃ T, χ(T)>0 ∧ C(T)−χ(T)≥A ∧ χ(T⊗T)/(2χ(T))≥R`. A single T serves both bounds; no upper bound on χ occurs in that sentence.
- `paper/nonadditivity.tex:390–406`, labels `cor:separation`, `eq:small-large`, `eq:vanishing-diverging`. The finite existence assertion is `∀ ε>0, ∀ Q>0, ∃ T, χ(T)≤ε ∧ χ(T⊗T)/2≥Q`; the sequence simultaneously has χ→0 and half of the two-use χ→∞, hence C→∞. Here Q denotes the source's R to avoid confusing it with a ratio threshold. Its sequence of witnesses and its two limits concern the same channels.
- `paper/nonadditivity.tex:356–368`, scope: positivity explanation. Zero Holevo information would force constant output even on joint inputs; a positive two-use bound therefore gives χ>0. This proof argument is not an allowable extra theorem premise.
- `paper/nonadditivity.tex:409–423`, scope: the separation proof. The family uses `ceil(K/sqrt(ln K))`, error `1/K`, and an eventually chosen sufficiently large K. Its two limits justify imposing finitely many eventual bounds on one witness.

C combines and strengthens the two existence conclusions. The source's own small/large conclusion plus positivity permits simultaneous small χ, arbitrarily large gain, and arbitrarily large ratio by choosing the two-use threshold sufficiently large. Thus this strengthening is source-supported; it is not a literal transcription of either corollary alone. It does not assert the prescribed dimensions, fixed-K liminf, explicit gain constants, or the entire displayed sequence theorem.

The exact target is `Nonadditivity.OperationalConsequences.exists_small_chi_large_capacity_gain_and_two_use_ratio` in `Nonadditivity/OperationalConsequences.lean:69–78`. Its source-file SHA-256 is `df80e2ddf60ccd6fde21cd77923aeb7ab4e63c57cfaa5718dc973a4e8ba2d2a9`. Result ID: `simultaneous-separation`. The target type in `metadata/declarations.json` was decoded and its recorded SHA-256 recomputed: `f8a97c886658799d68e18f7fd0be11cc3b87807b11319fa0a3b31b504f976bb8` (1938 decoded bytes). The static declaration matches `ComparatorChallenges/C_SmallInformationSeparation.lean:13–17`; the challenge's intentional sorry is not the solution proof.

## Exact binders and witness scope

The fully elaborated type has these four input binders and no universe parameters or instance binders. SOURCE includes source mathematical parameters; bins are exclusive.

| Order | Binder | Kind | Bin | Source/scope and assessment |
|---|---|---|---|---|
| 1 | `ε : ℝ` | implicit | SOURCE | `cor:separation`, 392; precision threshold fixed before T |
| 2 | `hε : 0 < ε` | explicit proof | SOURCE | 392; source positivity premise |
| 3 | `A : ℝ` | explicit | SOURCE | `cor:capacity`, 345–349; gain threshold fixed before T |
| 4 | `R : ℝ` | explicit | SOURCE | `cor:capacity`, 345–349; ratio threshold fixed before T |

Input counts: **SOURCE 4, STANDING 0, TYPING 0, RULED 0, EXCESS 0; total 4.** A and R range over all reals; their source positivity hypotheses are removed, making the result stronger. No `hA`/`hR` or analytic/construction gate is hidden. No ruling is used.

The conclusion is exactly `∃ T, 0<T.chi ∧ T.chi≤ε ∧ A≤T.classicalCapacity−T.chi ∧ R≤T.twoUseRatio`. All four conjuncts are under this one existential; the dimensions may depend on ε,A,R. T does not precede the thresholds. The conjunction supplies denominator positivity, rather than relying on Lean's totalized division at zero.

`FiniteQuantumChannel` is a witness carrier, not an input assumption bundle. Every leaf of its recursive structure is listed below; the counts are separate from the input counts.

| Witness leaf | Bin | Source/scope |
|---|---|---|
| `Input : Type` | TYPING | input finite matrix algebra, 88–90 |
| `Output : Type` | TYPING | output finite matrix algebra, 88–90 |
| `Environment : Type` | TYPING | finite Kraus realization used to exhibit a channel |
| `inputFinite : Fintype Input` | TYPING | finite input dimension |
| `inputDecidable : DecidableEq Input` | TYPING | matrix-index equality |
| `inputNonempty : Nonempty Input` | TYPING | positive input dimension/state space |
| `outputFinite : Fintype Output` | TYPING | finite output dimension |
| `outputDecidable : DecidableEq Output` | TYPING | matrix-index equality |
| `outputNonempty : Nonempty Output` | TYPING | positive output dimension/state space |
| `environmentFinite : Fintype Environment` | TYPING | finite sum of Kraus operators |
| `channel.kraus : Environment → Matrix Output Input ℂ` | SOURCE | actual complex channel data |
| `channel.complete : ∑k Aₖ* Aₖ = 1` | SOURCE | trace preservation; CP follows from Kraus form |

Witness-leaf counts: **SOURCE 2, STANDING 0, TYPING 10, RULED 0, EXCESS 0; total 12.** Definitions: `ActualConsequences.lean:34–45`; `Channels.lean:29–32`. No field stores χ, C, the desired inequalities, an analytic hypothesis, or a preselected result. Complete positivity for every finite ancilla is proved in `Channels.lean:308–316`; complex linearity and trace preservation on all matrices are proved at 52–75. For this existence theorem a finite Kraus construction suffices to exhibit a source CPTP channel; a converse representation theorem for arbitrary abstract CPTP maps is unnecessary.

## Semantic definition closure

| Definition/body and Lean location | Source location and scope | Audit |
|---|---|---|
| `DensityMatrix.matrix`, `.positive`, `.normalized`, `Entropy.lean:142–145` | 93–103, states | arbitrary complex positive-semidefinite matrix of trace one; no pure/product-input restriction |
| `weights`, `vonNeumann`, `Entropy.lean:147–164`; `shannon`, 32–33 | 101, entropy | eigenvalue entropy `−Σp ln p`; zero term is zero; divide by ln 2 for bits |
| `KrausChannel.map/output`, `Channels.lean:39–40,78–82` | 88–92, full algebra channel | finite sum `Σ Aₖ X Aₖ*` on every matrix, then bundled state output |
| `outputs`, `holevo`, `QuantumHolevo.lean:27–32` | `eq:def-chi`, 97–99 | actual output range and ensemble supremum; finite output ensembles have input preimages by their range memberships |
| `Ensemble`, `average`, `information`, `quantity`, `StateEnsembles.lean:90–109` | `eq:def-chi` | `size`, `weight`, `weight_nonneg`, `weight_sum`, `state`, `state_mem`; all finite probabilities and outputs, no assumed information bound |
| `holevoBits`, `HolevoBits.lean:24`; `Scalar.log2`, `Scalar.lean:26` | 101 | both divide natural-log quantities by positive `ln 2` |
| `chi`, `chiTwo`, `gap`, `twoUseRatio`, `ActualConsequences.lean:70–76` | `eq:def-gap`, `eq:ratio`, 111–114,345–349 | χ(T), χ(T⊗T), χ₂−2χ, χ₂/(2χ); ratio is dimensionless, gain is bits per use |
| `tensor`, `Channels.lean:280–294` | 107–114, joint channel use | Kraus Kronecker product acts on the entire joint matrix algebra; all joint density matrices enter the Holevo supremum |
| `PositiveTensorIndex/positiveTensorPower`, `RegularizedHolevo.lean:29–74` | 107–108, every positive m | zero index is one use; successor tensors another T; no omitted positive length |
| `classicalCapacity`, `OperationalCodingTheorem.lean:62–63` | `eq:capacity`, 104–109 | independently defined operational capacity of T.channel |
| `POVM`, `probability`, `Code`, `success`, `error`, `OperationalConverse.lean:29–40,82–84,129–133` | 104–109, unassisted classical coding interpretation | positive effects summing to identity; arbitrary density-matrix encoders; Born probability; uniform-message average error |
| `CodeSequence`, `rate`, `VanishingError`, `HasRate`, `OperationalCapacity.lean:29–46` | 104–109 | codes at every positive block length; positive message count; bits/use; error→0; every strictly smaller target rate eventually met |
| `AchievableRate/operationalCapacity`, `OperationalCapacity.lean:140–146` | 104–109 | existence of actual code sequence, then supremum over achievable real rates; no Holevo formula in the definition |
| `normalizedPowerHolevo/regularizedHolevo`, `RegularizedHolevo.lean:85–88,129–130` | `eq:capacity` | independent normalized positive-power Holevo supremum |
| `separatingFamily`, `DeterministicConsequences.lean:43–55` | 399–423, existential sequence | choice from proved existence for K≥2; K<2 is a one-dimensional identity prefix, never used for target witness |
| `blockLength`, `separationUpper`, `separationLower`, `Asymptotics.lean:32–40` | 410–419 | manuscript ceiling and asymptotic scales; deterministic two-use bound loses a vanishing/slack term without changing C's endpoint |
| `converted`, `Conversion.lean:27`; `switch`, `SwitchChannel.lean:30–31`; measured extension, `ChannelExtensions.lean:76–127` | 854–916,939–945 | switch then Weyl extension; labels are measured and discarded; output has no transmitted flag |

The definition-internal witness schemas also expand completely. They are quantified **inside the information/capacity definitions**, not premises of C. The following schema rows are counted once, independent of message/ensemble size.

| Recursive internal leaf | Bin | Source/Lean scope |
|---|---|---|
| `Ensemble.size` | TYPING | finite ensemble cardinality; source 97; `StateEnsembles.lean:91` |
| `Ensemble.weight` | SOURCE | probabilities; source 97–99; 92 |
| `Ensemble.weight_nonneg` | SOURCE | probabilities; source 97–99; 93 |
| `Ensemble.weight_sum` | SOURCE | normalized ensemble; source 97–99; 94 |
| `Ensemble.state(i).matrix` | SOURCE | arbitrary output density state; source 97–101; `Entropy.lean:143` |
| `Ensemble.state(i).positive` | SOURCE | positive density state; source 97–101; 144 |
| `Ensemble.state(i).normalized` | SOURCE | trace-one density state; source 97–101; 145 |
| `Ensemble.state_mem(i)` | SOURCE | actual channel output; source 97–99; `StateEnsembles.lean:96` |
| `CodeSequence.messages(n)` | TYPING | finite message cardinality; coding scope 104–109; `OperationalCapacity.lean:30` |
| `CodeSequence.messages_pos(n)` | TYPING | nonempty message alphabet; same scope; 31 |
| `code(n).encode(m).matrix` | SOURCE | arbitrary joint input density matrix; coding scope 104–109; `OperationalConverse.lean:83` |
| `code(n).encode(m).positive` | SOURCE | physical input state; same scope; `Entropy.lean:144` |
| `code(n).encode(m).normalized` | SOURCE | trace-one physical input; same scope; 145 |
| `code(n).decode.effect(m)` | SOURCE | POVM receiver; coding scope 104–109; `OperationalConverse.lean:30` |
| `code(n).decode.positive(m)` | SOURCE | PSD POVM effect; same scope; 31 |
| `code(n).decode.complete` | SOURCE | effects sum to identity; same scope; 32 |
| `VanishingError` | SOURCE | reliable code-sequence condition; coding scope 104–109; `OperationalCapacity.lean:42–43` |
| `HasRate(R)` | SOURCE | achievable-rate condition; coding scope 104–109; 45–46 |

Internal schema counts: **SOURCE 15, STANDING 0, TYPING 3, RULED 0, EXCESS 0; total 18.** The manuscript names operational unassisted classical capacity rather than spelling out these code fields; this expansion uses its standard uniform-message average-error meaning and verifies the formal definition/bridge under that convention.

The remaining recursive code fields are explicit, not bundled assumptions: `CodeSequence.messages` (positive natural cardinalities), `messages_pos`, `code n`; each `Code.encode m` expands to the three density-matrix fields above; each `decode` expands to `effect`, `positive`, `complete`. `AchievableRate` additionally requires `VanishingError` and `HasRate` inside an existential. These are the defining operational conditions, **not target input premises**. The generic `Code T 0` type is harmless here because `messages_pos` excludes it from every sequence used by capacity. Nonempty achievable-rate sets and finite upper bounds are proved in `OperationalCapacity.lean:185–201`; nonempty/bounded Holevo ensembles are proved in `StateEnsembles.lean:130–184`. The real suprema are not relying on out-of-domain fallback values.

Definition assessment for the target-facing χ, χ₂, ratio, and operational C: **BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.** The spectral formulation of entropy and finite output-ensemble formulation are the source formulas in coordinates. This does not claim minimum-entropy attainment, which is unnecessary for C's conclusion.

For the auxiliary witness family, **BODY_MATCH OK as existential selection; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK; CHARACTERIZATION OK (`separatingFamily_bounds/pos`); CHOICE_INDEPENDENCE N/A (the source does not demand a unique channel); DEFINITION_VERDICT PASS within K≥2**. Its two-value totalization is an auxiliary sequence prefix, not an invented definition of a manuscript-defined unique object. The exact proof chooses K≥2 explicitly. No independence-of-choice theorem is mathematically required for an existential witness or a family whose every selected term satisfies the same proved estimates.

## Actual use, rather than name reachability

`OperationalConsequences.lean:73–78` applies `DeterministicConsequences.exists_small_chi_large_gap_and_ratio hε (2*A) R`, obtains **one T** and its positivity/smallness/gap/ratio proofs, and reuses that T. `two_use_gain_le_classical_gain` (22–24) gives χ₂/2−χ≤C−χ; expanding `gap` and linear arithmetic turns `2A≤χ₂−2χ` into A≤C−χ. This is not four independently selected witnesses or an assumption of the conclusion.

The deterministic producer (`DeterministicConsequences.lean:111–121`) intersects four eventual conditions: K≥2, χ<ε, gap≥2A, ratio≥R. All are properties of its one `separatingFamily K`. Its `actual_vanishing_diverging` (58–72), `actual_gap_tendsto_atTop` (74–83), and `actual_ratio_tendsto_atTop` (93–107) establish them. Ratio division explicitly uses `separatingFamily_pos` and `2χ>0`. `exists_actual_separating_channel_positive` (19–40) supplies the family from `DeterministicQualitative.exists_actual_channel_bounds_positive` (86–92). The latter applies the concrete dimensional producer at 33–82, including the genuinely proved positivity term `DampedPositivity.converted_damped_block_holevoBits_pos` (118–133). No `AnalyticInputs` is passed in this path.

The capacity bridge is a proved theorem, not a definition alias: `classicalCapacity_eq_regularizedHolevo` (`OperationalCodingTheorem.lean:67–69`) invokes `operationalCapacity_eq_regularizedHolevoSupremum` (50–53), combining converse and achievability. The lower bound consumes actual block coding and physical blocking at 32–38. `half_chiTwo_le_classicalCapacity` (77–80) rewrites through that bridge and invokes the n=1, two-use bound of `RegularizedHolevo.lean:155–157`. The actual target therefore talks about codes with vanishing Born error even though its short final assembly uses the proved regularization identity.

## Findings and limits

1. **C1 — Strengthened source-supported statement, not verbatim corollary.** One shared T satisfies all four conditions; ε is positive and A,R may be any reals. Metadata correctly describes an `alternate_argument`.
2. **C2 — Correct units and safe denominator.** χ and χ₂ are bits, C is bits/use, and the ratio is χ₂/(2χ). Positivity is supplied by the construction and included in the conclusion.
3. **C3 — Actual operational meaning.** C is defined by concrete encoders/POVMs and vanishing error, with a proved coding bridge consumed in the proof.
4. **C4 — Legitimate selected family and alternative proof.** No source-defined unique channel is claimed. The K<2 prefix cannot supply the target witness; finite moments and damping replace the paper's qualitative random-matrix route. This review checked the producer's type and term composition, not all finite-moment estimates from first principles.
5. **C5 — Scope boundary.** This endpoint does not by itself prove the prescribed-dimensional family, fixed-K liminf constants, zero-Holevo characterization, or pure-input minimum attainment. Those are not hypotheses or conclusions hidden here. Exact application/axiom closure must be read from the [current verification record](../verification/statement-audit-20261006/checks.json); static type/hash checks alone do not establish those checks.
