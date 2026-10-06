<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution. -->

# Independent AI audit of the operational coding root

**Verdict: qualified root correspondence.** The exact root faithfully identifies
the independently defined operational capacity with the regularized Holevo
supremum, in bits, for finite Kraus channels with nonempty input and output
spaces. It has no excess premise. Its supporting public definitions have a
broader, totalized empty-space carrier than the manuscript's physical domain;
that qualification is recorded below rather than silently treating the broader
carrier as a physical capacity definition.

This is an independent AI source and semantics review dated 2026-10-06, not a
machine certificate of English equivalence. The reviewer read the manuscript
statement and bibliography before the declaration or implementation. The
review uses the binder, definition-body, carrier, and consumption methods of
the `lean-statement-audit` skill at upstream revision
`601fe274276d93052ef645f0ff2c1a355e8e5b16`, adapted to this existing proved
release. It does not claim compliance with the upstream freeze, draft,
versioning, or approval workflow. No proof files were edited and no builds were
run by this reviewer. Fresh exact-application and axiom checks are supplied
in the [retained mechanical evidence](../verification/statement-audit-20261006/checks.json).

## Source reconstruction before implementation

The source is `paper/nonadditivity.tex`, SHA-256
`3a65f68ea51e3b1dd6f66f1e0d53c9273e3d4abc0522a650c05ccd304b435b98`.
The mathematical reading recorded first was:

1. Lines 88–92 define a channel as a completely positive, trace-preserving
   linear map between full finite complex matrix algebras, including its action
   on unnormalized matrices.
2. Lines 97–101, `eq:def-chi`, define
   `chi(Phi) = sup_{(p_x,rho_x)} [S(sum_x p_x Phi(rho_x)) -
   sum_x p_x S(Phi(rho_x))]`, with `S(rho) = -Tr(rho log_2 rho)`.
   States and probability weights have their usual normalization. The input
   state to a tensor-power channel may be entangled across its uses.
3. Lines 104–109, `eq:capacity`, identify unassisted classical capacity with
   both the limit and the supremum of `chi(Phi^tensor m)/m`, over every integer
   `m >= 1`. No coding estimate, convergence hypothesis, or chosen ensemble is
   a premise of this assertion.
4. Lines 104–105 cite Holevo and Schumacher–Westmoreland. The bibliography
   entries are at 2733–2737 and 2805–2809. The manuscript cites this coding
   theorem; the Lean development supplies a proof of its formal formulation.

The manuscript does **not** spell out an operational code definition or the
error and rate quantifiers at this location. Their expansion below is a review
of the standard unassisted, uniform-message, vanishing-average-error meaning
of the cited term, not a claim that those formulas are literally printed in the
manuscript. In that reading, a positive-length code has `M >= 1` messages,
arbitrary joint input states, and a joint output POVM; its rate is `log_2 M/m`.
A rate is achievable when one sequence of such codes, at all positive lengths,
has error tending to zero and eventually exceeds every strictly smaller rate.
Capacity is the supremum of the achievable real rates.

## Exact target and identity evidence

The target is
`Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum`
in `Nonadditivity/OperationalCodingTheorem.lean:50–53`. It is the sole target
of `ComparatorChallenges/B_OperationalCoding.json` and the declaration at
`ComparatorChallenges/B_OperationalCoding.lean:16–19`.
`metadata/results.json:121–145` associates result `operational-coding` with
`eq:capacity` and separately lists the limit theorem.

The full exported type in `metadata/declarations.json` is:

```lean
∀ {ι : Type u_1} {ο : Type u_2} {κ : Type u_3}
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
  (T : Nonadditivity.Channels.KrausChannel ι ο κ),
  Nonadditivity.Operational.operationalCapacity T =
    sSup (Set.range (Nonadditivity.RegularizedHolevo.normalizedPowerHolevo T))
```

The metadata's gzip/base64 expression was decoded and its SHA-256 recomputed:
`b24ef587a7b61c32a601b1852d194757045d89107b36a0332204e2430c7937fe`,
matching the stored value. The source/challenge/readable export agree on
quantifier order, implicitness, carrier, and conclusion. This is textual and
export-integrity evidence; it is not a fresh elaboration check.

| Pinned file | SHA-256 |
|---|---|
| `Nonadditivity/OperationalCodingTheorem.lean` | `2db3bc12bdb69285f018eeecb13fef9793f30521b676a6561f4476ebee9451b7` |
| `ComparatorChallenges/B_OperationalCoding.lean` | `df0510a19dc3ed2ea5b750095d81cc18e40db430b10ee571a84de83bdd26e1a9` |
| `ComparatorChallenges/B_OperationalCoding.json` | `dd80623b945a2c41ba2a2fec81382c0e23096aacaf0e5d6bbefb98c14948fc06` |
| `metadata/declarations.json` | `9e42707d1781901fe0e4f39e7b9340626832409329aa5c485e4f614ffb70b201` |

The challenge's `sorry` is an expected-statement placeholder in the comparator
input, not the solution proof. This report makes no claim of external
Comparator execution.

## Complete binder audit

SOURCE means a mathematical input of the source assertion; TYPING means finite
matrix coordinates, dimension conventions, or their representation machinery.
STANDING, RULED, and EXCESS are unused. The three universe levels are sort
parameters, not logical hypotheses. All eleven term binders occur below in
outer-to-inner order; `T` is then recursively expanded in the next table.

| # | Binder and Lean type | Mode | Bin | Source justification |
|---:|---|---|---|---|
| 1 | `ι : Type u_1` | implicit | TYPING | Coordinates of the input complex matrix algebra; paper 88–92. |
| 2 | `ο : Type u_2` | implicit | TYPING | Coordinates of the output complex matrix algebra; paper 88–92. |
| 3 | `κ : Type u_3` | implicit | TYPING | Index of a finite Kraus representation of the channel; representation qualification below. |
| 4 | `Fintype ι` | instance | TYPING | Finite input dimension in paper 88–92. |
| 5 | `DecidableEq ι` | instance | TYPING | Coordinate equality for finite matrices; imposes no analytic estimate. |
| 6 | `Nonempty ι` | instance | TYPING | Positive-dimensional physical input space, needed for normalized input states. |
| 7 | `Fintype ο` | instance | TYPING | Finite output dimension in paper 88–92. |
| 8 | `DecidableEq ο` | instance | TYPING | Coordinate equality for output matrices. |
| 9 | `Nonempty ο` | instance | TYPING | Positive-dimensional physical output space supporting trace-one states. |
| 10 | `Fintype κ` | instance | TYPING | Finite Kraus family; no Kraus-rank bound is imposed. |
| 11 | `T : KrausChannel ι ο κ` | explicit | SOURCE | The channel quantified by paper 88–109, represented by the following two fields. |

`Channels.lean:29–32` has exactly these fields and no parent structure,
typeclass gate, or hidden result field:

| Expanded leaf replacing binder 11 | Lean type | Bin | Justification |
|---|---|---|---|
| `T.kraus` | `κ → Matrix ο ι ℂ` | SOURCE | Concrete data for the given channel; its full-matrix action is the Kraus sum at `Channels.lean:39–40`. |
| `T.complete` | `∑ k, (T.kraus k).conjTranspose * T.kraus k = 1` | SOURCE | Trace-preserving channel normalization; paper 88–92. Complete positivity and linearity are derived from this representation, not extra fields. |

| Count convention | SOURCE | STANDING | TYPING | RULED | EXCESS | Total |
|---|---:|---:|---:|---:|---:|---:|
| Original theorem binders | 1 | 0 | 10 | 0 | 0 | 11 |
| Expanded leaves, replacing `T` by its two fields | 2 | 0 | 10 | 0 | 0 | 12 |

The two representations are not added together. `Fintype` contains an
enumeration and its completeness proof; `DecidableEq` contains equality
decisions; `Nonempty` contains an inhabitant. These are ordinary library typing
structures, not project-owned mathematical assumption bundles. There is no
`Nonempty κ` or `DecidableEq κ` binder hidden in the export. On this root's
nonempty input carrier, a genuinely empty Kraus family cannot satisfy
`T.complete`.

## Expansion of physical witnesses and their proof fields

The following structures occur **inside the definitions in the conclusion**.
They are not additional premises of the root. This table expands every
project-owned field in the code/ensemble carriers, including all proof fields;
their local quantified variables are shown in their types. Thus a proof of a
coding theorem has not been disguised as part of a physical code.

| Structure field | Full mathematical content of its Lean type | Source meaning / local definition |
|---|---|---|
| `DensityMatrix.matrix` | `Matrix ι ι ℂ` | A finite complex state matrix; `Entropy.lean:142–145`. |
| `DensityMatrix.positive` | `matrix.PosSemidef` | Exactly Hermiticity and nonnegative quadratic form, expanded below. |
| `DensityMatrix.normalized` | `matrix.trace = 1` | Trace-one state normalization. |
| `POVM.effect` | `μ → Matrix ο ο ℂ` | One effect per finite measurement outcome; `OperationalConverse.lean:29–32`. |
| `POVM.positive` | `∀ m : μ, (effect m).PosSemidef` | Every effect is Hermitian positive semidefinite, of arbitrary rank. |
| `POVM.complete` | `∑ m : μ, effect m = 1` | A complete POVM; no missing success mass or uncounted failure outcome. |
| `Code.encode` | `Fin M → DensityMatrix ι` | An arbitrary state for each message; `OperationalConverse.lean:82–84`. |
| `Code.decode` | `POVM ο (Fin M)` | Joint measurement with the expanded positivity/completeness requirements above. |
| `CodeSequence.messages` | `ℕ → ℕ` | Message count for every positive block length; `OperationalCapacity.lean:29–32`. |
| `CodeSequence.messages_pos` | `∀ n : ℕ, 0 < messages n` | Excludes zero messages at every block length. |
| `CodeSequence.code` | `∀ n : ℕ, Code (positiveTensorPower T n) (messages n)` | Every block carries an actual encoder/decoder as expanded above. |
| `Ensemble.size` | `ℕ` | Arbitrary finite ensemble size; `StateEnsembles.lean:90–96`. |
| `Ensemble.weight` | `Fin size → ℝ` | Probability weights. |
| `Ensemble.weight_nonneg` | `∀ i : Fin size, 0 ≤ weight i` | Zero weights allowed; negative weights excluded. |
| `Ensemble.weight_sum` | `∑ i : Fin size, weight i = 1` | Normalization; also makes an empty ensemble impossible. |
| `Ensemble.state` | `Fin size → DensityMatrix ο` | Each output state has the three density-matrix fields above. |
| `Ensemble.state_mem` | `∀ i : Fin size, state i ∈ T.outputs` | Unfolds to `∀ i, ∃ ρ : DensityMatrix ι, T.output ρ = state i`; actual channel outputs, not arbitrary states of the output dimension. |

The library predicate `Matrix.PosSemidef`, at
`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:56–59`, is
`M.IsHermitian ∧ ∀ x : ι →₀ ℂ,
0 ≤ x.sum (fun i xi => x.sum (fun j xj => star xi * M i j * xj))`.
On finite coordinates this is the usual nonnegative quadratic-form condition
for every vector. `IsHermitian` means `M.conjTranspose = M`. Thus neither state
positivity nor effect positivity is a project alias concealing a coding or
entropy estimate.

There is no shared entangled resource, auxiliary receiver state, feedback, or
side communication in `Code`. The only decoder input is the channel output.
The allowed encoder states on a tensor-power input are arbitrary joint
density matrices; the definition imposes no separability or product condition.

## Definition bodies, carriers, and normalizations

| Object and source lines | Body / carrier actually inspected | Correspondence and endpoint behavior |
|---|---|---|
| `KrausChannel.map`, `Channels.lean:39–40` | `X ↦ ∑ k, A_k X A_k*` on all complex input matrices. | Matches the full-algebra action in paper 88–92. Linearity is proved at 42–55, trace preservation at 65–75, all finite ancilla positivity at 308–316. |
| `KrausChannel.output`, `Channels.lean:78–82` | Packages that map applied to a density matrix; positivity and trace-one proofs are supplied internally. | Actual output state, without assumed output estimates. |
| `KrausChannel.tensor`, `Channels.lean:280–294` | Kraus matrices `A_k ⊗ B_l`, acting by the full-matrix Kraus sum. | Defined on all joint matrices, including entangled input states. The product-input theorem at 298–305 does not restrict the definition. |
| `PositiveTensorIndex`, `RegularizedHolevo.lean:30–56` | At `0`, `ι`; at successor, previous index times `ι`; finite/equality/nonempty instances are constructed. | `n` means precisely `n+1` factors, with cardinality `card ι ^ (n+1)` proved at 58–65. |
| `positiveTensorPower`, `RegularizedHolevo.lean:68–74` | At `0`, `T`; at successor, previous power tensor `T`. | Covers every positive integer length, no selected subsequence or zero-use normalization. |
| `POVM.probability`, `OperationalConverse.lean:39–54` | `Re Tr(ρ E_m)`. Nonnegativity and sum-one are proved. | Actual Born probability. The real part does not discard a physical imaginary component because both matrices are Hermitian positive semidefinite. |
| `Code.success`, `.error`, `OperationalConverse.lean:129–133` | `success = (∑ m, probability (T.output (encode m)) m)/M`; `error = 1-success`. | Uniform average error, not worst-case error. `messages_pos` ensures no division by zero in any `CodeSequence`. |
| `CodeSequence.rate`, `OperationalCapacity.lean:39–40`; `Scalar.log2`, `Scalar.lean:26` | `(ln M/ln 2)/(n+1)`. | Bits per elementary use, matching paper 101, 107–109. `M>=1`, `n+1>0`, and `ln 2>0`. |
| `VanishingError`, `OperationalCapacity.lean:42–43` | `Tendsto (fun n => (S.code n).error) atTop (𝓝 0)`. | Actual errors tend to zero along all lengths. |
| `HasRate`, `OperationalCapacity.lean:45–46` | `∀ r < R, ∀ᶠ n in atTop, r ≤ S.rate n`. | Equivalently, every strictly smaller real rate is attained eventually. Rate need not have a limit. Quantifier order permits the length threshold to depend on `r`; one code sequence must work for all `r`. |
| `AchievableRate`, `OperationalCapacity.lean:140–141` | `∃ S : CodeSequence T, S.VanishingError ∧ S.HasRate R`. | No Holevo quantity, coding certificate, or bridge premise occurs in this predicate. Negative real rates are harmless and do not enlarge capacity; zero is achievable. |
| `operationalCapacity`, `OperationalCapacity.lean:145–146` | `sSup {R : ℝ \| AchievableRate T R}`. | Independent physical definition on the root domain. `zero_achievable` at 170–176 and `achievableRates_bddAbove` at 191–193 rule out empty/unbounded supremum defaults there. Its broader exported carrier is qualified below. |
| `DensityMatrix.weights`, `.vonNeumann`, `Entropy.lean:147–164`; `shannon`, 32–33 | Eigenvalues of the actual Hermitian positive matrix; `-∑ i, λ_i ln λ_i`. | Spectral von Neumann entropy in **nats** internally. Zero eigenvalues contribute zero, implementing `0 log 0 = 0`; no pure-state restriction. |
| `DensityMatrix.mixture`, `StateEnsembles.lean:33–42` | Matrix `∑ i, p_i ρ_i`, with positivity and normalization proved. | Exact finite convex average; includes zero-weight terms. |
| `Ensemble.average`, `.information`, `StateEnsembles.lean:98–103` | Mixture entropy minus weighted mean state entropy. | Literal Holevo expression of paper 97–101 before the base conversion. |
| `StateEnsembles.quantity`, `StateEnsembles.lean:108–109` | Supremum of information over all normalized finite ensembles in a specified output set. | On channel outputs in the root domain, a singleton ensemble gives zero (111–128) and information is bounded above by `ln(card ο)` (154–166). No supremum default is used. Arbitrary empty output sets are a broader helper carrier. |
| `KrausChannel.outputs`, `.holevo`, `QuantumHolevo.lean:27–38` | `outputs = Set.range T.output`; `holevo = quantity outputs`. | Supremum over actual channel-output ensembles. Lifting each output to an input gives the source's input-ensemble formulation; linearity identifies the average. Input preimages need not be unique because only their fixed outputs enter the expression. |
| `holevoBits`, `HolevoBits.lean:24` | `T.holevo / Real.log 2`. | Converts natural entropy to the manuscript's bits; the positive scaling commutes with these nonempty bounded suprema. |
| `normalizedPowerHolevo`, `RegularizedHolevo.lean:85–88` | `(positiveTensorPower T n).holevoBits / (n+1)`. | Exactly `chi_bits(T^tensor m)/m` with `m=n+1`; no missing `ln 2` factor. |
| Root right-hand side; `regularizedHolevo`, `RegularizedHolevo.lean:129–130` | `sSup (Set.range (normalizedPowerHolevo T))`; the wrapper substitutes `T.channel`. | Range is nonempty because `n=0` exists; `normalizedPowerHolevo_le` at 103–120 gives the uniform upper bound `log_2(card ο)` on the root domain. |
| `classicalCapacity`, `OperationalCodingTheorem.lean:62–63` | `Operational.operationalCapacity T.channel` for `T : FiniteQuantumChannel`. | This wrapper's carrier bundles nonempty input/output at `ActualConsequences.lean:34–45`. It stays entirely inside the physical source domain. |

These are literal constructions or predicates, not an arbitrary selected real
number awaiting a later source characterization. The operational equality is
a substantive theorem relating two independently constructed quantities; the
definition does not return the regularized supremum under a different name.

The real supremum operator itself is total: mathlib's
`Data/Real/Archimedean.lean:115–117` chooses a least upper bound for a nonempty
bounded set and returns zero otherwise; lines 168–186 give the empty and
unbounded cases. On the root domain the proof facts listed above establish
nonemptiness and boundedness for **all three** relevant suprema (ensemble,
regularized, and operational). Least upper bounds are unique, so the library
choice does not create an arbitrary capacity value there.

## Public carrier qualification and strict-rule result

The exported types of `operationalCapacity`, `AchievableRate`, `CodeSequence`,
and `normalizedPowerHolevo` in `metadata/declarations.json` contain finite and
decidable coordinate instances but **omit `Nonempty ι` and `Nonempty ο`**.
Section-variable declarations alone do not retain unused instances in a Lean
definition's type. These helpers consequently admit empty coordinate types.

For example, take an empty input index, a one-dimensional output index, and a
singleton Kraus index. The unique rectangular Kraus matrix satisfies
completeness because input identity and zero are the same empty matrix. There
is no trace-one input density matrix, hence no positive-message code or code
sequence. The achievable-rate set is empty and the total real supremum yields
zero. Likewise there are no input-output ensembles and the Holevo helper
receives the empty-set value. This is an off-physical-domain extension, not an
operational communication experiment described by the manuscript. It does not
occur at any instantiation of the audited root: the root explicitly requires
both nonempty spaces. The packaged `FiniteQuantumChannel` definitions also
exclude it.

Under the **strict upstream rule applied to the entire exported helper
carrier**, this is a public-carrier failure: that rule rejects a globally
exported definition whose source correspondence holds only on a valid locus.
The present task adapts selected review methods to existing roots and does not
assert wholesale upstream workflow compliance. Accordingly the root verdict
is qualified correspondence, with the stricter finding preserved explicitly.
No physical meaning for empty spaces is invented to erase the finding.

| Definition audit component | On the exact root's physical carrier | Strict audit of broader exported helpers |
|---|---|---|
| BODY_MATCH | OK | FAIL off-source: empty-carrier capacity/ensemble suprema totalize to zero. |
| PUBLIC_CARRIER | OK: the root and `FiniteQuantumChannel` require nonempty input/output. | FAIL: the general helper definitions omit those requirements. |
| WELL_DEFINEDNESS | N/A_LITERAL; each relevant real supremum is proved nonempty and bounded. | N/A_LITERAL; totality alone does not establish source meaning off-domain. |
| CHARACTERIZATION | N/A_LITERAL; capacity/Holevo equality is a proved theorem, not the definition's deferred meaning. | N/A_LITERAL. |
| CHOICE_INDEPENDENCE | OK for least upper bounds by uniqueness; no selected physical object defines capacity. | N/A for the off-domain zero branch. |
| DEFINITION_VERDICT | PASS on the audited root domain. | FAIL under the strict whole-public-carrier rule. |

A second scope qualification concerns representation. The source quantifies
over finite-dimensional CPTP linear maps; this Lean root quantifies over
finite **Kraus realizations**. The inspected code proves that every such
realization gives a linear, trace-preserving map with positive finite ancilla
amplifications. This is the standard concrete representation of the physical
channel carrier. The root does not itself prove that an arbitrary separately
defined abstract CPTP linear map admits Kraus data, and no reverse
representation theorem was identified in the inspected project definitions.
The correspondence judgment uses that mathematical representation convention;
it is not a claim that the project has machine-certified an English-to-Lean
equivalence of those two presentations.

## Proof consumption and scope of the coding assertion

The solution at `OperationalCodingTheorem.lean:50–53` applies antisymmetry to
two proved inequalities. The upper bound is
`operationalCapacity_le_regularizedHolevoSupremum`; the lower bound is
`regularizedHolevoSupremum_le_operationalCapacity`. Neither is an incoming
binder or field of the root.

The lower bound at `OperationalCodingTheorem.lean:32–46` applies
`QuantumCoding.holevoBits_le_operationalCapacity` to **each** positive tensor
power and uses `operationalCapacity_block_le` to rescale. The HSW file at
`QuantumCodingHSW.lean:120–139` lifts arbitrary finite output ensembles to
input states and consumes its proved finite-ensemble coding theorem. Its
constructed word codes (`QuantumCodingChannelWords.lean:89–93`) use product
states across repeated uses of the current channel. Once the current channel
is a block `T^tensor m`, those states can be arbitrary, entangled states inside
each block. Thus this proof construction does not replace the full coding or
Holevo definition by a product-input-only capacity.

`OperationalBlocking.lean:37–57` constructs a full-length sequence by
flattening complete blocks and padding unused positions, and by a valid
one-message code at finitely many short lengths. Lines 60–94 prove preserved
error and rescaled rates. The padding and flattening operations have actual
encoder/decoder bodies with error identities at
`OperationalBlockingCodes.lean:95–122` and
`OperationalBlockingFlatten.lean:93–101`. The short-length branch is an
ordinary physical code inside a proof construction, not an off-source
fallback value in the definition of capacity.

The upper bound at `OperationalWeakConverse.lean:150–194` applies to an
arbitrary `CodeSequence T`, bounds every sufficiently small-error code's rate
by its actual normalized block Holevo quantity plus a correction tending to
zero, and then bounds all achievable rates. No restriction to the product
codes constructed in the lower-bound proof is introduced.

The exact root concludes equality with the **supremum**, not the additional
limit assertion in `eq:capacity`. The result mapping correctly lists
`FiniteQuantumChannel.normalizedPowerHolevo_tendsto_classicalCapacity`
separately (`OperationalCodingTheorem.lean:84–87`), using the genuine all-length
Holevo limit proved at `HolevoRateLimit.lean:118–147`. This review inspected
that separation but does not replace the separate theorem's machine check.

## Review result and boundaries

| Check | Result |
|---|---|
| Exact root binder fidelity | PASS: 11 outer binders, 12 expanded leaves, zero EXCESS. |
| Independent physical capacity definition | PASS on the root's nonempty carrier. |
| Joint inputs and joint POVMs | PASS: arbitrary joint density matrices and normalized POVMs. |
| Rates, errors, all positive lengths | PASS: uniform average Born error tends to zero, eventual lower-rate condition, every positive length. |
| Units | PASS: both root sides are in bits despite natural-log internal entropy. |
| Supremum defaults on root domain | PASS: relevant sets are nonempty and bounded; fallback is never encountered. |
| Broader public helper carriers | QUALIFICATION; FAIL under the strict upstream whole-carrier rule. |
| Abstract CPTP versus Kraus presentation | QUALIFICATION: concrete Kraus carrier; reverse representation is not this root's conclusion. |
| Supremum versus full manuscript identity | Exact root supplies the supremum equality; a separately named theorem supplies the limit. |
| Fresh elaboration / exact application / axiom closure | Coordinating review evidence, not performed by this semantic reviewer. |

The adapted verdict is **qualified_root_correspondence**. No false equation,
hidden coding assumption, product-input restriction, rate normalization error,
or excess theorem premise was found on the exact target's carrier. The broader
empty-carrier totalizations and the representation boundary remain visible
limits of what this source-correspondence review certifies.
