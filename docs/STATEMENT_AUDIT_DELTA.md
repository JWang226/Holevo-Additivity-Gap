<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# Cleanup statement-review continuation

The cleanup preserves the six configured mathematical endpoints and their
previously recorded qualifications. This is an AI review of the **source delta**
and the affected definition contexts, continuing the
[historical independent reviews](STATEMENT_AUDIT.md). It is not a new complete
semantic audit of the manuscript or a machine proof of English–Lean equivalence.
The historical manifest, five semantic reports and mechanical logs remain
unchanged. The new [selected record](../verification/statement-audit-current.json)
identifies the current continuation and its fresh mechanical evidence.

## Changes reviewed

The reviewed mathematical delta is from
`a92c087e85603032cd0ece7b766b1f192b17a69e` to the proof sources of
`e943a85f0234a573477a10871f60a2d9583fa47b`, retained in the release candidate.
The [complete patch](../verification/statement-audit-20261007/proof-source-delta.patch)
and [file-by-file inventory](../verification/statement-audit-20261007/delta-review.json)
make its scope inspectable.

| Change | Semantic review finding |
| --- | --- |
| 50 direct local imports removed in 40 files | Each removed module remains in the same transitive local import closure through a retained provider path. No source declaration, instance, annotation or proof command was removed by this sweep. The complete baseline rebuild passed. Import closure is a dependency fact; acceptance of the actual declarations and exact public-type comparison supply the separate elaboration checks. |
| `Nonadditivity/Main.lean` module comment corrected | The old comment claimed unconditional endpoints were still open. The replacement points to the existing endpoint modules and current formalization scope. Both versions are comments, so this changes no declaration. |
| `RegularCoefficientEnergy.reindexFunction` summand supplied explicitly | Its data component is still `fun g => f (e g)` on vector-valued ℓ². The only changed expression is the proof that this function belongs to ℓ². The added `f := fun g : G => ‖f g‖ ^ (2 : ℝ≥0∞).toReal` is the norm-power function already required by `memℓp_gen` and supplied by `f.property.summable`. Reindexing by the same equivalence gives the same summability proposition. No additional premise, default branch, carrier, exponent or observable operator is introduced. |
| Fresh declaration export | Metadata was generated from the rebuilt development and compared with the historical export by independently decoding canonical kernel type bytes. This refreshes evidence; it is not a mathematical source change or proof of definition-body equivalence. |
| Release references in result metadata | Current evidence/selector paths identify the continuation while retaining historical references. Mathematical result identifiers, manuscript labels, formal pointers, notes and limitations must remain unchanged; the capture script rejects other result-metadata changes. |

In particular, type equality alone would be insufficient if a definition's
meaning changed while retaining its type. Here the source delta was inspected:
all data-valued formulas are unchanged, and the sole proof edit is the subtype
membership proof described above. `reindexIsometry`, `leftRegular` and
`regularPolynomial` still consume the same coordinate function; the coefficient
energy inequality remains a proved conclusion rather than a hypothesis. The
failed Gram-helper and null spectral-ascription experiments were reverted and
are absent from this patch. No heartbeat or recursion limit changed.

## Endpoint and definition-context review

The manuscript's definitions and claims were reread at `eq:def-chi`,
`eq:capacity`, `thm:main`, `cor:capacity`, `cor:separation`,
`rem:separation-cost`, `eq:chi-extension` and `eq:constructed-holevo-lower`.
The actual root statements and the relevant channel, entropy, capacity,
dimension and selected-family definitions were inspected in the current sources.
The table records the delta conclusion; the historical reports retain the full
binder inventories and source correspondence arguments.

| Challenge / root | Definitions and mathematical context checked | Retained qualification |
| --- | --- | --- |
| A: prescribed dimensions | `FiniteQuantumChannel`, finite Kraus output, `chi`, `chiTwo`, gap, `localDimension`, `n₀`, `aK`, `deltaK`, `kappa` and the joint existential producer. The same single channel carries both dimensions, positivity, the `2n/K` lower bound, one-use upper bound, two-use lower bound and gap bound. | Combines the main theorem and supplementary lower bound. Weyl conventions agree after phase cancellation and relabeling. |
| B: operational coding | Nonempty input/output carriers, finite Kraus channel, physical code sequence, vanishing average decoding error, operational rate supremum and normalized positive tensor-power Holevo supremum. No new analytic premise or channel certificate appears in the root. | The root states the supremum identity; convergence is a separate theorem. An abstract CPTP-to-Kraus representation theorem is outside this root. |
| C: simultaneous separation | The closed deterministic existential supplies one channel with positive small `chi`, arbitrarily large capacity gain and two-use ratio. `classicalCapacity` is the operational quantity, and `twoUseRatio` has the same division by `2 chi`. | A stronger common-witness conjunction using the alternate deterministic construction. The quantitative prescribed-dimension and sequence claims are outside this root. |
| D: positive self-powers of a Weyl extension | Index `n` denotes `n+1` uses; `holevoBits` divides natural-log entropy by `ln 2`; the subtracted output entropy is the same real infimum over actual channel outputs. No minimizer or abstract representation bridge was added by cleanup. | Infimum identity, with minimizer attainment/pure-minimizer reduction unformalized; finite Kraus self-powers only, rather than the distinct-channel identity. |
| E, first: one-use input cost | `growingFamily`, its joint prescribed witness, actual input cardinality, `inputQubits = log₂(card Input)`, `inputLogScale = sqrt(2/ln 2)` and the two-sided eventual bound on `chi sqrt(log₂ inputQubits)`. | Finite-prefix totalization disappears eventually; no uniqueness or choice-independent channel value is asserted. |
| E, second: two-use input cost | The same selected family and physical input qubits; `chiTwo/2` is per-use two-use information; operational capacity is bounded below using that same channel. The positive constant `1/(8 ln 2 inputLogScale)` and eventual denominator positivity remain unchanged. | Eventual lower bound with the same finite-prefix and existential-selection qualifications. No optimal leading constant is claimed. |

The changed endpoint-context files contain import removals only. The six
root statements, manuscript, challenge statements and all meaning-carrying
definitions above retain their mathematical contents. Existing qualifications
are copied unchanged into the continuation's six `qualified` entries; they
are not upgraded to unqualified correspondence passes.

## Mechanical evidence and reproduction

The new record is published only after real current-source expected-statement
applications and root type/axiom probes succeed. Its
[checks manifest](../verification/statement-audit-20261007/checks.json) records
actual commands, exit codes, six root axiom closures, source bindings and retained
logs. The checks reuse the project objects available at execution; their scope
does not itself claim a clean rebuild, Comparator run or Nanoda run. Those checks
remain separately recorded by the release verification workflow.

```sh
# Check the selected current continuation without executing Lean.
python3 verification/check_statement_audit.py

# Select the historical record explicitly; cleanup sources intentionally make
# its historical source-freshness check fail.
python3 verification/check_statement_audit.py --audit verification/statement-audit.json

# With current project dependencies already built, rerun the exact-type checks.
python3 scripts/check_challenges.py
./lean.sh verification/statement-audit-20261007/Roots.lean

# Synthetic controls check the selector, parent preservation, delta coverage,
# source/type/log freshness and unchanged qualifications.
python3 scripts/test_statement_audit.py
```

The freshness checker checks recorded identity and provenance. It does not
authenticate a reviewer, verify the semantic reasoning in this report, repeat
that review, or resolve the explicitly unformalized representation and entropy
attainment claims. Later mathematical changes require a new reviewed successor;
the historical review and this continuation must not be resealed merely to make
changed source hashes pass.
