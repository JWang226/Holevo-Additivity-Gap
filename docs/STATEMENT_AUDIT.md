<!--
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See ../COPYRIGHT.md for licensing and attribution.
-->

# Statement correspondence audits

Six principal Lean statements received independent AI source-and-definition
reviews on 2026-10-06. The reviewers found no excess theorem hypothesis,
split channel witness, or mismatched numerical constant in these endpoints.
The reports document the qualifications needed to read them alongside the
manuscript. This is a review of mathematical meaning, not a machine proof of
English–Lean equivalence or an independent human certification.

## What was reviewed

| Challenge | Informal result | Report and principal qualification |
| --- | --- | --- |
| A | Prescribed channel dimensions and information bounds | [Prescribed dimensions](AUDIT_PRESCRIBED.md): combines the main theorem with its supplementary single-use lower bound, on the same channel. |
| B | Operational capacity equals regularized Holevo information | [Operational coding](AUDIT_CODING.md): nonempty physical spaces and finite Kraus channels; the limit formulation is a separate theorem. |
| C | Small positive one-use information with large capacity gain and two-use ratio | [Simultaneous separation](AUDIT_SEPARATION.md): strengthens the two corollaries into a common-witness statement using the proved deterministic construction. |
| D | Weyl-extension identity at every positive number of uses | [Weyl powers](AUDIT_WEYL.md): proves the entropy-infimum identity for self-powers; minimizer attainment and the general distinct-channel assertion are outside this root. |
| E, first root | Two-sided single-use bounds in terms of input cost | [Input cost](AUDIT_INPUT_COST.md): eventual bounds for the selected growing family, with explicit constants. |
| E, second root | Two-use information and capacity lower bounds at that input cost | [Input cost](AUDIT_INPUT_COST.md): the same family and physical input dimension; the finite initial segment does not enter the asymptotic assertion. |

The [Manuscript-to-Lean map](PROOF_MAP.md) covers more results. These reviews
cover the six configured challenge roots, not every statement in the paper
or a fresh line-by-line audit of every proof dependency.

## Qualifications that matter

- **Minimum versus infimum.** The manuscript writes a minimum output entropy
  and uses a minimizing state. Lean's `minimumEntropy` is an infimum. The Weyl
  root proves the numerical identity with that infimum; this review did not
  locate a formal theorem establishing attainment or reduction to pure
  minimizers. The report does not silently count those additional claims as
  formalized.
- **Channel representation.** The development uses finite Kraus realizations
  and proves their complete positivity and trace preservation. The universal
  coding and Weyl roots do not also prove a representation theorem converting
  an arbitrary abstract CPTP linear map into Kraus data. The manuscript uses
  the abstract presentation.
- **Domains and sequences.** Some general information helpers also accept
  empty coordinate types; the coding root explicitly excludes those types.
  The input-cost family is defined at all natural indices, with a finite
  initial completion, and matches the manuscript's parameters eventually.
  Neither extension supplies a missing hypothesis or weakens the stated
  physical/asymptotic conclusion.

These are recorded scope qualifications. No proof or manuscript changes were
made as part of this review. All six machine-readable entries use `qualified`
to retain these distinctions, including where a report gives a scoped PASS.

## Method and evidence

Four fresh AI review tasks reconstructed their assigned statements from the
raw manuscript before inspecting the existing challenge and implementation.
They enumerated explicit, implicit, and instance binders; expanded bundled
proof fields; inspected the definitions of channels, entropy, ensembles,
codes, rates, dimensions, and selected witnesses; and checked units and
quantifier order. A further read-only AI review crosschecked the reports,
followed by an integration review.

The method adapts selected procedures from
[LeanAutoformalizationSkills' statement-audit skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/601fe274276d93052ef645f0ff2c1a355e8e5b16/skills/lean-statement-audit/SKILL.md).
The existing solved declarations and verification tools are retained. In
particular, selecting a channel from a proved existential does not require
uniqueness when the manuscript asserts none. This release does not claim
compliance with every rule of the upstream workflow.

The [audit manifest](../verification/statement-audit.json) records each root,
report, reviewer identifier, manuscript labels, qualifications, and files
inspected for that review. Its broader freshness envelope hashes all project
Lean sources, the manuscript, challenge files, declaration/result metadata,
and toolchain pins. Hashing a file does **not** mean its full contents received
semantic review. Reports and retained mechanical logs are also hash-bound.

The reviewed source checkout was
`5aa9c82f86a6d91bee0ddf773500086e85d5d592`. Documentation added later is identified
by its own file hashes. The freshness checker rejects changed inputs, missing
current proof files, invalid target/label associations, and modified reports
or logs. It does not authenticate a reviewer, establish the truth of review
judgments, or turn a `mismatch` or `unresolved` verdict into a pass.

Fresh [mechanical checks](../verification/statement-audit-20261006/checks.json)
elaborated five expected-statement modules, checked all six actual proofs
against those types, and printed the full root types and transitive axioms.
All passed with only `propext`, `Classical.choice`, and `Quot.sound`.
These incremental checks reused compiled project dependencies. They were not
a clean project rebuild or a new Comparator/Nanoda run. The separately
retained Comparator, Lean replay, and Nanoda evidence also passed its existing
source-freshness check.

## Reproduce the checks separately

From the repository root, inspect the retained records without compiling:

```sh
python3 verification/check_statement_audit.py
python3 verification/check_reports.py
```

With the pinned Lean toolchain and built project dependencies available,
rerun the statement applications and type/axiom probe:

```sh
python3 scripts/check_challenges.py
./lean.sh verification/statement-audit-20261006/Roots.lean
```

For the complete source build, Comparator, or Nanoda commands, use the
[verification guide](../verification/README.md). Each can still be run
separately. None of these commands repeats the informal semantic review.

The freshness validator's negative controls can be run independently:

```sh
python3 scripts/test_statement_audit.py
```

When a mathematical source changes, review the affected statements and
definitions again, rerun the applicable mechanical checks, and only then
update the recorded evidence and hashes. Do not refresh hashes merely to
silence a stale-review error.
