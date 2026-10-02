<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Generic Haar-convergence interfaces

## Definitions are not existence proofs

The library defines predicates describing strong convergence, upper norm convergence, and trace-moment control for broader Haar models. An older conditional theorem may accept one of these predicates and derive a channel consequence.

Defining the predicate or proving an implication from it does not establish that the predicate holds.

## The completed route is more specific

The [prescribed expectation theorem](result:prescribed-norm-certificate) and [sharp moment theorem](result:haar-moment-range) prove the specialized finite estimates needed by the channel construction. The final prescribed channel theorem has no generic convergence premise.

The [qualitative realization](result:qualitative-realization) also uses a separate completed deterministic argument.

## Corresponding formal entries

The declarations listed below are broad predicates or conditional interfaces. Their presence in the checked library should not be interpreted as proofs of generic strong convergence.

Read [free operators and finite Haar matrices](concept:free-haar) for the comparison actually used, and [reading Lean](guide:reading-lean) for checking assumptions.
