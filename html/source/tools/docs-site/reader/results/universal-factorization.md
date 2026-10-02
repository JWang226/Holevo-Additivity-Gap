<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Universal finite-set factorization

## What the theorem establishes

The finite-set factorization chooses a scalar and coefficient data before choosing a unitary representation. The same choice works for every nonzero complete complex Hilbert space in the theorem, including infinite-dimensional spaces.

An associated error-transfer estimate carries a norm approximation for the factorized linear expression back to the original finite-set polynomial.

## Why the quantifiers matter

Choosing fresh coefficients separately for each finite representation would not give a uniform reduction suitable for comparing the free and finite models. The universal choice provides one object whose behavior can be analyzed in both.

The nonzero-space hypothesis is explicit. It is required for the additive scalar norm identity used by the factorization.

## Role in the proof

The [structured linearization](lean:Nonadditivity.StructuredLinearization.exists_net_linearization) packages many observable tests. The factorization is an algebraic tool for reducing word length and transferring approximation errors within that process.

Read [the free/Haar comparison](concept:free-haar) and the exact declarations below for the coefficient support, representation class, and error hypotheses.
