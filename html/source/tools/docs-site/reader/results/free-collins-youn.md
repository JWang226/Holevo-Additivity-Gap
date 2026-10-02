<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Free-operator comparison

## Mathematical statement

For $K\ge2$, $n\ge1$, and a traceless coefficient matrix, the normalized free tensor polynomial has operator norm at most $c(K,n)$ times the Hilbert–Schmidt norm, where

$$
c(K,n)^2=\frac{(1+9/K)^n-1}{K^n}.
$$

The coefficient matrix is the observable appearing in the channel-adjoint problem.

## Proof idea

Creation and annihilation estimates control the one-factor expression. Tensor induction retains the improved coefficient scale across the block factors. This establishes the comparison in the free regular representation.

## Role in the finite construction

The free model supplies a tractable target norm. The [finite Haar comparison](concept:free-haar) approximates that target and produces a finite realization with adjoint coefficient $\kappa_n c(K,n)$.

This is a proved operator estimate, not a hypothesis left in the main channel endpoint. The [certificate](result:prescribed-norm-certificate) and [entropy consequence](result:purity-entropy) explain its downstream use.
