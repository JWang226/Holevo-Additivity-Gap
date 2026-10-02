<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Free operators and finite Haar matrices

## A tractable comparison model

Free-group regular unitaries act on the Hilbert space with basis indexed by group words. Their combinatorics allow a useful operator norm estimate for the tensor polynomial associated with a traceless coefficient matrix.

The [Collins–Youn comparison](result:free-collins-youn), in the normalization used here, gives the scale

$$
c(K,n)^2=\frac{(1+9/K)^n-1}{K^n}.
$$

The operator norm is bounded by $c(K,n)$ times the Hilbert–Schmidt coefficient norm. The proof library establishes this comparison; the final channel theorem does not assume it.

## A finite channel requires finite matrices

The free operators themselves act on an infinite-dimensional space. The channel endpoint must instead contain actual finite Kraus matrices.

The quantitative route uses structured polynomials in finite Haar unitary models, reduced to two base generators per leg. A finite-net polynomial and finite moment estimates compare the Haar expected operator norm with the free norm. The dimension is chosen to make the approximation losses fit the required tolerance.

This is more specific than an abstract assertion that every polynomial norm converges as dimension grows: the proof keeps enough numerical control to reach the prescribed $N$.

## Expected norm versus a realization

An expectation upper bound does not bound every sample. A selection argument finds a favorable sample, and the polynomial/net construction makes that sample control every required observable.

The [favorable-probability result](result:favorable-probability) also records an explicit positive probability for the relevant norm event. The [certificate result](result:prescribed-norm-certificate) uses the estimate to produce the finite channel.

## Corresponding Lean results

[collinsYounBound](lean:Nonadditivity.CollinsYounProduct.collinsYounBound) is the free comparison. [explicitHaarExpectation](lean:Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation) is the specialized finite-size expectation endpoint.

Read [Haar moments](concept:finite-moments) for the counting mechanism. The [generic Haar interfaces](result:generic-haar-convergence) are recorded separately: definitions of broad convergence predicates are not proofs of those predicates.
