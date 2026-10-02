<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Prescribed norm certificate

## Mathematical content

At the prescribed local size and moment order, the finite Haar expected norm of each admissible self-adjoint linear polynomial is controlled by its free-regular norm with an explicit multiplicative error.

A finite net and a combined polynomial then select one sample whose block channel $\Phi$ satisfies

$$
\|\Phi^*(A)\|_{\mathrm{op}}
\le\frac{n+1}{n-1}\,c(K,n)\|A\|_{\mathrm{HS}}
$$

for every traceless Hermitian output observable.

## Two formal steps

The expectation theorem supplies the analytic comparison. The certificate theorem accepts that comparison as a premise and proves the finite sample-selection and net-extension consequences. Their combination in the main assembler removes the expectation premise.

The [interactive proof map](site:dependencies.html) preserves this distinction: separately proved ingredients can meet in an assembler without one theorem's proof directly referencing the other.

## Why uniformity matters

Testing a few observables would not control every output density matrix. The net reduction and extension make the estimate uniform, allowing the [purity/entropy theorem](result:purity-entropy) to bound all single-use ensembles.

Read the [adjoint-certificate concept](concept:adjoint-certificate) for the trace-duality argument.
