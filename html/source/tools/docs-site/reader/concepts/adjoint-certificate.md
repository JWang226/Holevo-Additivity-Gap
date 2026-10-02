<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# The uniform adjoint certificate

## Testing outputs through observables

The adjoint map $T^*$ is defined by trace duality:

$$
\operatorname{Tr}(A\,T(\rho))=\operatorname{Tr}(T^*(A)\rho).
$$

The construction seeks a constant $t$ such that

$$
\|T^*(A)\|_{\mathrm{op}}\le t\|A\|_{\mathrm{HS}}
$$

for every traceless Hermitian output observable $A$. This compares the operator norm of the pulled-back observable with its Hilbert–Schmidt size.

## Why this controls every output state

For $\sigma=T(\rho)$, write $X=\sigma-I/d$. This is traceless and Hermitian, and

$$
\operatorname{Tr}(X\sigma)=\operatorname{Tr}X^2=\|X\|_{\mathrm{HS}}^2.
$$

Trace duality and the certificate bound the same expression by $t\|X\|_{\mathrm{HS}}$, since $\rho$ is a density matrix. Thus $\|X\|_{\mathrm{HS}}\le t$, including the zero case, and

$$
\operatorname{Tr}\sigma^2=\frac1d+\|X\|_{\mathrm{HS}}^2\le\frac1d+t^2.
$$

The [purity-to-entropy inequality](concept:output-entropy) completes the single-use estimate.

## How one finite sample becomes uniform

First test a finite net of normalized traceless Hermitian observables. A structured polynomial packages these tests into one norm question. An expectation comparison supplies one favorable sample, and a net extension controls all observables.

At the prescribed size, the resulting coefficient is $t=\kappa_n c(K,n)$. The [free comparison](concept:free-haar) provides $c(K,n)$; $\kappa_n=(n+1)/(n-1)$ accounts for the finite-net approximation.

## Corresponding Lean objects

[KrausChannel.adjointMap](lean:Nonadditivity.Channels.KrausChannel.adjointMap) is the concrete Kraus adjoint. [output_purity_and_entropy_of_certificate](lean:Nonadditivity.Channels.KrausChannel.output_purity_and_entropy_of_certificate) proves the matrix consequence.

[exists_net_linearization](lean:Nonadditivity.StructuredLinearization.exists_net_linearization) builds the finite test polynomial. [exists_explicit_certificate](lean:Nonadditivity.StructuredHaarConsequences.exists_explicit_certificate) performs selection and extension once its expectation premise is supplied. The [prescribed expectation theorem](lean:Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation) supplies that premise in the completed construction.
