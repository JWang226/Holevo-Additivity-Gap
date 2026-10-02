<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Prescribed dimensions

## Mathematical statement

Let $K\ge2$ and $n\ge\lceil256(1+\ln K)^2\rceil$ be integers. Put $N=\lceil\exp(40(7\ln K+2)n)\rceil$ and $\kappa_n=(n+1)/(n-1)$. There is one finite CPTP channel with

$$
d_{\mathrm{in}}=2N^nK^{2n},\qquad d_{\mathrm{out}}=K^n,
$$

and the bit-valued bounds

$$
\begin{aligned}
\frac{2n}{K}\le\chi(T)&\le n\log_2(1+9/K)+2\log_2\kappa_n,\\
\chi(T\otimes T)&\ge\frac{n\log_2K}{K},\\
\Delta_\chi(T)&\ge n\delta_K-4\log_2\kappa_n,
\end{aligned}
$$

where $\delta_K=\log_2K/K-2\log_2(1+9/K)$.

## Why it matters

The dimensions and information bounds concern the same actual channel. For fixed $K$ with $\delta_K>0$, the gap grows linearly with $n$. The theorem also retains a positive single-use lower bound, so the associated information ratio has a nonzero denominator.

The dimension is a sufficient guarantee, with no claim of optimality.

## Proof idea

A finite Haar realization gives a [uniform adjoint certificate](concept:adjoint-certificate). That certificate bounds every output's purity and entropy. A [Bell input](concept:bell-input) gives a low-entropy joint output for the channel/conjugate pair. The [switch/Weyl conversion](concept:weyl-switch) produces the single-use upper and two-use lower bounds.

The analytic inputs are discharged in the final endpoint. [The construction chapter](guide:construction) shows the formulas and the finite-size error budget.
