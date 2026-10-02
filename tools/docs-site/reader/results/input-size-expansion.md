<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Input-size expansion

## Mathematical statement

For fixed $K\ge2$ along the prescribed family,

$$
q_{\mathrm{in}}(T_{K,n})=
\frac{b_K}{\ln2}n^2+2n\log_2K+1+o(1),
\qquad b_K=40(7\ln K+2).
$$

The remainder tends to zero, including the integer ceiling in $N=\lceil e^{b_Kn}\rceil$.

## Where the terms come from

Taking $\log_2$ of $2N^nK^{2n}$ gives $1+n\log_2N+2n\log_2K$. The local dimension's exponential contributes the quadratic term, Weyl labels contribute the term linear in $n$, and the switch flag contributes one.

The ceiling changes $\log N$ by an exponentially small amount. Multiplication by $n$ still leaves a term tending to zero.

## Why retain the rounding?

The endpoint concerns actual finite index sets, so their dimensions must be integers. Keeping the ceiling connects the asymptotic cost to the same channel supplied by the existence theorem.

The expansion is used in [fixed-K input scaling](result:fixed-k-scaling) and the [growing-family cost calculation](result:growing-family-cost).
