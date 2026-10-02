<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Qualitative realization

## Mathematical statement

For integers $K\ge2$, $n\ge1$, and every tolerance $\eta>0$, there are a finite channel and an integer $N>0$ with

$$
\begin{aligned}
d_{\mathrm{in}}&=2N^nK^{2n},\qquad d_{\mathrm{out}}=K^n,\\
0<\chi(T)&\le n\log_2(1+9/K)+\eta,\\
\chi(T\otimes T)&\ge n\log_2K/K.
\end{aligned}
$$

The lower two-use bound has no additive tolerance loss.

## A different finite realization

This proof uses a deterministic finite-moment construction and damping, rather than assuming generic Haar strong convergence. A small perturbation of branch weights creates a strict Bell entropy reserve. The damping error is chosen afterward and absorbed within that reserve.

The single-use loss fits the chosen $\eta$ budget. The resulting channel retains positivity of $\chi$ and the exact qualitative two-use lower bound.

## What size information is supplied?

The result supplies finite $N$ and the displayed shape of the dimensions, but not the prescribed exponential formula for $N$. It works at every allowed block length, unlike the quantitative endpoint's threshold restriction.

Read [prescribed dimensions](result:prescribed-dimensions) for the explicit size guarantee, and [the vanishing/diverging sequence](result:small-large-and-sequence) for qualitative consequences.
