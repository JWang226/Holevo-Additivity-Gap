<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Two-use ratio

## Mathematical statement

For each fixed integer $K\ge2$, the prescribed family has

$$
\liminf_{n\to\infty}
\frac{\chi(T_{K,n}\otimes T_{K,n})}{2\chi(T_{K,n})}
\ge 1+\frac{\delta_K}{2a_K}
\ge\frac{\ln K}{18},
$$

where $a_K=\log_2(1+9/K)$.

## Why the order of limits matters

The limit inferior first takes $n$ to infinity with $K$ fixed. A sufficiently large choice of $K$ makes the lower ratio guarantee as large as desired. The formal channels have positive single-use information, so the ratio is well-defined.

## Proof idea

Divide the two-use lower bound by twice the single-use upper bound. The correction $2\log_2\kappa_n$ is negligible compared with $n$, yielding the first expression. The inequality $\ln(1+9/K)\le9/K$ gives the displayed simpler guarantee.

A large ratio alone need not imply a large absolute gap. [Simultaneous separation](result:simultaneous-separation) controls both a capacity difference and this ratio for one witness.
