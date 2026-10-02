<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Simultaneous separation

## Mathematical statement

For every $\varepsilon>0$ and any real targets $A,R$, there is one actual finite quantum channel satisfying

$$
0<\chi(T)\le\varepsilon,\qquad
C(T)-\chi(T)\ge A,\qquad
\frac{\chi(T\otimes T)}{2\chi(T)}\ge R.
$$

All three inequalities concern the same witness.

## Why this is stronger than a ratio alone

Shrinking a denominator can make a ratio large while the absolute information advantage stays small. This theorem simultaneously makes the single-use information small and the capacity advantage large. Positivity makes the ratio meaningful.

## Proof idea

Use a finite-channel family whose single-use information tends to zero and whose two-use information per use diverges. The [coding theorem](result:operational-coding) bounds capacity below by that two-use quantity. Eventually the capacity difference and ratio exceed the chosen targets while the one-use information lies below the tolerance.

The channel depends on the targets, and its dimensions can grow. The [cost-controlled growing family](result:growing-family-cost) separately quantifies an input-size guarantee.
