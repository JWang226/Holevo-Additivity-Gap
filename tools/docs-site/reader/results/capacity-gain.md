<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Prescribed capacity gain

## Mathematical statement

Under the prescribed-channel hypotheses, the same channel and dimensions satisfy

$$
C(T)-\chi(T)\ge\frac{n\delta_K}{2}
-2\log_2\frac{n+1}{n-1}.
$$

For fixed $K\ge2$ with $\delta_K>0$, the gain along the prescribed family tends to infinity.

## Proof idea and interpretation

The [coding theorem](result:operational-coding) gives $C(T)\ge\chi(T\otimes T)/2$. Insert the [main theorem's](result:prescribed-dimensions) two-use lower bound and subtract its single-use upper bound.

The result preserves the exact input/output dimensions and positive same-witness $\chi$. It gives a lower bound on the actual capacity advantage, not an exact capacity formula. The diverging conclusion requires positive $\delta_K$; the finite inequality remains meaningful for all allowed parameters.

Read [the capacity chapter](guide:capacity) to distinguish this advantage from additivity of regularized capacity for distinct channels.
