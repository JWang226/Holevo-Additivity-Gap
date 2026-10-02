<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Operational coding

## Mathematical statement

For every actual finite Kraus channel, operational capacity in bits equals the supremum, and limit, of normalized positive-power Holevo information:

$$
C(T)=\sup_{m\ge1}\frac{\chi(T^{\otimes m})}{m}
=\lim_{m\to\infty}\frac{\chi(T^{\otimes m})}{m}.
$$

Capacity is defined independently using physical density-matrix encoders, normalized POVM decoders, and vanishing average Born error.

## Proof idea

HSW achievability constructs codes attaining rates below the Holevo information of finite ensembles. Applying it to block channels and unblocking the resulting codes gives the normalized tensor-power rates. A weak converse bounds every finite code's message count by Holevo information plus an explicit error correction.

As error vanishes, this correction vanishes at the rate level. Superadditivity and the finite dimension bound turn the supremum into a limit.

## How it is used here

Taking $m=2$ gives $C(T)\ge\chi(T\otimes T)/2$, hence a capacity gain at least half the two-use gap. The theorem establishes this operational meaning rather than defining capacity to have the desired value.

Read [the capacity chapter](guide:capacity) and [code definitions](concept:operational-capacity). A strong converse at every rate above capacity is outside this endpoint.
