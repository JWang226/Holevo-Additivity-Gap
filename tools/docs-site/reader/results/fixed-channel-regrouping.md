<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Fixed-channel regrouping

## Mathematical statement

For any fixed finite channel $\Phi$,

$$
\frac{\chi(\Phi^{\otimes2m})-2\chi(\Phi^{\otimes m})}{m}
\longrightarrow0.
$$

This concerns two blocks of $m$ uses of the same fixed channel.

## Proof idea

Set $a_m=\chi(\Phi^{\otimes m})/m$. Superadditivity and the finite dimension bound give a regularized limit. The displayed expression is exactly $2(a_{2m}-a_m)$, which tends to zero because both subsequences have the same limit.

The proof of this entropy limit does not require defining the limit operationally; the [coding theorem](result:operational-coding) identifies it with capacity.

## Why it matters for the construction

A persistent linear gap cannot be obtained just by regrouping uses of one fixed channel. The [prescribed family](result:fixed-k-scaling) changes the channel and its local dimensions as its construction parameter grows.

The theorem says the regrouped gap is sublinear in $m$. It does not require the unnormalized gap itself to converge to zero.
