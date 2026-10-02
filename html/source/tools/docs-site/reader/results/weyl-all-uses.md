<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Weyl identity at every positive power

## Mathematical statement

For output dimension $d$ and every $m\ge1$, the Weyl extension satisfies

$$
\chi(W(\Phi)^{\otimes m})
=m\log_2d-S_{\min,\mathrm{bits}}(\Phi^{\otimes m}).
$$

The minimum output entropy is an infimum over all joint input states, including entangled ones.

## Proof idea

The tensor Weyl orbit averages an output to the maximally mixed state on the full joint output space. Each conjugated state has the original entropy, so the orbit ensemble realizes the entropy deficit. The general Holevo upper bound gives the reverse direction.

The formal proof tracks tensor indices and channel identities rather than assuming covariance for the whole tensor power. It does not rely on pure-input attainment.

## Capacity consequence

Regularization gives the corresponding operational-capacity identity. The one-use and two-use specializations drive the main channel conversion; the all-use result explains the broader entropy/information relationship.

Lean's index $j$ denotes $j+1$ uses. See [switch and Weyl extensions](concept:weyl-switch) and [the coding theorem](result:operational-coding).
