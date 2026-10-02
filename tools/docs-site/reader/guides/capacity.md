<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# From Holevo information to capacity

## Capacity starts with physical codes

For $m$ uses of a channel, a code assigns each of $M$ messages an input density matrix and decodes with a normalized POVM. Its rate is $\log_2M/m$; its error is the average probability of an incorrect outcome. A rate is achievable when a sequence of such physical codes has vanishing error and eventually attains every strictly smaller rate.

The formal [operationalCapacity](lean:Nonadditivity.Operational.operationalCapacity) is the supremum of achievable rates. It is not defined to be an entropy expression.

## The coding theorem supplies the equality

The [operational coding theorem](result:operational-coding) proves

$$
C(T)=\sup_{m\ge1}\frac{\chi(T^{\otimes m})}{m}
=\lim_{m\to\infty}\frac{\chi(T^{\otimes m})}{m}.
$$

Achievability uses finite output ensembles, physical input lifts, spectral packing, and actual decoders. Applying it to a tensor-power channel and unblocking its codes realizes normalized block Holevo rates.

The converse bounds the number of messages in every finite code by Holevo information plus an explicit error correction. Vanishing error removes the correction at the rate level. Superadditivity of tensor-power Holevo information and the finite dimension bound identify the limit with the supremum.

The exact equality is [operationalCapacity_eq_regularizedHolevoSupremum](lean:Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum). Its proof connects the independently defined code quantity to the entropy quantity.

## Why two uses already imply a capacity gain

Taking $m=2$ gives $C(T)\ge\chi(T\otimes T)/2$. Therefore

$$
C(T)-\chi(T)\ge\frac{\Delta_\chi(T)}2.
$$

For the prescribed channel,

$$
C(T)-\chi(T)\ge\frac{n\delta_K}{2}-2\log_2\frac{n+1}{n-1}.
$$

For fixed $K$ with $\delta_K>0$, the lower bound diverges as $n$ increases. The [growing-K family](result:growing-family-cost) can instead make $\chi(T)$ vanish while capacity diverges.

This says that the long-run coding rate can greatly exceed the single-use Holevo benchmark. It gives a lower bound on capacity, not an exact capacity formula for each constructed channel.

## Keep the two additivity questions distinct

The separation concerns $\chi(T\otimes T)>2\chi(T)$ and $C(T)>\chi(T)$. Additivity of already regularized capacity would ask whether $C(S\otimes T)=C(S)+C(T)$ for distinct channels. The displayed results do not establish a violation of that latter identity.

Indeed, for a fixed channel, the proved blocking and coding results give $C(T^{\otimes m})=mC(T)$. Increasing a regrouping parameter alone also cannot create the persistent linear two-block gap of the changing family: [the normalized fixed-channel gap tends to zero](result:fixed-channel-regrouping).

## What to read next

The [capacity concept](concept:operational-capacity) gives the code definitions and indexing convention. The [capacity-gain result](result:capacity-gain) retains the prescribed dimensions, while [simultaneous separation](result:simultaneous-separation) explains the small-information, large-gain quantifiers.
