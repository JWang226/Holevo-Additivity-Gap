<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Operational capacity and regularization

## A physical code

A code for $m$ uses and $M$ messages chooses a density matrix $\rho_x$ on the full input tensor power for each message. The receiver uses positive effects $E_x$ with $\sum_xE_x=I$. Its mean success probability is

$$
\frac1M\sum_x\operatorname{Tr}\!\left(E_xT^{\otimes m}(\rho_x)\right).
$$

The error is one minus this value. Encoders may be mixed and entangled across uses, and decoding is an actual POVM.

## Achievable rates

A sequence with error tending to zero achieves rate $R$ if every rate $r<R$ is eventually bounded above by its rates $\log_2M_m/m$. Capacity is the supremum of those achievable rates.

This definition is operational. An entropy expression becomes equal to it only after the [coding theorem](result:operational-coding).

## Why the Holevo quantity is regularized

Applying achievability to a block channel $T^{\otimes m}$ gives rates approaching $\chi(T^{\otimes m})/m$ per physical use. Blocking and padding turn these into code sequences at all sufficiently large lengths.

The converse bounds every vanishing-error code rate by the supremum of normalized block Holevo quantities. Consequently

$$
C(T)=\sup_{m\ge1}\frac{\chi(T^{\otimes m})}{m}.
$$

Superadditivity and the dimension bound also make this a limit. In particular, a two-use witness is enough to certify $C(T)\ge\chi(T\otimes T)/2$.

## Corresponding Lean definitions and theorem

| Mathematical object | Lean object |
| --- | --- |
| Normalized decoder | [POVM](lean:Nonadditivity.Operational.POVM) |
| Physical input/decoder code | [Code](lean:Nonadditivity.Operational.Code) |
| Achievability criterion | [AchievableRate](lean:Nonadditivity.Operational.AchievableRate) |
| Capacity supremum | [operationalCapacity](lean:Nonadditivity.Operational.operationalCapacity) |
| Coding equality | [operationalCapacity_eq_regularizedHolevoSupremum](lean:Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum) |

Lean's positive tensor-power index $j$ represents $j+1$ uses. The construction's block parameter $n$ is a different parameter. See the [capacity chapter](guide:capacity) for the resulting communication advantage and its scope.
