<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Holevo information and the two-use gap

## An ensemble entropy difference

An ensemble $\{p_x,\sigma_x\}$ has average state $\bar\sigma=\sum_xp_x\sigma_x$. Its Holevo information in bits is

$$
\chi(\{p_x,\sigma_x\})=S(\bar\sigma)-\sum_xp_xS(\sigma_x).
$$

It measures the entropy difference associated with the classical preparation label. Every measurement's classical mutual information about that label is bounded by this quantity. Equality for a single measurement is not required.

For a channel $T$, optimize over finite ensembles of states in its actual output range. Each such output has an input preimage, so this is the channel ensemble optimization.

## Why joint inputs can change the answer

Product ensembles give

$$
\chi(S\otimes T)\ge\chi(S)+\chi(T).
$$

The two-use optimization also allows entangled inputs. The project quantifies how much larger it can be for two copies of one channel:

$$
\Delta_\chi(T)=\chi(T\otimes T)-2\chi(T),\qquad
R_2(T)=\frac{\chi(T\otimes T)}{2\chi(T)}.
$$

The ratio is useful only with a positive denominator. The formal endpoints include a positive same-channel lower bound or an explicit $\chi(T)>0$ condition.

## Difference versus ratio

A large ratio can come from a tiny denominator without a large absolute advantage. The [simultaneous theorem](result:simultaneous-separation) controls both: one channel has tiny positive $\chi$, a prescribed large capacity gain, and a prescribed large ratio.

Operational capacity is related by $\chi(T)\le\chi(T\otimes T)/2\le C(T)$. Read the [capacity chapter](guide:capacity) for the coding theorem behind the last inequality.

## Corresponding Lean objects

[Ensemble.information](lean:Nonadditivity.StateEnsembles.Ensemble.information) is the entropy difference in nats. [StateEnsembles.quantity](lean:Nonadditivity.StateEnsembles.quantity) is the supremum over finite ensembles in a set of output states. [KrausChannel.holevoBits](lean:Nonadditivity.Channels.KrausChannel.holevoBits) converts the channel quantity to bits.

The [gap](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.gap) and [twoUseRatio](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.twoUseRatio) definitions use the same packaged finite channel and its actual tensor square.
