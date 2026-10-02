<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# The communication problem

## One channel, many possible messages

A sender represents a classical message by a quantum state and sends it through a [finite quantum channel](concept:channels). The receiver sees the output state. Noise can make different messages difficult to distinguish.

For an ensemble of messages with probabilities $p_x$ and inputs $\rho_x$, the output ensemble has Holevo information

$$
\chi(\{p_x,T(\rho_x)\})=
S\!\left(\sum_xp_xT(\rho_x)\right)-\sum_xp_xS(T(\rho_x)).
$$

Here entropy is measured in bits. The channel quantity $\chi(T)$ is the supremum over finite ensembles. It bounds the accessible information of a measurement on one ensemble, and need not equal that ensemble's one-shot accessible information. Its operational role comes from coding over many repetitions.

## What changes with two uses?

Two independent physical uses give the channel $T\otimes T$. Its input need not be a product state: the sender can prepare an entangled state across the two input systems. Optimizing over all such ensembles gives $\chi(T\otimes T)$.

Product ensembles already give at least $2\chi(T)$. Additivity would say that this lower bound is always an equality. The quantity studied here is

$$
\Delta_\chi(T)=\chi(T\otimes T)-2\chi(T).
$$

Positive $\Delta_\chi$ means joint inputs improve the Holevo information beyond the product-ensemble benchmark. The ratio $\chi(T\otimes T)/(2\chi(T))$ measures a relative improvement when $\chi(T)>0$; the difference measures an absolute one.

## What the project proves

The [prescribed-dimension theorem](result:prescribed-dimensions) constructs finite channels with quantitative size and information bounds. Choosing the parameters makes the gap arbitrarily large.

The [simultaneous separation](result:simultaneous-separation) is stronger than an unbounded ratio alone. For every $\varepsilon>0$ and any targets $A,R$, one finite channel satisfies

$$
0<\chi(T)\le\varepsilon,\qquad
C(T)-\chi(T)\ge A,\qquad
\frac{\chi(T\otimes T)}{2\chi(T)}\ge R.
$$

The same channel meets all three requirements. The [operational capacity](concept:operational-capacity) $C(T)$ is defined through actual codes with decoding error tending to zero. The [coding theorem](result:operational-coding) proves

$$
\chi(T)\le \frac{\chi(T\otimes T)}2\le C(T).
$$

Dimensions grow as stronger separations are requested. For each fixed channel, capacity is bounded by the logarithms of its input and output dimensions. There is no claim of arbitrarily large capacity in a fixed finite space.

## The mechanism in one paragraph

The construction makes every single-use output highly mixed, restricting the information of every single-use ensemble. A specific [Bell input](concept:bell-input) nevertheless produces a less mixed joint output for a channel paired with its conjugate. A [switch and Weyl extension](concept:weyl-switch) turns this entropy contrast into the Holevo separation for two uses of one channel. [The construction chapter](guide:construction) develops these steps.

## Connecting this discussion to Lean

The physical object is [FiniteQuantumChannel](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel). Its [chi](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.chi), [chiTwo](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.chiTwo), [gap](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.gap), and [twoUseRatio](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.twoUseRatio) refer to actual Kraus-channel outputs.

Start with the informal [main theorem](result:prescribed-dimensions), follow the [proof route](stage:1), or use the [notation dictionary](guide:notation) when reading an exact statement.
