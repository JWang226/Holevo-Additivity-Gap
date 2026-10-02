<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Vanishing and diverging information

## Mathematical statements

For every $\varepsilon>0$ and real target $R$, an actual finite channel has

$$
0<\chi(T)\le\varepsilon,\qquad
\chi(T\otimes T)/2\ge R.
$$

The library also constructs a sequence with

$$
\chi(T_K)\longrightarrow0,\qquad
\chi(T_K\otimes T_K)/2\longrightarrow\infty,\qquad
C(T_K)\longrightarrow\infty.
$$

## Proof idea

Choose a growing branch parameter and a block length of order $K/\sqrt{\ln K}$. The qualitative upper bound is then of order $1/\sqrt{\ln K}$, while the two-use lower bound is of order $\sqrt{\ln K}$. The [coding theorem](result:operational-coding) transfers the latter to capacity.

## Which family is being described?

These endpoints use the deterministic qualitative realization. The [prescribed growing family](result:growing-family-cost) additionally tracks explicit input dimensions and cost bounds.

Each individual channel is finite. The dimensions vary along the sequence, allowing the information per use to diverge without contradicting finite-dimensional capacity bounds.
