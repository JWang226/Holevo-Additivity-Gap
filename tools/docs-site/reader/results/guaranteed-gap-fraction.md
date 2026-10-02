<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Guaranteed gap fraction

## Mathematical statement

The prescribed family satisfies

$$
\liminf_n\frac{\Delta_\chi(T_{K,n})}{q_{\mathrm{out}}(T_{K,n})}
\ge r_K=\frac1K-\frac{2\ln(1+9/K)}{\ln K}.
$$

For real $K>1$, the scalar expansion has an explicit remainder:

$$
0\le r_K-\frac{1-18/\ln K}{K}
\le\frac{162}{K^2\ln K}.
$$

## Meaning of the fraction

If $\delta_K>0$, then $r_K>0$: the proved gap occupies a positive fraction of output-qubit cost at fixed $K$. The guarantee decreases with the large-$K$ scale; the theorem does not claim a uniform positive fraction as $K$ grows.

## Proof idea

Divide the main gap lower bound by $n\log_2K$ and let the finite-size correction vanish. The scalar identity cancels the base conversion factors. Elementary bounds on $\ln(1+9/K)$ give the remainder estimate.

This is a lower guarantee, not an exact value of the channel's gap fraction. See [the scaling chapter](guide:scaling).
