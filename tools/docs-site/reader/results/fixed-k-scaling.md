<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Fixed-K scaling

## Mathematical statement

For a fixed $K\ge2$ with $\delta_K>0$, the prescribed family satisfies

$$
q_{\mathrm{out}}=n\log_2K,\qquad
\Delta_\chi(T_{K,n})=\Theta_K(n)=\Theta_K(\sqrt{q_{\mathrm{in}}}).
$$

The formal estimates give two-sided eventual bounds with constants allowed to depend on $K$.

## Proof idea

The main lower bound is $n\delta_K$ minus a vanishing correction. The general output dimension bound gives $\Delta_\chi\le2n\log_2K$. These produce the linear order in $n$.

The [input expansion](result:input-size-expansion) shows $q_{\mathrm{in}}=\Theta_K(n^2)$. Substituting this scale gives the square-root input order.

## Interpreting “large”

The gap is extensive in output qubits for this fixed-$K$ limit. The prescribed input cost is larger, so the theorem gives a sublinear input-qubit gap. Neither statement asserts optimality of the input dimension.

The [dimension-cost concept](concept:dimension-cost) and [scaling chapter](guide:scaling) explain the distinction and the separate growing-$K$ regime.
