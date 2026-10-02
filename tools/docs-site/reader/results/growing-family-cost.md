<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Growing-family cost

## The same explicit family

Choose $n_K=\lceil K/\sqrt{\ln K}\rceil$ and use the prescribed channel family. This length eventually exceeds the construction threshold. The formal results track the actual chosen finite channels and their integer-rounded dimensions.

$$
\frac{q_{\mathrm{in}}(T_K)}{K^2}\longrightarrow\frac{280}{\ln2},
\qquad
\chi(T_K)\longrightarrow0.
$$

The single-use quantity has positive two-sided bounds of order $1/\sqrt{\log_2q_{\mathrm{in}}}$.

## Lower bounds for entangled information and capacity

Let $L=\sqrt{2/\ln2}$. Eventually,

$$
\frac{\chi(T_K\otimes T_K)}2,\ C(T_K)
\ \ge\ \frac{\sqrt{\log_2q_{\mathrm{in}}(T_K)}}{8\ln2\,L}.
$$

Thus two-use information per use and operational capacity diverge while single-use information vanishes.

## Proof idea

The prescribed bounds at $n_K$ give the information scales in $K$. The exact input dimension gives $q_{\mathrm{in}}=\Theta(K^2)$. Comparing $\sqrt{\log_2q_{\mathrm{in}}}$ with $\sqrt{\ln K}$ transfers the estimates to the physical size parameter.

The square root is applied to the logarithm of input-qubit cost. This differs from the fixed-$K$ square-root-of-input-cost gap. Read [the scaling chapter](guide:scaling) for both limits.
