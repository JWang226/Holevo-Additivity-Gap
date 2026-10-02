<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# What grows, and what it costs

## Fixed K: a large absolute gap

Fix $K\ge2$ with $\delta_K>0$, where

$$
\delta_K=\frac{\log_2K}{K}-2\log_2(1+9/K).
$$

Let the block parameter $n$ increase. The [prescribed channels](result:prescribed-dimensions) obey

$$
\Delta_\chi(T_{K,n})\ge n\delta_K-4\log_2\frac{n+1}{n-1}.
$$

The correction tends to zero. The upper bound $\Delta_\chi(T)\le2\log_2d_{\mathrm{out}}$ gives a matching order bound, so $\Delta_\chi(T_{K,n})=\Theta_K(n)$. The same argument gives an unbounded capacity gain.

The sufficient condition $\ln K>18$ implies $\delta_K>0$ by $\ln(1+x)\le x$. It is a sufficient parameter choice, not a claim about the smallest useful $K$ or the actual optimal gap.

## Output-linear does not mean input-linear

Use the logarithmic dimension costs $q_{\mathrm{in}}=\log_2d_{\mathrm{in}}$ and $q_{\mathrm{out}}=\log_2d_{\mathrm{out}}$. For the constructed channel,

$$
\begin{aligned}
q_{\mathrm{out}}&=n\log_2K,\\
q_{\mathrm{in}}&=\frac{40(7\ln K+2)}{\ln2}\,n^2
+2n\log_2K+1+o(1).
\end{aligned}
$$

Thus, at fixed $K$ with positive $\delta_K$, the gap is linear in output cost and of order $\sqrt{q_{\mathrm{in}}}$ in input cost. The [input expansion](result:input-size-expansion) includes the ceiling in $N$ and proves that its remaining error tends to zero.

The [guaranteed output fraction](result:guaranteed-gap-fraction) satisfies

$$
\liminf_n\frac{\Delta_\chi(T_{K,n})}{q_{\mathrm{out}}}
\ge r_K=\frac1K-\frac{2\ln(1+9/K)}{\ln K}.
$$

This is a proved lower guarantee. It is not an equality for the actual gap.

## Growing K: vanishing one-use information

For a different family, choose $n_K=\lceil K/\sqrt{\ln K}\rceil$ and let $K$ increase. This rounded length eventually meets the prescribed theorem's threshold. The information bounds then imply

$$
\chi(T_K)=\Theta\!\left(\frac1{\sqrt{\ln K}}\right),\qquad
\frac{\chi(T_K\otimes T_K)}2=\Omega(\sqrt{\ln K}),\qquad
C(T_K)=\Omega(\sqrt{\ln K}).
$$

The first two regimes use different parameter limits: fixed $K$, growing $n$ gives the output-linear gap; growing $K$ with the specified $n_K$ gives vanishing single-use information. These statements should not be combined into one limit without fixing the family.

For the growing family, [the formal input-cost result](result:growing-family-cost) proves

$$
\frac{q_{\mathrm{in}}(T_K)}{K^2}\longrightarrow\frac{280}{\ln2}.
$$

Consequently $\chi(T_K)$ is of order $1/\sqrt{\log_2q_{\mathrm{in}}}$, while both two-use information per use and capacity have positive lower bounds of order $\sqrt{\log_2q_{\mathrm{in}}}$.

## Why varying the channel matters

These families change the channel and its dimensions. For one fixed channel $\Phi$, regularization instead gives

$$
\frac{\chi(\Phi^{\otimes2m})-2\chi(\Phi^{\otimes m})}{m}\longrightarrow0.
$$

The [fixed-channel regrouping theorem](result:fixed-channel-regrouping) makes this distinction formal. The large family gap is not obtained simply by renaming blocks of one fixed channel.

## Lean landmarks

Read [prescribedFamily_gap_linear_bounds](lean:Nonadditivity.HaarPrescribedDimension.prescribedFamily_gap_linear_bounds), [prescribed_gap_sqrt_input_bounds](lean:Nonadditivity.HaarPrescribedDimension.prescribed_gap_sqrt_input_bounds), and [growingFamily_input_qubits_div_sq_tendsto](lean:Nonadditivity.PrescribedCost.growingFamily_input_qubits_div_sq_tendsto). The [dimension-cost concept](concept:dimension-cost) explains the logarithmic cost convention.
