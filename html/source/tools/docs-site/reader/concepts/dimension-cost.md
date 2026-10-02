<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Input and output qubit costs

## Logarithmic dimensions

The guide uses

$$
q_{\mathrm{in}}=\log_2d_{\mathrm{in}},\qquad
q_{\mathrm{out}}=\log_2d_{\mathrm{out}}.
$$

These are logarithmic dimension costs. A literal register of qubits requires their ceilings, changing each cost by less than one. The asymptotic orders are unchanged.

For the prescribed channel, $d_{\mathrm{in}}=2N^nK^{2n}$ and $d_{\mathrm{out}}=K^n$. The input includes the local tensor space, the switch flag, and the Weyl labels.

## Why the distinction matters

At fixed $K$, $\log N$ grows linearly in the construction parameter $n$. Thus

$$
q_{\mathrm{in}}=\Theta_K(n^2),\qquad
q_{\mathrm{out}}=\Theta_K(n).
$$

When $\delta_K>0$, the proved gap is $\Theta_K(n)$. It is therefore output-linear and of order $\sqrt{q_{\mathrm{in}}}$, rather than input-linear.

For the growing-$K$ family, $q_{\mathrm{in}}/K^2\to280/\ln2$. Its information lower bound is expressed through $\sqrt{\log_2q_{\mathrm{in}}}$. This is a square root of the logarithm of the qubit cost, not a square root of the cost itself.

## Bound the information by finite size

The general two-use bound $\chi(T\otimes T)\le2q_{\mathrm{out}}$ is consistent with an output-linear gap. Operational capacity is bounded by both input and output logarithmic dimensions. The unbounded separations vary the channel and its dimensions.

## Corresponding Lean results

[prescribedFamily_output_qubits](lean:Nonadditivity.HaarPrescribedDimension.prescribedFamily_output_qubits) gives the exact output cost. [prescribedFamily_input_size_remainder_tendsto](lean:Nonadditivity.HaarPrescribedDimension.prescribedFamily_input_size_remainder_tendsto) gives the input expansion with integer rounding.

[growingFamily_input_qubits_div_sq_tendsto](lean:Nonadditivity.PrescribedCost.growingFamily_input_qubits_div_sq_tendsto) supplies the growing-family constant. Read the [scaling chapter](guide:scaling) to compare the two regimes.
