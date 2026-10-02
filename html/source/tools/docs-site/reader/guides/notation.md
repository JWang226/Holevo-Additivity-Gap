<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Notation and units

## Information quantities

Unless a formula explicitly says nats, information in this guide is in bits.

| Symbol | Meaning | Formal object |
| --- | --- | --- |
| $\chi(T)$ | Supremum of finite output-ensemble Holevo information | [FiniteQuantumChannel.chi](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.chi) |
| $\chi(T\otimes T)$ | The same optimization over joint inputs to two uses | [chiTwo](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.chiTwo) |
| $\Delta_\chi(T)$ | $\chi(T\otimes T)-2\chi(T)$ | [gap](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.gap) |
| $R_2(T)$ | $\chi(T\otimes T)/(2\chi(T))$, interpreted when $\chi(T)>0$ | [twoUseRatio](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.twoUseRatio) |
| $C(T)$ | Supremum of rates achievable with vanishing decoding error | [operationalCapacity](lean:Nonadditivity.Operational.operationalCapacity) |

## Logs and entropy

The manuscript's base-two logarithm is $\log_2$. Lean's Real.log is $\ln$. [Scalar.log2](lean:Nonadditivity.Scalar.log2) implements $\ln x/\ln2$.

The primitive [vonNeumann entropy](lean:Nonadditivity.Entropy.DensityMatrix.vonNeumann) and [KrausChannel.holevo](lean:Nonadditivity.Channels.KrausChannel.holevo) use nats. [holevoBits](lean:Nonadditivity.Channels.KrausChannel.holevoBits) divides by $\ln2$. This factor must be tracked when passing from a matrix entropy lemma to a channel endpoint.

## Parameters of the main family

| Symbol | Meaning |
| --- | --- |
| $K$ | Integer branch parameter, at least two |
| $n$ | Block parameter used to construct one channel |
| $n_0(K)$ | $\lceil256(1+\ln K)^2\rceil$ |
| $N$ | $\lceil\exp(40(7\ln K+2)n)\rceil$ |
| $\kappa_n$ | $(n+1)/(n-1)$ |
| $a_K$ | $\log_2(1+9/K)$ |
| $\delta_K$ | $\log_2K/K-2a_K$ |
| $q_{\mathrm{in}},q_{\mathrm{out}}$ | Base-two logarithms of input and output dimensions |

The construction parameter $n$ is not the number $m$ of communication uses of the finished channel. In tensor-power Lean interfaces, a natural index $j$ commonly denotes $j+1$ positive uses.

## Parameters inside the Haar proof

$p$ is a moment order. In the one-pair Haar statements, the Lean size parameter is one less than the actual local matrix dimension $D$. Those statements call their parameter $N$, so their matrices have size $N+1$; that local name should be distinguished from the prescribed channel's dimension $N$ in the table above. The symbol $\delta$ in a path estimate is an integer path defect; it is different from the real scalar $\delta_K$ that controls the final gap.

The Hilbert–Schmidt norm is $\|A\|_{\mathrm{HS}}=(\operatorname{Tr}A^\dagger A)^{1/2}$; $\|\cdot\|_{\mathrm{op}}$ is the operator norm. Read the [adjoint-certificate entry](concept:adjoint-certificate) for their role.
