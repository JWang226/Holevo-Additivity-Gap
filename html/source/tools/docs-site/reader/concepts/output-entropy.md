<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Minimum output entropy and purity

## Why highly mixed outputs limit information

For output dimension $d$, entropy never exceeds $\log_2d$. If every output has entropy at least $s$, every output ensemble satisfies

$$
\chi(\{p_x,T(\rho_x)\})\le\log_2d-s.
$$

Taking the ensemble supremum preserves the bound. The minimum output entropy is the infimum over all input density matrices:

$$
S_{\min}(T)=\inf_\rho S(T(\rho)).
$$

Thus $\chi(T)\le\log_2d-S_{\min}(T)$. This inequality need not be an equality for an arbitrary channel. The [Weyl extension](concept:weyl-switch) is what makes an exact equality available.

## Purity is an easier intermediate quantity

For a state $\sigma$, purity is $\operatorname{Tr}\sigma^2$. It is $1/d$ for the maximally mixed state and one for a pure state. The entropy estimate

$$
S(\sigma)\ge-\log_2\operatorname{Tr}\sigma^2
$$

turns a uniform purity upper bound into an entropy lower bound. Zero eigenvalues are handled with the usual $0\log0=0$ convention.

The [adjoint certificate](concept:adjoint-certificate) gives $\operatorname{Tr}T(\rho)^2\le1/d+t^2$ for every input, hence

$$
S(T(\rho))\ge\log_2d-\log_2(1+dt^2).
$$

This is the single-use side of the construction. The [Bell input](concept:bell-input) supplies the opposite direction for a selected joint output.

## Corresponding Lean objects

[DensityMatrix.purity](lean:Nonadditivity.Entropy.DensityMatrix.purity) and [vonNeumann](lean:Nonadditivity.Entropy.DensityMatrix.vonNeumann) are spectral matrix quantities. The entropy field uses nats. [vonNeumann_ge_neg_log_purity](lean:Nonadditivity.Entropy.DensityMatrix.vonNeumann_ge_neg_log_purity) proves the primitive inequality.

[KrausChannel.minimumEntropy](lean:Nonadditivity.Channels.KrausChannel.minimumEntropy) uses an infimum over the actual output range; no pure-input attainment is assumed. [output_purity_and_entropy_of_certificate](lean:Nonadditivity.Channels.KrausChannel.output_purity_and_entropy_of_certificate) discharges the matrix duality requirements.
