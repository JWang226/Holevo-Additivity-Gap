<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Switch channels and Weyl extensions

## Put the channel and its conjugate in one map

The entropy witness first compares $\Phi\otimes\bar\Phi$. A switch channel has an input flag selecting either $\Phi$ or $\bar\Phi$, with the same output space. The flag is not retained in the output.

A single-use switched output is a mixture of branch outputs. Entropy concavity preserves the branch lower bound. For two uses, fixed opposite flags select exactly the channel/conjugate pair needed by the Bell input.

This converts a paired-channel construction into a statement about two uses of one channel.

## Make the ensemble average maximally mixed

For a channel $\Psi$ with $d$-dimensional output, a Weyl extension accepts an extra input label for one of $d^2$ Weyl conjugations. Uniformly averaging the orbit of any output state gives $I/d$, while conjugation preserves that state's entropy.

An orbit ensemble therefore has Holevo information $\log_2d-S(\sigma)$. Taking the infimum of output entropies proves

$$
\chi(W(\Psi))=\log_2d-S_{\min}(\Psi).
$$

The ordinary Holevo upper bound supplies the reverse inequality. This argument uses an infimum; it need not assume that a pure input attains the minimum.

## The identity survives arbitrary positive powers

The formal [all-use theorem](result:weyl-all-uses) permits entangled inputs across the tensor factors:

$$
\chi(W(\Psi)^{\otimes m})=m\log_2d-S_{\min}(\Psi^{\otimes m}),
\qquad m\ge1.
$$

The switch flag contributes a factor two to the input dimension. The Weyl label contributes $d^2=K^{2n}$. Neither enlarges the final output dimension $K^n$; together they explain the main theorem's input dimension $2N^nK^{2n}$.

## Corresponding Lean objects

[KrausChannel.switch](lean:Nonadditivity.Channels.KrausChannel.switch) defines the branch map. [weylExtension_holevo](lean:Nonadditivity.Channels.KrausChannel.weylExtension_holevo) is the one-use equality.

[positiveTensorPower_weylExtension_holevoBits](lean:Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits) proves the bit-valued positive-power identity. [block_converted_bounds_of_certificate](lean:Nonadditivity.BlockConstruction.block_converted_bounds_of_certificate) combines the adjoint and Bell inputs for the final channel.
