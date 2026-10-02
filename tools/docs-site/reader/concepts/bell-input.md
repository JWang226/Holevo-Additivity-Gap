<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# The Bell-state witness

## One concrete entangled input

On two equal $D$-dimensional input spaces, the Bell vector is

$$
|\Omega_D\rangle=\frac1{\sqrt D}\sum_{j=1}^D|j\rangle\otimes|j\rangle.
$$

Its density matrix is a valid joint input. Unitary-conjugate correlations, expressed by $(U\otimes\bar U)|\Omega_D\rangle=|\Omega_D\rangle$, make it especially useful for a channel paired with its conjugate.

## An entropy deficit for the joint output

The complementary channel records branch overlaps of the unitary family. With the Bell input, correlations between matching branches create a component that lowers the entropy relative to the maximum possible entropy.

For the $n$-block complementary channel and its conjugate, the [proved bound](result:bell-entropy) is

$$
S_{\mathrm{nats}}(\text{joint output})\le
n(2\ln K-\ln K/K).
$$

The joint output dimension is $K^{2n}$, so the deficit from maximum entropy is at least $n\ln K/K$. The theorem holds for any finite local unitary family with the required branch structure. Randomness enters the separate uniform single-use estimate.

## Its place in the final theorem

A low-entropy joint output alone is not yet a Holevo lower bound for two copies of the desired final channel. The [switch channel](concept:weyl-switch) provides the channel/conjugate branches, and the Weyl extension supplies an orbit ensemble with maximally mixed average.

The deficit then yields $\chi(T\otimes T)\ge n\log_2K/K$. The input is an explicit witness, whereas the single-use entropy estimate must hold for every input.

## Corresponding Lean results

[complementary_bell_entropy_le](lean:Nonadditivity.BellOutput.complementary_bell_entropy_le) proves the one-block output estimate. [block_complementary_bell_entropy_le](lean:Nonadditivity.BlockBell.block_complementary_bell_entropy_le) assembles the tensor block witness. The [construction chapter](guide:construction) connects them to the converted channel bounds.
