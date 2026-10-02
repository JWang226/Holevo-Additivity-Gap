<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Bell-output entropy

## Mathematical statement

For a finite unitary family with $K$ branches, the complementary channel and its conjugate have an explicit Bell-input output with

$$
S_{\mathrm{nats}}(\text{one-block joint output})\le2\ln K-\ln K/K.
$$

For an $n$-block tensor construction, the bound becomes $n(2\ln K-\ln K/K)$.

## Proof idea

The actual output is a matrix assembled from the unitary branch overlaps. The Bell-state correlations expose an entropy deficit. Tensor-product entropy identities assemble the block witness.

The theorem does not require the unitary family to be a favorable random sample. Random realization supplies the other side of the argument: a uniform single-use entropy lower bound.

## How the deficit becomes a gap

The maximum joint entropy is $2n\ln K$, so the deficit is at least $n\ln K/K$. The [switch/Weyl conversion](concept:weyl-switch) turns it into $\chi(T\otimes T)\ge n\log_2K/K$ for two uses of the final channel.

Read the [Bell-input concept](concept:bell-input) for the physical witness and the [construction chapter](guide:construction) for the assembly.
