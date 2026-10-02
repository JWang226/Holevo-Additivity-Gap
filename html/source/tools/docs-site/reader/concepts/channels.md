<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Finite quantum channels

## States and physical maps

A density matrix is a positive semidefinite complex matrix with trace one. A finite quantum channel is a completely positive, trace-preserving map. In this library it is given concretely by rectangular Kraus matrices:

$$
T(\rho)=\sum_a V_a\rho V_a^\dagger,\qquad
\sum_a V_a^\dagger V_a=I.
$$

The completeness equation gives trace preservation; the Kraus formula gives positivity even after adding an arbitrary finite ancilla. Thus the constructed object is a physical map, not a list of numbers asserted to behave like channel information.

## A channel and its complement

An isometry $V$ sends an input into an output system and an environment. Tracing out the environment gives one channel; tracing out the output gives its complementary channel.

For $K$ unitaries $U_i$ on a local space, the isometry

$$
V\psi=\frac1{\sqrt K}\sum_{i=1}^K U_i\psi\otimes|i\rangle
$$

gives a complementary output in the $K$-dimensional branch space. Its matrix entries contain the overlaps $\operatorname{Tr}(U_i\rho U_j^\dagger)/K$. This connects output observables to polynomials in the unitary family. Tensor blocks make the branch output dimension $K^n$.

The [uniform adjoint estimate](concept:adjoint-certificate) controls these outputs. The [Bell witness](concept:bell-input) exploits correlations between this channel and its complex conjugate.

## Two uses and joint states

The channel $T\otimes T$ acts on all density matrices of the joint input space, including entangled ones. Product input states are only a subset. This is the domain used by the two-use Holevo optimization.

## Corresponding Lean objects

| Informal object | Exact formal object |
| --- | --- |
| Positive, trace-one state | [DensityMatrix](lean:Nonadditivity.Entropy.DensityMatrix) |
| Rectangular Kraus family and completeness | [KrausChannel](lean:Nonadditivity.Channels.KrausChannel) |
| Kraus matrix sum | [KrausChannel.map](lean:Nonadditivity.Channels.KrausChannel.map) |
| Complementary map | [KrausChannel.complementary](lean:Nonadditivity.Channels.KrausChannel.complementary) |
| Joint channel | [KrausChannel.tensor](lean:Nonadditivity.Channels.KrausChannel.tensor) |
| Packaged finite channel with its actual map | [FiniteQuantumChannel](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel) |

Read [the construction](guide:construction) to see how the local maps become the final channel.
