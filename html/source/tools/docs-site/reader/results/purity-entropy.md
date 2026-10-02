<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Purity and entropy from the adjoint

## Mathematical statement

Let $T$ be an actual Kraus channel with output dimension $d$ and a nonnegative certificate constant $t$. Suppose every traceless Hermitian $A$ satisfies $\|T^*(A)\|_{\mathrm{op}}\le t\|A\|_{\mathrm{HS}}$. Then every input density matrix $\rho$ obeys

$$
\begin{aligned}
\operatorname{Tr}T(\rho)^2&\le1/d+t^2,\\
S_{\mathrm{nats}}(T(\rho))&\ge\ln d-\ln(1+dt^2).
\end{aligned}
$$

The primitive theorem uses nats; division by $\ln2$ gives the bit-valued statement.

## Proof idea

Center the output at $I/d$ and apply the certificate to that centered observable. Concrete Kraus trace duality bounds its Hilbert–Schmidt length by $t$. The order-two Rényi lower bound then converts purity to von Neumann entropy.

All matrix positivity and duality conditions are proved for the actual channel. No separate assumption that its outputs behave like valid density matrices is needed.

## Role in the main theorem

The estimate bounds every output, hence every single-use ensemble. Combined with the [Weyl extension](concept:weyl-switch), it becomes the single-use Holevo upper bound. See [the certificate concept](concept:adjoint-certificate).
