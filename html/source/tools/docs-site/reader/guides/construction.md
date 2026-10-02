<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# How the channel is built

## The target inequalities

Choose integers $K\ge2$ and $n\ge n_0(K)$, and define

$$
\begin{aligned}
n_0(K)&=\left\lceil256(1+\ln K)^2\right\rceil,\\
b_K&=40(7\ln K+2),\qquad N=\left\lceil e^{b_Kn}\right\rceil,\\
\kappa_n&=\frac{n+1}{n-1},\qquad a_K=\log_2(1+9/K).
\end{aligned}
$$

The [main theorem](result:prescribed-dimensions) gives one channel with input dimension $2N^nK^{2n}$, output dimension $K^n$, and

$$
\begin{aligned}
2n/K\le\chi(T)&\le na_K+2\log_2\kappa_n,\\
\chi(T\otimes T)&\ge n\log_2K/K.
\end{aligned}
$$

The first lower bound also guarantees positive single-use information. The construction is an existence proof with explicit sufficient dimensions; it does not assert an efficient numerical sampler or an optimal size.

## First make every output highly mixed

For a base block channel $\Phi$ with output dimension $d=K^n$, prove a [uniform adjoint certificate](concept:adjoint-certificate):

$$
\|\Phi^*(A)\|_{\mathrm{op}}\le t\|A\|_{\mathrm{HS}}
\quad\text{for every traceless Hermitian }A.
$$

Trace duality lets us apply this bound to the centered output density matrix. It implies

$$
\operatorname{Tr}\Phi(\rho)^2\le \frac1d+t^2,\qquad
S_{\mathrm{nats}}(\Phi(\rho))\ge\ln d-\ln(1+dt^2)
$$

for every input $\rho$. These are [proved matrix inequalities](result:purity-entropy), including outputs with zero eigenvalues. Uniformity matters: a single exceptional low-entropy input would defeat a minimum-output-entropy lower bound.

## Where the certificate comes from

The [free-operator comparison](result:free-collins-youn) supplies

$$
c(K,n)^2=\frac{(1+9/K)^n-1}{K^n}.
$$

The finite construction achieves $t=\kappa_n c(K,n)$. To obtain one realization that controls all observables, first use a finite net of normalized traceless Hermitian matrices. Linearization encodes its many tests into one self-adjoint polynomial. An expectation comparison with the free model then supplies a favorable Haar sample, and the net estimate extends to the whole sphere.

The [Haar moment argument](concept:finite-moments) tracks every dimension and error factor. It uses corrected exploration counts and coefficient estimates. The channel assembly uses the proved one-pair estimate with local dimension $D\ge2^{80}p^{80}$. A separate sharper result has threshold $D\ge2^{32}p^{80}$; it is a distinct formal endpoint, not an additional premise of this assembly.

Read the [certificate result](result:prescribed-norm-certificate) and [free/Haar comparison](concept:free-haar) for the finite realization step.

## Then use a Bell input

High entropy for all single-use outputs does not force high entropy for every joint output. For the complementary block channel and its conjugate, a tensor product of Bell states gives

$$
S_{\mathrm{nats}}(\text{joint output})
\le n(2\ln K-\ln K/K).
$$

The [Bell estimate](result:bell-entropy) holds for the actual channel output. Its deficit from $2n\ln K$ is the ingredient that survives as the two-use information lower bound.

## Convert the entropy contrast to information

The [switch](concept:weyl-switch) places the channel and its conjugate into branches of one channel. Two uses can select the two branches needed by the Bell witness. The Weyl extension averages a unitary orbit to the maximally mixed state, turning minimum output entropy into a Holevo quantity.

The [converted-channel bounds](lean:Nonadditivity.BlockConstruction.block_converted_bounds_of_certificate), initially in nats, become

$$
\chi(T)\le na_K+2\log_2\kappa_n,\qquad
\chi(T\otimes T)\ge n\log_2 K/K.
$$

For the upper bound, the certificate gives the factor $1+\kappa_n^2((1+9/K)^n-1)\le\kappa_n^2(1+9/K)^n$. Taking its base-two logarithm explains the correction $2\log_2\kappa_n$.

Subtracting twice the upper bound yields

$$
\Delta_\chi(T)\ge n\delta_K-4\log_2\kappa_n,\qquad
\delta_K=\frac{\log_2K}{K}-2\log_2(1+9/K).
$$

If $\delta_K>0$, this grows linearly with $n$. [The scaling chapter](guide:scaling) explains its resource cost.

## Formal landmarks

The endpoint is [exists_prescribed_channel_with_lower_bound](lean:Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound). The main analytic input is [explicitHaarExpectation](lean:Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation), and the uniform-selection step is [exists_explicit_certificate](lean:Nonadditivity.StructuredHaarConsequences.exists_explicit_certificate). The latter accepts an expectation premise; the final assembler discharges it.

The [interactive map](site:dependencies.html) follows actual stored-proof references. It therefore distinguishes a theorem proving an ingredient from another theorem that accepts that ingredient as a hypothesis.
