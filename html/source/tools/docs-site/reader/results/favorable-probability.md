<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Favorable-realization probability

## A general probability estimate

Let $f\ge0$ almost everywhere be integrable on a probability space, and let $\varepsilon,\rho>0$. If

$$
\mathbb E f\le(1+\varepsilon/2)\rho,
$$

then

$$
\mathbb P\{f\le(1+\varepsilon)\rho\}
\ge\frac{\varepsilon}{2(1+\varepsilon)}>0.
$$

The expectation bound is therefore enough to guarantee a favorable sample.

## Application to the Haar polynomial

The prescribed polynomial theorem applies this estimate to an actual finite-evaluation operator norm, using its proved integrability and expectation comparison. It retains the support, self-adjointness, coefficient-dimension, and positive free-norm hypotheses.

The event concerns the polynomial norm. The [finite-net construction](concept:adjoint-certificate) makes a favorable test polynomial control all required observables.

## What the guarantee means

This gives positive probability for a specified norm event at a finite size. It is not a claim that every Haar sample works, or an efficient sampling algorithm with a practical parameter size.

The existence endpoint uses sample selection; this additional result quantifies the favorable-event probability.
