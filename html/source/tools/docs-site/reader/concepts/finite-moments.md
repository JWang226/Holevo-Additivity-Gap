<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Haar moments and path counting

## Why use moments?

For a finite self-adjoint matrix, an even trace moment controls its largest eigenvalue in magnitude, with a dimension factor. Integrating these moments over Haar unitary matrices therefore provides a route to an expected operator norm bound.

The proof replaces one Haar pair at a time with its free counterpart and tracks the error through all tensor legs. This requires controlling the actual mixed-word trace expansion, not just a qualitative convergence claim.

## Paths organize the trace expansion

Exploration paths encode which identifications occur in a word contribution. The integer parameter $\delta$ measures its combinatorial departure from the leading behavior. Here $\delta$ means Lean's [defectTwice](lean:Nonadditivity.HaarPathGraph.Path.defectTwice): twice the graph defect, equal to path length plus singleton-edge count minus twice the visited-vertex count.

The revised proof retains the extra endpoint event:

$$
\#\{\text{important exploration times}\}\le\delta+2.
$$

Operator coefficient contraction separately gives the repaired moment exponent $9\delta+11$. Here $\delta$ is a path defect, not the final gap coefficient $\delta_K$.

The [important-time correction](result:correction-important-times) and [marked-position correction](result:correction-middle-runs) explain the counterexamples and replacements.

## Two dimension thresholds

The prescribed-channel assembly uses a one-pair trace comparison at actual local dimension $D\ge2^{80}p^{80}$, for moment order $p\ge2$. In these one-pair statements, the Lean size parameter is $D-1$.

A separate weighted chronological counting route recovers the stronger endpoint at $D\ge2^{32}p^{80}$. Both compare the real normalized Haar trace moment with the real free trace moment plus a controlled $D^{-1/2}$ error.

The sharper estimate is proved for the finite matrix/free-factor coefficient representations used here. It is not a claim covering every abstract traced algebra.

## Corresponding Lean results

[card_importantTimes_le](lean:Nonadditivity.HaarPathGraph.Path.card_importantTimes_le) is the corrected exploration count.

[coefficient_bound](lean:Nonadditivity.HaarOperatorPathBridge.coefficient_bound), [the prescribed one-pair bound](lean:Nonadditivity.HaarPrescribedDimension.onePairTraceBound), [the sharp one-pair bound](lean:Nonadditivity.HaarSharpBound.onePairTraceBound), and [iteratedExpectation_le](lean:Nonadditivity.HaarIteratedMoments.iteratedExpectation_le) expose the implemented estimates.
