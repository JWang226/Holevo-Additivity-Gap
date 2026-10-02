<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Marked-position and coefficient accounting

## What is repaired

The older middle-run count does not cover all allowed refined paths. Formal counterexamples show the missing configurations. The corrected argument keeps marked positions in the composition sum and proves the resulting weighted accounting.

For a nonempty refined path and moment order $p\ge1$, assume the coefficient polynomial is supported on free-group words of length at most one. The actual operator coefficient bound uses the repaired exponent

$$
\|\text{coefficient sum}\|
\le D^v\,2^{e_1}\,p^{9\delta+11}\,
\|A_{\mathrm{regular}}\|^p.
$$

Here $D$ is local dimension, $v$ counts visited vertices, $e_1$ counts singleton edges, $p$ is moment order, and $\delta$ is [defectTwice](lean:Nonadditivity.HaarPathGraph.Path.defectTwice), twice the graph defect.

## Why it matters

Path-class counts alone do not bound a Haar moment: each class also carries operator coefficients. First- and last-occurrence contractions and the marked-position budget control those coefficients without the invalid run shortcut.

The revised manuscript uses the repaired accounting. The [prescribed realization](result:prescribed-dimensions) and the separate [sharp moment estimate](result:haar-moment-range) use proved replacements.

The exact declarations below distinguish the counterexamples, the marked-sum estimate, and the coefficient theorem.
