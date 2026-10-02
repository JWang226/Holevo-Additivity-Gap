<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Corrected exploration count

## The replacement estimate

For a nonempty exploration path, write $\delta$ for the integer [defectTwice](lean:Nonadditivity.HaarPathGraph.Path.defectTwice), twice its graph defect. Then

$$
\#\{\text{important exploration times}\}\le\delta+2.
$$

The extra endpoint event must remain in the encoding budget.

## Why the change is necessary

The library contains a literal path violating the older intermediate count, together with a path attaining the repaired bound. This rules out repairing the argument merely by restating the smaller budget.

The revised manuscript incorporates the replacement. The correction concerns an intermediate proof estimate, while the final prescribed channel dimensions remain as displayed in the main theorem.

## Downstream use

Encoding important times gives defect-class counts. Retaining chronological positions also gives the weighted count used by the sharp Haar route. Those counts feed [the moment comparison](result:haar-moment-range).

Read [Haar moments](concept:finite-moments) for the role of path defect and [the second correction](result:correction-middle-runs) for coefficient accounting.
