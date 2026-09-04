# ChartLipschitz

## Goal

Provide the missing intrinsic-to-coordinate local Lipschitz direction for a
canonical manifold chart.  Mathlib already supplies the converse local bound
for the inverse chart.

## Route

The centered chart derivative is bounded on a neighborhood.  A smaller
intrinsic ball is chosen inside that neighborhood.  For two points in the
smaller ball, a path of length less than twice their intrinsic distance stays
inside the derivative-controlled neighborhood.  Integrating the fully applied
chart derivative along this path gives the Lipschitz bound.  The zero-distance
case uses topological inseparability and continuity of the chart, so no extra
separation assumption is introduced.

`extChart_lip` transfers the centered estimate to a fixed canonical chart by
factoring through the centered chart at each point.  The coordinate-change map
is `C¹` on the model range, hence locally Lipschitz there.  Intersecting the two
local neighborhoods and composing their estimates yields local intrinsic
Lipschitz control on the fixed chart source.

`extChart_lip_cpt` is the compact-set projection used by finite chart
partitions.  It requires a `PseudoMetricSpace`, exactly because the standard
compact local-to-global Lipschitz theorem is metric-valued; the two local
theorems retain the weaker `PseudoEMetricSpace` assumption.

## Verification

All three declarations passed focused verification without warnings.  No
completeness, connectedness, finite-dimensionality, or boundarylessness
assumption is used.
