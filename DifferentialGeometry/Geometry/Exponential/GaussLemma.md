# GaussLemma notes

## 2026-07-01, normal-chart source projection

Added `memNChartSrcOfDist`, the direct source-membership projection of
`metricBall_subset_normalBall`: a point at finite Riemannian distance strictly
below `expRadiusGp g c` lies in `(normalChartAt g c).source`.

This keeps C4 code from unpacking the radial-vector existential when it only
needs the normal-chart source predicate. Verification passed for the edited
file and the targeted module build. The axiom probe reports only the usual
project axioms.
