# RiemannianDistContinuity

## 2026-07-16 pairwise chart-distance producer

Mathlib's `eventually_riemannianEDist_le_edist_extChartAt` controls the
Riemannian distance from the chart center to one nearby point. That one-fixed-
endpoint statement does not imply the pairwise Lipschitz estimate needed by
Euclidean difference quotients or a chart-pushed distance cutoff.

`chart_symm_edist_le` generalizes the same path-length proof to arbitrary
endpoints in one sufficiently small convex ball in the extended chart range.
It uses only the local derivative bound for `extChartAt.symm`, the Euclidean
line segment, and `riemannianEDist_le_pathELength`. It does not use an
exponential chart, injectivity radius, `HasLocallyConstantChartAt`, or any
noncollapsing input, so the route is non-circular.

This producer gives a metric-dependent local constant. Compactness can make
it uniform over the finitely many fixed chart supports for one fixed metric;
it does not by itself make the constant uniform along flow times approaching
a singular endpoint.

`chart_inv_edist_le` removes the remaining fixed-center restriction for a
single chosen chart. At an arbitrary target point it switches locally to the
chart centered at the corresponding manifold point, applies
`chart_symm_edist_le`, and composes with the smooth chart transition. This is
the local statement needed to treat a POU-weighted distance tent throughout
the support of a fixed chart, rather than only near that chart's center.

Focused verification passed without warnings.
