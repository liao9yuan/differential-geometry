# BusemannConcavity

## Status

Both active-metric and explicit-complete-metric forms of `buse_comp_concave`
are implemented without placeholders.  The public `buse_geo_concave`
headlines use the closed-segment globalization producer to prove
`IsGeodesicConcave` for the Busemann function of every minimizing ray under
`NonnegSecMetric`.  The reusable finite-distance producer
`dist_geo_semiconcave` lives in `Comparison/DistanceSemiconcavity.lean`.

The finite-distance theorem combines the Calabi scalar upper support with the one-dimensional quantitative upper-support criterion. For a minimizing ray, the second theorem applies those estimates at points tending to infinity, subtracts a quadratic error whose coefficient tends to zero, and passes concavity to the pointwise Busemann limit.

The compatibility theorem remains available for globally smooth geodesics.
The public predicate now also requires `ContinuousOn` on each closed segment;
`IsGeodesicConcave.of_global` uses completeness and geodesic uniqueness to
globalize such a segment before invoking the smooth theorem.

## Project position

- Finite-distance geodesic semiconcavity: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` Busemann theorem: 100%.
- Compact totally convex exhaustion under nonnegative sectional curvature: 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 31--32%.
- Whole B1 nonnegative-curvature lane: approximately 22--25%.
- Whole post-HCG Poincare program: approximately 15--20%.

Focused, targeted, and full-project verification passed without a new warning
or placeholder.  Direct axiom verification of the public Busemann concavity
endpoints found only `propext`, `Classical.choice`, and `Quot.sound`.
