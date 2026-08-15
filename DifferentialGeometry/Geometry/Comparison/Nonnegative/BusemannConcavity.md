# BusemannConcavity

## Status

Both active-metric and explicit-complete-metric forms of `buse_comp_concave` are implemented without placeholders. The reusable finite-distance producer `dist_geo_semiconcave` lives in `Comparison/DistanceSemiconcavity.lean`. Focused, targeted, and full-project verification passed after the module split. Direct axiom inspection of both forms reports only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The finite-distance theorem combines the Calabi scalar upper support with the one-dimensional quantitative upper-support criterion. For a minimizing ray, the second theorem applies those estimates at points tending to infinity, subtracts a quadratic error whose coefficient tends to zero, and passes concavity to the pointwise Busemann limit.

The result is deliberately stated for a globally smooth geodesic. It cannot yet be packaged as the existing `IsGeodesicConcave`: that predicate quantifies a bare `Geodesic.IsGeodesicOn` curve, which records pointwise geodesic equations but not continuity. The canonical correction is to require `ContinuousOn` for the segment and then use local geodesic regularity. Changing those public predicates requires an explicit API decision.

## Project position

- Finite-distance geodesic semiconcavity: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` Busemann theorem: unstated, 0%; dedicated comparison machinery approximately 60%.
- Compact exhaustion under nonnegative sectional curvature: unstated, 0%; the conditional compactness consumer is 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 24%.
- Whole B1 nonnegative-curvature lane: approximately 18--20%.
- Whole post-HCG Poincare program: approximately 15--20%.
