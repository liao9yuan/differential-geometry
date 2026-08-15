# RadialLaplacian

## Status

`branchHess_le_flat`, `branchHess_le_perp`, `branchHess_cross`, and the arbitrary-vector `branchHess_le` are implemented without placeholders. Focused, targeted, and full-project verification passed.

For a selected inverse exponential branch, a minimizing launch with nonzero length, and a perpendicular launch variation, the theorem proves the nonnegative-sectional-curvature comparison

```text
Hess(branchRadius)(J(1), J(1)) <= |J(1)|^2 / sqrt(g(u,u)).
```

The perpendicular proof composes `branchHess_shape` with `intrJacobi_pair_le`. The arbitrary-vector theorem splits into radial and perpendicular parts, uses local Hessian symmetry and the vanishing cross/radial terms, and controls the perpendicular norm. The minimizing input remains explicit as an endpoint-distance equality, so the theorem does not assert smoothness of the true distance across the cut locus.

## Project position

- `branchHess_le_flat`, `branchHess_le_perp`, `branchHess_cross`, and `branchHess_le`: 100% after focused, targeted, and full-project verification.
- Selected-branch Hessian comparison phase: 100%.
- Exact Calabi-tail distance, scalar upper support, and one-dimensional barrier passage: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` Busemann theorem: 100%.
- Compact totally convex exhaustion under nonnegative sectional curvature: 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 30%.
- Whole B1 nonnegative-curvature lane: approximately 22--25%.
