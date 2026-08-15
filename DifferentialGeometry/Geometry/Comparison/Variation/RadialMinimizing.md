# RadialMinimizing

## Status

`radial_min_len` is implemented without placeholders and passed focused, targeted, and full-project verification.

The theorem turns an exact endpoint-distance identity for a unit-speed intrinsic radial geodesic on `[0, L]` into the length-minimizing predicate used by the index-form comparison layer. It combines the general distance-versus-arc-length inequality with `arcLength_radial`.

The checked route deliberately does not use the older `HopfRinow.unit_speed_rescale`, whose current source path still contains a placeholder. This file is the shared low-level producer for endpoint comparison and future volume consumers.

## Project position

- `radial_min_len`: 100% after focused, targeted, and full-project verification.
- Unit-speed/minimizing bridge needed by `intrJacobi_pair_le`: 100%.
- Selected-branch Hessian comparison: 100% after focused, targeted, and full-project verification.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` Busemann theorem: 100%.
- Compact totally convex exhaustion under nonnegative sectional curvature: 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 30%.
- Whole B1 nonnegative-curvature lane: approximately 22--25%.
