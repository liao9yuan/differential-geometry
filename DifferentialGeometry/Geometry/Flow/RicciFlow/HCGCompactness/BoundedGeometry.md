# BoundedGeometry

Source used: MSM135 Definition 3.8 and the bounded-curvature assumptions in Theorems 3.9 and 3.10.

Introduced definitions: `curvCovDerivStep`, `curvCovDeriv`, `curvDerivNormSq`, `curvDerivNorm`, `HasCurvDerivBound`, `BoundedGeometry`, `SeqBoundedGeometry`, `HasSpacetimeCurvBound`, `HasSpacetimeCurvDerivBound`, `SpacetimeCurvBound`, `FlowDerivBounds`, and `FlowDerivativeInput`.

Design note: bounded geometry is derivative-order indexed. `HasCurvDerivBound` is no longer an opaque predicate: it unfolds to a global pointwise bound on `curvDerivNorm`, defined from the canonical metric Riemann tensor, iterated `totalNabla0S`, and the metric-induced `normSq0S`. The flow derivative bound is a spacetime family of spatial curvature-derivative bounds on the time-slice metrics.

2026-05-27 correction: removed the vague curvature-bound axioms. The remaining solution compactness theorem still needs `FlowDerivativeInput` and `SmoothFlowLimitInput`; those are theorem-facing packages, but their curvature-bound fields now have concrete norm content.

Verification: passed.
