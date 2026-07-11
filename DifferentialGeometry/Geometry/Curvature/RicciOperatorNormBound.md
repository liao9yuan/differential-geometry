# RicciOperatorNormBound

## 2026-07-10 compact fixed-metric bound

- Added `exists_rm04_bound`: spatial continuity of `normSq0S` for the canonical
  smooth `metricRm04` field and compactness give one global nonnegative bound.
- Added `exists_ricci_bound`: the orthonormal Riemann-trace estimate and the
  geometric Rayleigh argument turn that curvature bound into
  `|Ric_g(v,v)| ≤ C g(v,v)`, uniformly in the point and tangent vector.
- The constant depends only on the fixed smooth metric.  It does not depend on
  a scalar field, its spectral support, or the number of eigenmodes.
- Focused verification passed without warnings.  This closes the coefficient
  bound needed by the scalar Bochner Hessian estimate; the remaining frontier
  is the scalar integrated Bochner/Green assembly and its rank-zero L² readout.
