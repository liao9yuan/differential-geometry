# Metric preservation by parallel flows

## Mathematical route

`curveAt_inner_eq` treats the spatial differentials of a complete flow as two
vector fields along the same flow line.  The connection-level producer
`curveAt_mfderiv_par` makes both fields parallel.  Metric compatibility then
shows that their pointwise inner product has zero derivative, so it is constant
in time.  At time zero, `curveAt_zero` identifies the flow slice with the
identity and `mfderiv_id` recovers the initial tangent vectors.

`curveAt_pullback_eq` packages the pointwise inner-product identity with the
existing fixed-time `curveAtDiffeo` and the canonical pullback-metric
evaluation theorem.  Thus every fixed-time flow map is a Riemannian isometry
in the pullback-metric sense.

## Reused native API

- `curveAt_contMDiff` supplies joint smoothness of the complete flow.
- `exists_smooth_curve` and
  `variationField_chartRep_differentiableAt` supply the chart-representative
  differentiability required by the metric-compatibility derivative theorem.
- `mfderiv_comp_apply` identifies that variation field with the spatial
  differential applied to the prescribed initial tangent vector.
- `metric_compat_hasDerivAt_inner`, `curveAt_mfderiv_par`, and
  `is_const_of_deriv_eq_zero` close the constancy argument.

## Status

`curveAt_inner_eq` and `curveAt_pullback_eq` passed a warning-free focused
check and explicit named module refresh.  The only integration repairs were
local normal-form issues: zero continuous-linear-map evaluation and the
time-zero identity slice of the flow.  No public assumption or mathematical
route changed, and there is no known mathematical or missing-API blocker in
this producer.
