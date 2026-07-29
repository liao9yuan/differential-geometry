# H6MetricJet

## Role

This module transfers the finite-tube intrinsic Jacobi-jet cap to endpoint
Gram jets. It is the scalar estimate layer before the two polarization steps
that recover the full pullback-metric derivative norm.

## Status

The scalar layer is complete in source:

- `intrMetricJet_abs_le` bounds an order-`n` Gram jet by
  `2 ^ n * B ^ 2`;
- `intrMetricJet_tube` supplies the common Jacobi-jet cap from
  `H6JacobiPair.intrJet_upto_le`;
- `intrMetric_deriv_le` uses full derivative-slot symmetry, metric-slot
  symmetry, and the two polarization estimates to bound the complete
  order-`n` Fréchet derivative of `intrFrameMetric`.

`intrMetric_deriv_le` is focused and exact GREEN (`3964/3964`). The only
repairs needed were removal of a redundant `NormedSpace` binder, an explicit
normed-space instance for the bilinear-form carrier, and normalization of the
final product bound. The mathematical statement and route were unchanged.

## Next target

Transfer this bound into the final `exists_h6NormalData` assembly through
`NormalBallChart.MetricDerivBound.of_eqOn`.

## Accounting

`intrMetric_deriv_le` and its dedicated metric-jet machinery are complete and
exact-verified. `exists_h6NormalData` is stated but still unverified, so that
theorem remains 0%. The independent legacy
`NormalRadiusProfile.le_exp_radius` gate remains 0%.
