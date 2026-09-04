# Manifold image measure equality

## Role

This module supplies the injective equality companion to `ManifoldImageLe`.
Its public endpoint is `riemVol_image_eq`: a `C¹` map from a finite-dimensional
Euclidean model into a Riemannian manifold sends a measurable set on which it
is injective to a measurable image whose Riemannian volume is exactly the
integral of `mapJacDensity`.

The statement deliberately requires only an open neighborhood of the source
set, measurability, `C¹` regularity, and injectivity on that set. It introduces
no completeness, connectedness, intrinsic-distance, or exponential-map
assumptions.

## Mathematical route

- Localize the target Riemannian measure with the existing chart-atlas
  partition of unity.
- On each chart term, extend the coordinate expression by zero outside the
  relevant source region and apply Mathlib's exact Euclidean injective area
  formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
- Identify the absolute coordinate derivative determinant times the chart
  volume density with `mapJacDensity` via the existing Gram determinant and
  manifold-derivative APIs.
- Sum the chart terms and collapse the partition of unity to one.

The coordinate and partition-of-unity lemmas are private: they are the minimal
bridge needed for the public equality and do not form a second general area
hierarchy.

## Verification

`riemVol_image_eq` and all private helpers pass the warning-free focused check.
No targeted refresh was run because the checkout is in a parallel focused-only
window.

## Progress accounting

- Generic injective manifold-image equality: **100%** (stated, proved, and
  focused-verified).
- The separate raw framed-exponential multiplicity-area specialization:
  **0% as a theorem endpoint** until it is stated and proved in its comparison
  module; this generic result is completed dedicated machinery for that later
  specialization.
- Whole Poincare endpoint completion is unchanged by this lower-layer producer.
