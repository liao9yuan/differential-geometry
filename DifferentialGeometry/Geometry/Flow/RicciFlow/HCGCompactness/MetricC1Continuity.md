# MetricC1Continuity

## Goal

Prove time continuity at a regular time of the cumulative order-one metric
derivative seminorm, without selecting a global frame and without forming a
tensor-valued map whose fibre varies with the spatial point.

## Route

The implementation fully evaluates each fixed-background covariant derivative
on slots from one genuine smooth local frame.  Local frame vectors are extended
to global smooth sections only near the point, the existing joint scalar tower
then gives continuity, a finite component-square bound produces a local norm
patch, and compactness turns the spatial cover into one uniform time
neighborhood.

The proposed extra partial-derivative continuity API is not needed:
`prodExtDerivAt_inf`, already consumed by
`covDerivOfField_eval_contMDiffAt`, supplies the parametric scalar derivative
step.

## Status

The lower scalar metric-pair producer has passed focused and targeted module
verification.  The complete local-to-global file passes focused verification:

- `metricCov_smooth` proves scalar spacetime continuity only after applying
  the varying-fibre tensor to actual local-frame slots;
- `metric_c_patch` turns the finite component square into one exact-order
  local modulus;
- `metric_c1_patch` intersects the order-zero and order-one patches;
- `metric_c1_tendsto` takes a compact finite subcover and intersects its time
  neighborhoods.

No `HasLocallyConstantChartAt`, global frame, whole-tensor equality, or new
consumer convergence hypothesis is used.

## Progress

The `metric_c1_tendsto` theorem is proved (100%), and its dedicated machinery
is complete (100%).  This continuity theorem is one coefficient producer for
the noncollapsing operator route; the actual finite-spectral-support `A2(s)`
estimate remains unstated and unproved (0%).  Dedicated `A2` machinery is
approximately 74% complete: the remaining local analytic work is the three
coefficient/norm bridges recorded in `Nonautonomous.md`, followed by the
operator extension.
