# CompactPerturbationComplete

## Role

This module supplies the completeness bridge needed by the native CGT
construction.  The pullback metric on an open Euclidean ball is not complete,
so the CGT route extends it to a total metric that is flat outside a compact
collar.

## Checked API

- `RiemannianMetricComplete.of_eq_off_compact`: equality with a complete metric
  outside a compact set implies completeness.
- `RiemannianMetricComplete.bumpExtend_complete`: the standard bump extension is
  complete when the fallback metric is complete and the cutoff has compact
  support.
- `flatModelMetric` and `RiemannianMetricComplete.flatModel_complete`: the
  canonical flat smooth metric on the finite-dimensional model space and its
  completeness witness.

The proof first obtains a positive lower bound on the compact exceptional set
and combines it with equality outside that set.  It does not add connectedness
or completeness assumptions to the original pullback ball.

## CGT status

The compact-fenced Whitehead/join producer remains theorem-level 0%.  Its
dedicated machinery is about 80%: endpoint positivity is checked, and this
module closes both the flat fallback and compact-perturbation completeness
steps.  A separate first-exit argument is still required to show that a
minimizing geodesic for the extended metric stays in the agreement region.

For connectedness, the standing decision is component restriction only when a
legacy ambient theorem genuinely needs it.  On `intrPullBall`, use the
connectedness of the Euclidean ball subtype directly.  This decision does not
replace the completeness argument in this module.

## Verification

Focused verification is green with no diagnostics, and the targeted module
artifact is exact-current.
