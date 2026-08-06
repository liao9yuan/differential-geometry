# UnifCurvActionZero.lean

## Purpose

This module is the thin HCG adapter from the supplied class-uniform tangent
curvature caps to the finite rank-two `IsCurvAction0` package.  It intentionally
uses only metric comparability and metric jets through order three; it does not
revive the all-rank/all-order curvature gate.

## Route

- `unifCurvSup_of` supplies the variable-metric `R` cap from the fixed
  background order-zero cap.
- `unifRmOpOne_of` supplies the variable-metric `nabla R` cap from the fixed
  background order-zero and order-one caps.
- `ptCurv_zero_of` turns those two tangent caps into the rank-two first-order
  commutator estimate.
- `unifCurvAction0_of` packages that estimate as `IsCurvAction0 g 2 K`.

## Verification

Not yet run.  The native supplied-cap pointwise producer is being repaired and
verified first; this adapter will be checked after its direct dependency is
green and refreshed.

## Progress

`unifCurvAction0_of` theorem: implemented, not yet verified.  This adapter is a
small part of the common realization-radius producer; the actual common
six-number envelope `lowreg_bounds_unif` remains unproved.
