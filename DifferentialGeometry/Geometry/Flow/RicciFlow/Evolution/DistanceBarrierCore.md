# DistanceBarrierCore

## Role

This module is the precompiled analytic core for the evolving Calabi distance
barrier.  It owns the fixed-path length variation, the bundled Calabi support,
the fixed-time comparison coefficient, and the exponential rescaling
calculation.

The split from `DistanceBarrier.lean` is an elaboration boundary, not a second
mathematical route.  The public import path remains `Evolution.DistanceBarrier`.

## Exported producer boundary

- `DistanceBarrierCore.ricci_quad_of_curv` converts the order-zero intrinsic
  curvature-tower bound to the uniform quadratic Ricci bound.
- `DistanceBarrierCore.scaled_of_quad` consumes that quadratic Ricci bound and
  completeness of the selected slice, and returns a nonempty
  `DistanceBarrierCore.ScaledDistSupport`.
- `DistanceBarrierCore.ScaledDistSupport.toResult` is the single projection to
  the exact explicit support proposition used by the endpoint.

The support bundle is exposed only in the internal `DistanceBarrierCore`
namespace so that the endpoint can cross the artifact boundary without
re-elaborating the large nested existential proposition.  All fixed-time Calabi
structures remain private.

## Verification

Focused verification is green with zero diagnostics, and the exact targeted
artifact refresh is green (`3994/3994`).

## Accounting

The core producer machinery is about 95% of the evolving support route, but it
does not by itself prove the public endpoint.  Until
`scaledDist_calabiUpperSupport_of_sol` is checked, that theorem remains 0%.
The whole HCG supporting machinery remains about 60%, and unconditional
`compactnessSol` remains 0%.
