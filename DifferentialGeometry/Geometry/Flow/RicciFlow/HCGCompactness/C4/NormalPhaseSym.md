# NormalPhaseSym

## Role

This file retains the negative-time half of the normalized Picard family so
that the launch time is an interior point for geometric realization and
geodesic uniqueness.  The time-one endpoint and its quantitative approximation
are unchanged.

## Current state

- `exists_normal_biflow` constructs a common exact normal phase flow on
  `[-1,1]`, exposes both closed-interval and ordinary interior derivatives,
  retains phase-box confinement, and proves the same forward
  `ApproximatesLinearOn` estimate.
- Focused verification and the targeted module build passed; the new file has
  no local warnings or `sorry`.

## Frontier

`NormalPhaseEndpoint.exists_normal_diag` now consumes this bilateral family and
identifies its endpoint with intrinsic `diagExp`.  The remaining frontier is
uniform branch-domain and `expDiffeoRadius` containment for `normal_inv_eq`.
