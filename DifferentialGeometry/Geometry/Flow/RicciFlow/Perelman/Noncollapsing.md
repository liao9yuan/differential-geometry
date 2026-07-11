# Noncollapsing

## 2026-07-09 canonical geometry refactor

`FlowMetricBall S t` is now the canonical ball object.  The time is a
`RealTimeInterval.FlowTime`, and the structure stores only a center and positive
radius.  Its carrier `setAt`, distinguished-time `set`, Riemannian `volume`,
backward-parabolic `IsRmControlled`, and model-dimensional
`IsKappaNoncollapsed` predicates are all derived from the actual solution
metric and canonical `rm04` tensor.

`Nested` is genuine same-time set inclusion, so `volume_mono` follows from
measure monotonicity.  The carrier has the same intrinsic-distance shape as the
existing `smallNormalBall`; a future `Metric.ball` adapter belongs in the
comparison/HCG layer rather than this low Perelman layer.

The zero-callsite `ScaleControlledBall` hierarchy and generic
`hypothesis -> conclusion` proposition aliases were deleted after final audit;
they could otherwise serve as a fake-geometric bypass despite a legacy label.
Hamilton Section 12 has migrated: `ham3RescaledBall` is a genuine
`FlowMetricBall` for the actual `paraSolution`, and `Ham3Noncollapse` uses its
`IsRmControlled` and `IsKappaNoncollapsed` predicates.

Verification passed.  The Hamilton rescaled-source realization and its
`ham3_rm_control` theorem are checked.  The genuine remaining theorem is
Perelman's no-local-collapsing producer (`ham3_noncollapse` remains 0%); further
volume/ball scaling lemmas belong below that producer rather than in a fake
numeric-volume wrapper.

## 2026-07-09 W-route start

`Entropy/ConjugateHeat.lean` now checks the local and interval forms of total
mass conservation for smooth solutions of `∂ₜu = -Δu + Ru`.  This is the first
new analytic producer on the Perelman route.  The moving-metric conjugate-heat
existence theorem remains 0%.

The checked supporting chain now also contains the interval-local
`IsHeatPotOn` / `IsConjHeatOn` interfaces and time reversal,
`heat_pot_nonneg`, the time-operator lift, the abstract
`nonaut_strong_exists` fixed-point theorem, and the local moving-volume
first-variation theorem `first_var_local`.  The source-level scalar Laplacian
bridge is focused-checked, but its targeted refresh is blocked by the upstream
`nablaRSFun_eval_moving_raw` elaboration performance wall.  Independently, the
geometric `A2` realization needs a support-independent fixed-metric estimate
for `Delta_(g_s) - Delta_(gT)`; the exact theorem and three audited routes are
recorded in `TensorMaximalRegularity/Nonautonomous.md`.

The geometric scale-transfer lane is now complete.  The canonical volume law
is in `Analysis/Integration/Measure/Scaling.lean`; `Metric/DistanceScaling.lean`
proves distance and ball-carrier scaling and is used directly by `setAt`;
`ScaleTransfer.lean` proves two-way transfer of ball carriers, volume,
`IsRmControlled`, `IsKappaNoncollapsed`, the below-scale predicate, and
`NoLocalCollapsing`.  Hamilton's checked `ham3_noncollapse_of` now reduces the
fixed rescaled-ball conclusion to a genuine original-flow
`NoLocalCollapsing` producer.

Consequently the scale-transfer sublane is 100%, but the analytic
no-local-collapsing theorem and `ham3_noncollapse` remain theorem-level 0%.
Dedicated analytic machinery is about 25%; whole HCG machinery remains about
45% with endpoint theorems at 0%.
