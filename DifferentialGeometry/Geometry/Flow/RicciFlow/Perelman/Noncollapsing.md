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
