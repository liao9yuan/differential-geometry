# StepCInputs.lean

## 2026-06-30

Added the C4-layer strict distance-squared convexity input for MSM135
`lbl413`/`lbl416`.

The input is intentionally shaped exactly like
`CenterOfMass.exists_unique_curve*`: it packages the midpoint containment,
endpoint laws, and per-summand `StrictConvexOn` statement along the selected
joining curves in the Hopf--Rinow metric world. It does not claim to prove the
Hessian comparison.

Verification passed for the focused file check and the targeted module refresh.

Implementation trap: this file must live in the same RiemannianBundle instance
world as `CenterOfMass.lean`. The local `Tensor0SBundle` tangent norm instances
are removed so `g.toRiemannianMetric` controls tangent fibers.

The index type is currently restricted to `Type`, matching the finite-gradient
equation endpoint in `CenterOfMass.lean`.
