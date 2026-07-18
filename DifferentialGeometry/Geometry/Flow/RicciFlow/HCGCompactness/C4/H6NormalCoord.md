# H6NormalCoord

## Purpose

This module is the native producer boundary between radial Jacobi estimates
and the Chapter-4 `NormalCoordMetricBoundInput` API. It must not introduce a
replacement geometric assumption.

## Status

Implementation resumed on 2026-07-18. The raw-coordinate brick records the
exact endpoint-Jacobi formula for `normalCoordMetric` and the resulting legacy
conversion from two-sided Jacobi length estimates to
`NormalCoordMetricEquivOn`.

`Geometry/Exponential/NormalFrame.lean` now constructs, at every center `x`, a
chosen continuous linear equivalence `normalFrame : E ≃L T_xM` and proves

`g_x(normalFrame v, normalFrame w) = <v,w>`.

`Geometry/Exponential/FramedNormalCoordinates.lean` now defines the genuine
normal chart `z |-> exp_x(normalFrame z)`, its inverse, its differential, and
the exact equivalence between model balls and `g_x` tangent balls. This file
proves that `framedMetric` is the pullback metric of that chart, equals
`innerSL Real` at the center, and is the endpoint Gram form of radial Jacobi
fields launched through the same frame. Its framed Jacobi API now consumes the
intrinsic `expRadiusGp` rather than the raw `expMapC2Radius`. All three focused
checks and the generic targeted module builds pass.

## Corrected feasibility diagnosis

The current `normalCoordMetric Y x` uses the raw model identification
`E = TangentSpace I x`. At the origin, `normalMetric_zero` gives

`normalCoordMetric Y x 0 = Y.metric.inner x`.

Therefore the raw predicate on a set containing zero already requires the
fixed model norm and `Y.metric.inner x` to be between `1 / 2` and `2`.
Intrinsic curvature and injectivity bounds cannot imply that raw-coordinate
claim, since a linear rescaling of the ambient atlas changes the coefficients
while preserving the intrinsic geometry.

This is not a mathematical obstruction and does not require a new H6
hypothesis. Genuine normal coordinates include a per-center `g_x`-orthonormal
identification `E ≃ T_xM`; the checked `normalFrame` supplies it by classical
choice from the metric itself.

The remaining obstruction is a shared API migration. The current HCG chart
consumers and the geometric `injRadius` backend use raw model-norm balls.
The textbook injectivity radius and H6 estimates must instead use the framed
map `z ↦ exp_x(normalFrame z)`, whose model ball is exactly the `g_x` tangent
ball. Merely replacing the metric estimate while retaining the raw chart would
be inconsistent.

## Honest progress

- Raw conditional bridges `metric_eq_jacobi` and `equiv_of_jacobi`: 100%
  proved and checked. The latter is retained only as a legacy adapter.
- Per-center orthonormal normalizer and exact radial norm correspondence: 100%
  proved and checked.
- Framed chart, inverse chart, differential, pullback metric, and framed Jacobi
  bridge: 100% proved and checked.
- Native zero-order `NormalCoordMetricEquivOn` producer theorem: 0%; its
  dedicated Jacobi/Rm04 machinery is about 80%, while its coordinate
  representation layer is about 75% (the framed chart is done; shared
  injectivity-radius and consumer semantics remain).
- Native all-order `NormalCoordMetricBoundInput` producer theorem: 0%; its
  dedicated machinery is about 30%, because the high-order curvature-to-metric
  jet induction has not been formalized.
- Unconditional MSM135 Theorem 3.9: 0%. Conditional Theorem 3.9 remains 100%;
  whole HCG compactness machinery remains about 60%.

## Next target

The mathematical route is fixed. The next edit crosses a shared B/C API and
therefore requires ownership coordination:

1. Introduce the framed/intrinsic injectivity-radius ball and migrate the HCG
   radius consumers; retain the raw generic APIs only as explicitly named
   tangent-model compatibility machinery.
2. Make `NormalCoordMetricBoundInput` and the Chapter-4 transition maps consume
   the same framed chart, then specialize the existing radial Gronwall/Rm04
   producer under `HasCurvDerivBound ... 0`.
3. Treat higher coordinate derivatives as a separate induction on curvature
   derivatives; do not hide that frontier in the zero-order package.

## Migration audit

The minimal canonical migration is not a new parallel API:

1. `Geometry/Comparison/InjectivityRadius.lean` must measure injectivity of
   `z |-> exp_x(normalFrame z)` on model balls, equivalently `exp_x` on
   intrinsic `g_x` tangent balls.
2. `Geometry/Comparison/ExpBallDiffeo.lean` must restrict that same framed
   exponential map, not the raw model identification.
3. `C4/StepBInputs.lean` should retain its public HCG names but redefine
   `normalCoordMetric` through `framedExpDiffeo` and `normalTransition` through
   the checked generic `framedTransition`.
4. Downstream B/C files should then need proof-shape repairs rather than new
   hypotheses. The existing raw formulas remain useful only as implementation
   lemmas relating framed coordinates to the underlying tangent-fiber map.

The generic frame, chart, transition, radial-ball, differential, and pullback
identities are now available, so none of those layers should be rebuilt during
the migration.
