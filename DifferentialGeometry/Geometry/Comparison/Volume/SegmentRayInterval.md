# SegmentRayInterval

## Mathematical route

For a fixed nonzero tangent vector, the positive radial parameters lying in
`SegInt` form a nonempty downward-closed set with no largest element.  Local
radial distance equality supplies a small minimizing vector, `segInt_smul`
supplies downward closure, and the defining outward extension in `SegInt`
supplies a larger member above every member.

Splitting on boundedness and taking the real supremum therefore identifies the
set as either `Ioo 0 b` for some positive finite endpoint or all of `Ioi 0`.
`segIntRay` is only the direct radial predicate set; no cut-radius choice
object or packaged frontier assumption is introduced.

For any radial vector with positive metric square, membership of `t • u` in
`gBall R` is exactly `t < R / sqrt (g.inner x u u)` when `t > 0`.
Intersecting the two branches of `segIntRay_eq` with this condition gives an
open initial interval whose positive endpoint is bounded by that quotient.
This is `segIntRay_gball_eq`; `segIntRay_ball_eq` is its `g`-unit specialization
and supplies the sharper displayed bound `b ≤ R`.

## Verification

Focused verification, including the arbitrary positive-square and unit
ball-truncated interval theorems, passes without warnings.  The ambient
manifold grade is the smooth grade actually used by the proofs; the earlier
outer-top annotation accidentally required the stronger analytic grade and
blocked its smooth downstream consumer.  Focused reverification now passes
without warnings.  The targeted named refresh also passes because
`DistanceRadialIntegral` consumes the corrected exported instance level.
