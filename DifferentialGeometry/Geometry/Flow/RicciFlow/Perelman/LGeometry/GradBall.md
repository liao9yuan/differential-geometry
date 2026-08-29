# GradBall

## Role

`lGrad_ball` converts the ball-local first derivative Shi estimate into the
scalar-curvature gradient pairing needed by the regularized L-speed ODE. It
keeps the dimension-only constants uniform in the terminal time, center, and
radius while retaining the later-half-time and additional half-radius losses.

## Implementation

At a fixed spacetime point the proof traces `ricCovTower` in its first two
slots. The trace is identified with one half of the scalar differential by the
contracted second Bianchi identity, and `inner_gradientFun` converts that
differential into the metric pairing with `gradientFun`. The native
`ricTower_normSq_le`, `trace_normSq_rank_le`, and `abs_apply_le_norm0S` bounds
then give a dimension factor `d^4` after taking square roots. Combining this
with `shiRm1_ball` yields the scale `C / radius^3` on the radius-`1/16`
subball.

No compactness, whole-manifold curvature bound, new tensor representation, or
new analytic assumption is introduced. The pointwise trace realization is
private to this adapter.

## Status

Focused verification is warning-free green. `lGrad_ball` is **100%** for its
stated interface and contains no placeholder. It has not yet been named-
refreshed because the next downstream module is not source-written yet.

The exact next theorem is `lRegSpeed_unif`: feed this local gradient pairing
and the existing ball-local Ricci quadratic bound into `lRegSpeed_gron`, with
constants chosen before terminal time and radius. `smooth_nlc` remains
unstated and unproved (**0%**). Dedicated L8--L9 machinery is about
**88--90%**; reused generic infrastructure is **100%**; whole P0--P9 remains
**15--25%**.
