# ShiBallCutoff

## Status

`shiBallCutoff` is the fixed-radius cutoff profile built from the scaled
time-dependent Riemannian distance. `shiBallCutoff_mem` gives its range,
`shiBallCutoff_ctr` gives its center value, and `shiCutoff_inner` proves that a
positive cutoff point at nonnegative time lies in the inner half-radius ball.

`shiCutoffError` records the exact profile error with the required quadratic
dependence on the inverse radius, and `cutoffError_nonneg` proves that budget
is nonnegative in positive dimension. `exists_cutoff_ne` consumes the generic
`support_of_scaled` and the ball-local `exists_ballFlow`; at every positive
noncenter cutoff point it produces an actual `ShiCutoffLowerSupportAt` without
a whole-manifold curvature bound.

The regular-time center branch is now complete. `exists_cutoff_ctr` uses the
local `edistContAt_ctr` theorem to show that the cutoff is identically one on a
spacetime neighborhood of the center, so the constant function one is a lower
parabolic support. `exists_cutoff` combines center and noncenter points and is
the all-point fixed-radius lower-support endpoint. The complete file is
warning-free focused GREEN.

`shiBallSupport` is the time-zero intrinsic half-ball selected for the finite
cutoff package, and `shiBallSupport_cpt` proves it compact from time-zero
metric completeness. `shiCutoff_zero` has now been source-written from the
separate local distance anchor: it splits according to whether the scaled
later distance has already crossed the controlled radius, and otherwise uses
`dist0_le_scaled` to force the cutoff argument past the profile's zero
threshold. The anchor has been warning-free focused checked and refreshed,
and `shiCutoff_zero` is now warning-free focused GREEN. Thus compactness and
fixed-support vanishing are both checked.

The ordered two-slice anchor `distPair_scaled` is also checked and refreshed.
Under the direct-route shortness condition

```text
exp (2 * (dim M)^2 / radius^2 * T) < 2,
```

`shiBallCutoff_cont` first proves that every point of the time-zero half-ball
has enough room for the two-slice estimate throughout the slab, then squeezes
the moving distance between continuous fixed-slice distances. This gives joint
continuity on `Icc 0 T ×ˢ shiBallSupport B` without a whole-manifold Ricci
bound or a false global moving-distance continuity claim.

`shiFixedCutoff` now assembles the checked compact support, off-support
vanishing, range, joint continuity, nonnegative exact error, and all-point
lower supports into the generic `ShiFixedCutoff` record. Both the continuity
theorem and the assembled data are warning-free focused GREEN.

## Next theorem

The generic finite-error `m = 1` Bernstein theorem `estimate_cutoff_one` is
warning-free focused GREEN. `shiCutoff_one` supplies the exact plateau and
`shiCutoff_dist_lt` converts cutoff positivity to the strict intrinsic
half-ball condition; both are consumed by the now checked `shiRm1_ball` proof.

This file's fixed-cutoff package and `shiRm1_ball` are 100% theorem endpoints.
`smooth_nlc` remains 0%. Dedicated L8--L9 machinery is about 86--88%,
generic reused infrastructure is 100%, and whole P0--P9 infrastructure remains
15--25%.
