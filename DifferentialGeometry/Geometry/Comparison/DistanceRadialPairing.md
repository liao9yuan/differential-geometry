# DistanceRadialPairing

## Mathematical route

`dist_action_radial` combines the regular-locus distance-gradient identity
with the metric gradient pairing.  At an exponential image of a nonzero
interior minimizing vector, the action of a smooth test gradient on distance
is the test differential evaluated on the outgoing radial velocity, divided
by the radial speed.

The bridge is kept separate from the distributional endpoint because its
natural model-space assumptions are exactly the inner-product assumptions of
`SegInt` and the intrinsic radial Jacobi machinery.  It introduces no new
geometric hypothesis and no substitute predicate.

`dist_action_scaled` specializes this bridge to `v = r • u` for any direction
with positive squared metric norm and `r > 0`.  The public identity
`intrGeo_smul_apply` identifies the scaled geodesic with the reparameterized
geodesic.  The existing scalar curve chain rule converts the intrinsic
velocity evaluation to the ordinary derivative at parameter `r`, while
`sqrt_gInner_smul_self` cancels the positive factor `r` and leaves precisely
the inverse speed `sqrt (g.inner p u u)⁻¹`.  Positivity supplies nonzeroness
internally, so the consumer has no separate nonzero assumption.

`dist_action_param` is now the unit-speed specialization of
`dist_action_scaled`; its public statement is unchanged.

## Verification

Focused verification passed without warnings.  The proof uses an explicit
continuous-linear-map scalar calculation to avoid dependent-fiber rewrite
ambiguity; no additional hypothesis or auxiliary frontier is introduced.

The arbitrary-positive-direction producer and its unit-speed specialization
both passed focused verification without warnings.  All three public pairing
theorems in this module are complete.  This helper is complete (100%); the
downstream signed polar integration endpoint is a separate theorem and remains
unstated here (0%).
