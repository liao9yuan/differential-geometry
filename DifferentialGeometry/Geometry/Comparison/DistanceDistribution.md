# DistanceDistribution

## Mathematical route

`tsupp_dist_bounds` isolates the compact-support reduction used by the direct
polar proof of weak distance-Laplacian comparison.  A compact test support that
avoids the pole has a positive minimum and finite maximum of the real-valued
Riemannian distance, so every later radial calculation can take place on one
annulus `0 < a <= r <= R`.

`dist_green` supplies the noncompact first-order Green identity that was absent
from the smooth-only divergence API.  It combines the intrinsic one-Lipschitz
bound for distance with `lip_green_comp`, taking the compactly supported vector
field to be the gradient of the smooth test function.  It proves integrability
of the distance action and rewrites the test Laplacian integral as its negative.

`dist_action_radial` is kept in the adjacent radial-pairing module.  The formal
distributional Laplacian comparison still requires the signed polar integral
and initial-segment radial integration-by-parts assembly; neither checked
result is presented as that endpoint.

`dist_locInt` records local integrability of the real-valued distance, and
`invDist_locInt` records local integrability of `c / distance` off the pole.
They fill the two analytic data fields of the eventual distributional
predicate without assuming its test-function inequality.

## Verification

Focused verification of `tsupp_dist_bounds`, `dist_green`, `dist_locInt`, and
`invDist_locInt` passed without warnings after refreshing the imported
radial-pairing module.  The formal distance-Laplacian endpoint remains pending.
