# DistanceRadialIntegral

## Role

This module assembles the direct signed polar proof for the distributional
distance-Laplacian comparison.  It is a consumer of the segment-domain,
Jacobian-density, radial-action, and weighted one-dimensional integration
producers; it does not replace any of those producers with assumptions.

## Route

- Compact support away from the pole makes the comparison right-hand side
  globally integrable through `invDist_locInt`.
- Both pairings are localized to a slightly larger intrinsic ball and then
  rewritten by signed polar integration.
- On almost every polar direction, the truncated regular ray is an open finite
  interval.  The radial Jacobian derivative estimate and weighted integration
  by parts give the pointwise directional inequality.
- Fubini reassembles those inequalities over the model sphere.

## Verification

The private `radial_pairing_le` theorem is verified under the native smooth
manifold assumptions.  It uses the actual model-Haar unit sphere, so the test
function is scaled by the inverse Riemannian speed rather than assuming the
polar direction is `g`-unit.

The public `dist_pairing_le` theorem transports both signed integrands through
the exponential Jacobian, obtains almost-everywhere integrable radial slices
from product integrability, applies the directional estimate, and reassembles
the result by Fubini.  `dist_lap_distrib` combines that inequality with
`dist_green` to provide the final `IsLapLEDistribOn` comparison on the punctured
manifold.  The complete file passed a warning-free focused check.

## Project status

The formal P1c Laplacian-comparison endpoint is stated and focused-verified:
**100%**.  This closes one of the four separately counted P1c endpoints, so the
P1c endpoint count is **25%**; Busemann, splitting, and soul remain separate and
are not credited here.  The dedicated Laplacian machinery is **100%**, while
whole-P1c dedicated machinery is conservatively about **35--40%**.  The broader
P0--P9 infrastructure estimate remains **15--25%**, and the final Poincare
theorem itself remains unstated at **0%**.
