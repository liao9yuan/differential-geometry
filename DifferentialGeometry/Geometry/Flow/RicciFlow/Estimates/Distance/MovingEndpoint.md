# MovingEndpoint

## Purpose

This module supplies the local moving-endpoint contribution needed in the
two-point changing-distance argument.  It measures the endpoint segment with
the frozen backward-time metric and bounds its arc length by the base-time
speed plus an arbitrary positive error.

It also supplies `edist_curve_lip`: a `C¹` curve on a compact real interval is
uniformly Lipschitz for the intrinsic extended distance of any fixed smooth
Riemannian metric.  The theorem needs neither completeness nor a Ricci-flow
equation.

## Route

- Extract one open interval on which the endpoint curve is `C¹` from the
  `ContMDiffAt 1` germ.
- Evaluate the smooth metric family on the curve velocity over the joint
  endpoint/curve-parameter space.
- Use joint continuity at the diagonal point to obtain a uniform speed bound
  on every sufficiently short endpoint segment.
- Bound the frozen-metric arc length by that constant and then bound intrinsic
  distance by the same curve segment.

No ambient compact image, completeness, connectedness, Ricci bound, or
Ricci-flow equation is needed.  A pointwise metric comparison cannot replace
the segment route because intrinsic distance requires a bound along a joining
curve.

For `edist_curve_lip`, the compact interval's within-velocity is continuous,
so its fixed-metric speed has a uniform bound.  On every subinterval, the
within derivative agrees almost everywhere with the unrestricted derivative
used by `arcLength`; integrating the speed bound and applying the existing
intrinsic-distance-to-arc-length bridge gives the linear estimate.  Treating
this agreement almost everywhere is essential at the two endpoints and avoids
strengthening `ContMDiffOn` to smoothness on an open neighborhood.

## Verification

Focused verification is warning-free GREEN.  A direct axiom audit of
`edist_curve_lip` reports only `propext`, `Classical.choice`, and `Quot.sound`.
An earlier exact named refresh of the pre-existing module passed GREEN for its
then-current downstream consumer; the new export has not been refreshed during
the active parallel-work window.
