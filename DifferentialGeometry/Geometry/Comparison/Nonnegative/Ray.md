# Minimizing rays

## Scope

This module supplies the Phase N1 minimizing-ray producer.  It contains no
curvature hypothesis and does not assert the existence of a minimizing line.

The public endpoints are:

- `Geometry.Riemannian.minRay_of_escape`, which extracts a unit initial
  direction from minimizing segments to a sequence whose intrinsic distance
  from the base point tends to infinity;
- `RiemannianMetricComplete.exists_minRay`, which constructs such an escaping
  sequence on a complete connected noncompact Riemannian manifold and returns
  a minimizing geodesic ray from any chosen base point.

## Proof route

Hopf--Rinow supplies minimizing exponential vectors to the escaping points.
After normalizing those vectors, compactness of the metric unit sphere gives a
convergent subsequence.  Star-shapedness and closedness of `SegDom` show that
every nonnegative multiple of the limiting direction remains minimizing.
Exact radial distance, the triangle inequality, and the geodesic length upper
bound then prove the `IsMinRay` identity on every nonnegative subsegment.

This route uses the intrinsic minimizing-exponential API and does not pass
through the legacy sorry-bearing Hopf--Rinow capstone.

## Boundary and progress

The minimizing-ray producer package is complete.  The pointed limiting-segment
argument needed to produce a two-sided minimizing line is still absent, so the
line producer remains 0% and Phase N1 as a whole is approximately 50%.

The Soul theorem itself remains unstated and therefore 0%.  Its dedicated
machinery remains approximately 5--10%; this ray theorem is shared
nonnegative-curvature infrastructure, not a proof of the Soul theorem.
The whole B1 nonnegative-curvature lane is approximately 10--13%, while the
whole post-HCG Poincare program remains approximately 15--20%.

## Verification

Focused verification passed with no warnings or placeholders.  The public
endpoints have no `sorryAx` dependency.
