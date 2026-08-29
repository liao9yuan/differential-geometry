# Busemann asymptotic ray

## Role

`exists_asymp_ray` is the native supplied-ray producer needed after Busemann
comparison: from any basepoint it extracts a minimizing ray asymptotic to the
given minimizing ray and proves the global distance-support inequality for the
given ray's Busemann function.

The statement has no noncompactness or Ricci assumption.  Noncompactness is
already witnessed by the supplied ray, while curvature enters only in later
Laplacian applications.

## Proof route

Join the chosen basepoint to integer points escaping along the supplied ray,
normalize the minimizing initial velocities, and extract a convergent
subsequence from the compact metric-unit sphere.  Continuous dependence of the
intrinsic exponential gives the limiting radial curve.  The exact remaining
length of each finite minimizing segment, together with the triangle
inequality, passes to the Busemann limit and gives the global support
inequality.

The support inequality at the basepoint gives exact radial distance.  It also
forces the supplied Busemann function to decrease linearly along the limiting
curve.  The Busemann one-Lipschitz inequality then supplies the lower bound for
pairwise distances on the curve, while the geodesic length estimate supplies
the upper bound.  This packages the curve as an `IsMinimizingRay` without
copying the private radial-to-pair proof from `MinimizingRay.lean`.

## Verification

The first focused check failed only on the finite-tail rescaling identity and
three malformed implicit-binder spellings.  The rescaling was repaired by
using `intrinsicGeodesic_smul` once in the reverse direction and proving the
scalar identity separately; no new hypothesis was needed.

The second focused check reached the final assembly.  It failed on an
ambiguous constant-limit type, one remaining use of a private distance-
commutativity helper, the missing `Geodesic` namespace opening, and one local
`sigma` unfolding shape.  All are local elaboration issues and have static
repairs.  The third focused check passed without warnings, and the explicit
named refresh also passed.  The checked public result retains the limiting
unit initial direction as well as the induced minimizing ray and its global
support inequality.  There is no mathematical or producer-shaped assumption
gap.

## Project accounting

The splitting theorem remains unstated and therefore 0% complete.  Its
dedicated machinery is now about 50--55%; the whole P1c comparison/splitting
phase is about 62--67%, and the whole P0--P9 program about 15--25%.  This
producer closes the supplied-ray compactness/support input to the post-
regularity eikonal chain, not the weak-solution regularity frontier, parallel
flow, or global product endpoint.
