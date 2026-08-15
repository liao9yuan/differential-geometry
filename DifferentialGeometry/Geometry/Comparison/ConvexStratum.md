# Convex stratum growth

`exists_slice_succ` is the local dimension-growth theorem used in Sakai's
maximal-stratum construction.  If an embedded `d`-slice `N` lies in a totally
convex set `C`, and a point of `N` is approached by points of `C \ N`, then
every prescribed neighborhood of that point contains a nonempty embedded
`(d + 1)`-slice lying in `C`.

The proof installs the metric determined by the complete Riemannian metric,
uses a uniform diagonal inverse-exponential branch, chooses a nearest point on
the locally closed slice, and pulls the slice into framed normal coordinates.
The nearest-point condition makes the radial coordinate transverse to the
slice.  The finite-dimensional cone theorem then raises the dimension, while
total convexity keeps the cone inside `C`.  Choosing the cone parameter near
the endpoint places the resulting slice in the requested neighborhood.

The file also completes the maximal-dimension assembly expressible in the
current API.  `maxSliceDim` is attained, the union `maxSliceLocus` of maximal
slices is itself an embedded slice and relatively open in `C`, and local
radial transport propagates it along intrinsic geodesics.  The two-parameter
chord identity gives a clopen continuation argument.  Segment globalization
then proves all-geodesic `IsTotallyConvex`, not merely selected-minimizing
convexity.  `max_stratum_spec` packages nonemptiness, containment in `C`, the
embedded-slice model, relative openness, density in `C`, connectedness, and
total convexity using only the complete metric `hg` as its public metric input.
`exists_max_stratum` gives the corresponding textbook-facing existential and
adds the local `IsTotallyGeodesic` conclusion.

## Verification

Focused verification, targeted module builds, and the root aggregate check
passed.  Direct axiom inspection of `min_join_chord`, maximal propagation,
all-geodesic total convexity, and `max_stratum_spec` reports only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`.  Independent
reviews found no endpoint-direction or metric-coupling defect.  The current
full-project build is pending.

## Frontier and progress

The concrete maximal-locus package and the textbook-facing
`exists_max_stratum` theorem are complete.  The convex-stratum stage is 100%:
the locus is embedded, relatively open and dense, connected, totally convex,
and locally totally geodesic.

The next genuine Soul producer is concavity of distance to the relative
boundary `C \ maxSliceLocus I C`, followed by the flat-rectangle equality case
and strict dimension drop.  The current comparison library lacks the boundary
tangent-cone supporting half-space theorem, the sharp moving-base parallel-exp
Rauch estimate with `J(0) = v`, `J'(0) = 0`, and the local hinge comparison
used by Sakai's affine upper-support proof.  The Soul theorem itself remains
unstated and 0%,
with dedicated machinery approximately 48--52%.  The whole B1 lane is
approximately 30--34%, and the whole post-HCG Poincare program approximately
18--22%.
