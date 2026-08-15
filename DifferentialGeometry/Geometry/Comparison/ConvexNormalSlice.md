# Convex normal slices

## Scope

This module begins the local regularity route toward the Cheeger--Gromoll
convex-stratum theorem.  It studies a totally convex set in the intrinsic
framed exponential coordinates centered at one of its points.  It does not
assert that the set is already a submanifold or that its coordinate slice is
linear.

## Implemented API

`normalSlice` is the intersection of a model-space ball with the inverse image
of the convex set under the intrinsic framed exponential map.

`zero_mem_normalSlice` records that a positive-radius slice contains the
origin.  `normalSlice_star` proves that every such slice is star-convex at the
origin.  The proof uses total convexity on the complete radial geodesic from
the center to the selected endpoint; it is not a chart-convexity assumption.

`exists_slice_chart` selects a positive ball inside the source of the local
framed exponential diffeomorphism.  On that ball the map is injective, its
image is open and contains the center, and the image of `normalSlice` is
exactly the relative neighborhood obtained by intersecting that image with
the convex set.  This original public signature is retained for compatibility.
The separate strengthened endpoint `exists_radial_chart` selects an all-order
framed inverse branch and additionally gives the exact radial identity
`riemannianEDist p (B z) = ENNReal.ofReal ‖z‖` on the selected ball.

`exists_rel_path` combines the chart identity with star-convexity to produce
an ambient-open neighborhood whose intersection with the convex set is path
connected.

## Verification

Focused verification, downstream targeted verification, and the root
aggregate check passed without warnings.  Direct axiom verification of the
new local producer chain found only `propext`, `Classical.choice`, and
`Quot.sound`.  The current full-project build is pending.

## Frontier and progress

The local dimension-growth theorem `exists_slice_succ` is now stated, proved,
and verified.  This normal-slice API supplies its coordinate and radial input.
The next genuine N4 producer is maximal-dimension assembly: prove that the
union of maximal embedded slices is relatively open, connected, dense, and
totally geodesic in the compact totally convex core.

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 38--40%; the convex-stratum theorem remains unstated and 0%,
with approximately 45% of its dedicated smooth-stratum machinery now present.
The whole B1 lane remains approximately 22--25%, and the whole post-HCG
Poincare program remains approximately 15--20%.
