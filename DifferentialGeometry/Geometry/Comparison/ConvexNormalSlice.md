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
the convex set.

`exists_rel_path` combines the chart identity with star-convexity to produce
an ambient-open neighborhood whose intersection with the convex set is path
connected.

## Verification

Focused, targeted, and full-project verification passed without a warning or
placeholder in the edited module.  Direct axiom verification of the public API
found only `propext`, `Classical.choice`, and `Quot.sound`.

## Frontier and progress

The next genuine N4 theorem is still the dense convex-stratum producer.  The
new slice API supplies its normal-coordinate and local-connectivity input, but
does not yet identify the maximal-dimensional tangent span, prove local
linearity, construct an embedded submanifold, or prove that the stratum is
totally geodesic and dense.

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery
is approximately 33--34%; the convex-stratum theorem remains unstated and 0%,
with roughly 10--15% of its dedicated local groundwork now present.  The whole
B1 lane remains approximately 22--25%, and the whole post-HCG Poincare program
remains approximately 15--20%.
