# Geodesic convexity

## Scope

This module contains two deliberately distinct convexity interfaces.
`IsGeodesicallyConvexWith join S` says that one selected family of joins stays
inside `S`.  `IsTotallyConvex g S` says that every ambient geodesic segment
whose endpoints lie in `S` stays inside `S`.

The total-convexity definition explicitly quantifies the curve and its two
parameter endpoints.  It does not require the geodesic to be minimizing.  This
is the version required by the Soul theorem; the textbook erratum explicitly
removes the older minimizing qualifier.

All three all-geodesic predicates now require `ContinuousOn` on the closed
parameter interval in addition to `IsGeodesicOn`.  This is necessary because
the latter records pointwise extended-chart equations but does not by itself
imply continuity.

## Implemented API

The closure layer provides `mapsTo`, `univ`, `empty`, `inter`, and `sInter`.
`IsGeodesicConvex` and `IsGeodesicConcave` quantify convexity or concavity
along every ambient geodesic segment.  Their `sublevel` and `superlevel`
theorems convert scalar comparison results directly into total convexity.
`IsGeodesicConcave.of_global` uses the complete-manifold globalization
producer from `IntrinsicExp.lean` to transport a theorem for global smooth
geodesics to this closed-segment interface.
In the complete connected Riemannian setting, `IsTotallyConvex.minJoin` applies
the all-geodesic definition to the existing Hopf--Rinow selected join, and
`IsTotallyConvex.joinedIn` shows that two points of a totally convex set are
joined inside that set.

The selected-join interface remains useful for local ball and HCG arguments,
but it is not used as the definition of total convexity.

## Frontier and progress

The canonical total-convexity and scalar geodesic-convexity interfaces are
complete.  Busemann concavity under nonnegative sectional curvature now feeds
these interfaces and produces a compact totally convex exhaustion.  The next
Soul frontier is the shaving/minimum-set stage: inner parallel sets,
dimension drop, and the passage to a compact boundaryless totally geodesic
submanifold.

The Soul theorem remains unstated and therefore 0%; its dedicated machinery
is approximately 31--32%.  The whole B1 nonnegative-curvature lane is
approximately 22--25%, and the whole post-HCG Poincare program remains
approximately 15--20%.

## Verification

Focused, targeted, and full-project verification passed.  The edited source
introduced no warnings or placeholders, and direct axiom verification of the
public globalization consumers found only `propext`, `Classical.choice`, and
`Quot.sound`.
