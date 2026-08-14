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

## Implemented API

The closure layer provides `mapsTo`, `univ`, `empty`, `inter`, and `sInter`.
`IsGeodesicConvex` and `IsGeodesicConcave` quantify convexity or concavity
along every ambient geodesic segment.  Their `sublevel` and `superlevel`
theorems convert scalar comparison results directly into total convexity.
In the complete connected Riemannian setting, `IsTotallyConvex.minJoin` applies
the all-geodesic definition to the existing Hopf--Rinow selected join, and
`IsTotallyConvex.joinedIn` shows that two points of a totally convex set are
joined inside that set.

The selected-join interface remains useful for local ball and HCG arguments,
but it is not used as the definition of total convexity.

## Frontier and progress

The canonical total-convexity and scalar geodesic-convexity interfaces are
complete.  `ConvexExhaustion.lean` now constructs the Busemann half-space
family and proves the compactness contradiction once geodesic concavity is
available.  The remaining producer is the curvature theorem that Busemann
functions are geodesically concave under nonnegative sectional curvature.

The Soul theorem remains unstated and therefore 0%; its dedicated machinery
is approximately 15%.  The whole B1 nonnegative-curvature lane is
approximately 12--15%, and the whole post-HCG Poincare program remains
approximately 15--20%.

## Verification

Focused and full-project verification passed.  The edited source introduced no
warnings or placeholders, and the public total-convexity lemmas have no
`sorryAx` dependency.
