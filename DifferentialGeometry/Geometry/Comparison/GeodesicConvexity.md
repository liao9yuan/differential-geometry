# Geodesic convexity

## Scope

This module contains deliberately distinct local and global geodesic
interfaces.
`IsGeodesicallyConvexWith join S` says that one selected family of joins stays
inside `S`.  `IsTotallyConvex g S` says that every ambient geodesic segment
whose endpoints lie in `S` stays inside `S`.

`IsTotallyGeodesic g S` is the local chord version: around every point of `S`,
ambient geodesic chords with endpoints in `S` stay in `S`.  It is strictly
local and does not identify total geodesy with global total convexity.

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
`IsGeodesicConcaveOn g C f` restricts the scalar assertion to geodesic
segments mapped into a carrier `C`; its `superlevel` theorem proves total
convexity of the corresponding inner superlevel inside a totally convex
carrier.  This is the correct interface for distance to a relative boundary,
which is not expected to be concave along geodesics outside the carrier.
`IsGeodesicConcave.of_global` uses the complete-manifold globalization
producer from `IntrinsicExp.lean` to transport a theorem for global smooth
geodesics to this closed-segment interface.
In the complete connected Riemannian setting, `IsTotallyConvex.minJoin` applies
the all-geodesic definition to the existing Hopf--Rinow selected join, and
`IsTotallyConvex.joinedIn` shows that two points of a totally convex set are
joined inside that set.  A nonempty totally convex set is therefore
path-connected and connected via `IsTotallyConvex.isPathConnected` and
`IsTotallyConvex.isConnected`; these are the connectivity inputs used by the
classical convex-stratum theorem.
`IsTotallyConvex.is_totally_geodesic` supplies the canonical implication from
the stronger global property to the local chord property.

The selected-join interface remains useful for local ball and HCG arguments,
but it is not used as the definition of total convexity.

## Frontier and progress

The canonical total-convexity and scalar geodesic-convexity interfaces are
complete.  Busemann concavity under nonnegative sectional curvature now feeds
these interfaces and produces a compact totally convex exhaustion.  Generic
inner-parallel and deepest-set consumers live in `ConvexShaving.lean`.  The
dense smooth-stratum theorem is now verified in `ConvexStratum.lean`.  The next
genuine Soul frontier is concavity of distance to its relative boundary,
followed by strict dimension drop and the passage to a compact boundaryless
totally geodesic submanifold.

The Soul theorem remains unstated and therefore 0%; its dedicated machinery
is approximately 48--52%.  The whole B1 nonnegative-curvature lane is
approximately 30--34%, and the whole post-HCG Poincare program remains
approximately 18--22%.

## Verification

Focused and targeted verification and the root aggregate check passed.  The
edited source introduced no warnings or placeholders, and direct axiom
verification of the new total-geodesy bridge found only `propext`,
`Classical.choice`, and `Quot.sound`.  The current full-project build is
pending.
