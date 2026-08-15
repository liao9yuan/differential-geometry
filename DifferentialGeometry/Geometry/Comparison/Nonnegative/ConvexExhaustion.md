# ConvexExhaustion

## Scope

This module supplies the elementary Busemann half-space and ray-sublevel layer used before the curvature-dependent core of the Soul theorem.

The sign is the classical exhaustion sign: the existing Busemann function is distance minus time, so the half-space is defined by `-busemann ≤ c`.

## Implemented layer

- The minimizing-geodesic-ray predicate is reused from `Ray.lean`, its canonical producer layer, and the half-spaces use the metric-explicit `busemannOf g`.
- Busemann half-spaces are monotone and closed, and their intersection with the defining ray is computed exactly.
- Ray Busemann sublevels are closed, monotone, contain the basepoint at nonnegative levels, cover the manifold at natural levels, and strictly nest into interiors.
- No defining minimizing geodesic ray can remain inside one fixed finite ray sublevel, providing the contradiction half of the compactness route.
- Total convexity is obtained conditionally from geodesic concavity of every Busemann function.
- `RiemannianMetricComplete.raySublevel_compact` combines that conditional total convexity with the internal-ray escape producer and proves compactness for every real level; negative levels are closed subsets of the compact zero level.
- `ray_convex_of_nonneg` and `ray_compact_nonneg` discharge the conditional
  input from `NonnegSecMetric` through the public Busemann concavity theorem.
- `rayExhaustion` packages the natural levels as a `CompactExhaustion`, and
  `rayExhaustion_convex` proves that every level is totally convex.

## Verification

Focused, targeted, and full-project verification passed without a new warning
or placeholder.  Direct axiom verification of the public exhaustion endpoints
found only `propext`, `Classical.choice`, and `Quot.sound`.

## Frontier

The curvature-dependent compact totally convex exhaustion is complete, and
`ConvexCore.lean` now selects its least nonempty level.  The next Soul frontier
is relative-boundary shaving: prove stability of the appropriate inner parallel
sets, obtain dimension drop at boundary, and identify the terminal set as a
compact boundaryless totally geodesic submanifold.

## Progress

The compact totally convex exhaustion theorem is stated and proved, so that
endpoint is 100%.  The Soul theorem itself remains unstated and therefore 0%;
its dedicated machinery is approximately 31--32% after the minimum-core
producer.  Shaving, terminal-set
submanifold regularity, normal-bundle structure, and the final diffeomorphism
remain.  The whole B1 lane is approximately 22--25%, and the whole post-HCG
Poincare program remains approximately 15--20%.
