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

## Verification

Focused verification and the full-project build passed without a new
placeholder.  The public compactness endpoint has no `sorryAx` dependency.

## Frontier

The remaining curvature producer is the nonnegative-sectional-curvature theorem that Busemann functions are geodesically concave.  The Hopf--Rinow escape lemma and the compactness contradiction are now proved; `raySublevel_compact` is deliberately conditional on concavity until the comparison theorem exists.

## Progress

The Soul theorem endpoint remains unstated and is therefore 0% complete. Its dedicated infrastructure is approximately 15% complete.  The elementary exhaustion and conditional compactness route are checked, while Busemann concavity, minimum-set regularity, shaving, normal-bundle structure, and the final diffeomorphism remain.  The curvature-dependent compact exhaustion theorem itself is still unstated and therefore 0%.
