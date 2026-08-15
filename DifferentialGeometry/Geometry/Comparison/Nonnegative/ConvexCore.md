# ConvexCore

## Scope

This module selects the least nonempty real level of the compact totally convex ray-Busemann sublevels.  The resulting canonical core is the minimum-set input for the later relative-boundary shaving construction.

## Implemented API

`rayMinLevel` is the infimum of the nonempty ray-Busemann levels, and `rayMinCore` is its sublevel set.  `rayMinLevel_spec` proves that the infimum level is attained and is below every other nonempty level.  `exists_ray_min_level` exposes the corresponding existence theorem.  `rayMinCore_spec` packages nonemptiness, compactness, and total convexity of the canonical core.

The attainment proof uses a fixed minimizing ray to bound the nonempty levels below and the directed-intersection theorem for nonempty compact closed sets.  No aggregate Busemann envelope is introduced.

The `NoncompactSpace M` hypothesis is essential here: it produces a basepoint minimizing ray and prevents the defining ray family from being empty.  Without it, every level could reduce vacuously to `univ`, so the set of nonempty real levels would have no minimum.

## Verification

Focused verification, the targeted module build, and the full-project build passed without a new warning or placeholder.  Direct axiom verification of the public minimum-level endpoints found only `propext`, `Classical.choice`, and `Quot.sound`.

## Frontier

The next Soul frontier is relative-boundary shaving of `rayMinCore`.  Ambient `frontier` is not a valid iterative boundary after dimension drop: a closed lower-dimensional carrier has empty ambient interior, so its ambient frontier is the carrier itself and its distance-to-frontier vanishes identically on the carrier.  The remaining genuine producers are an intrinsic or relative boundary, inner-parallel total convexity, strict dimension drop, and the terminal totally geodesic submanifold.

## Progress

The Soul theorem remains unstated and therefore 0%.  Its dedicated machinery is approximately 31--32% after verifying the minimum-core producer.  The whole B1 nonnegative-curvature lane remains approximately 22--25%, and the whole post-HCG Poincare program remains approximately 15--20%.
