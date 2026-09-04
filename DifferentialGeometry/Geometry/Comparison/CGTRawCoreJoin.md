# CGTRawCoreJoin

## Scope

This source-only slice carries the complete-extension minimizing join back to
the raw pullback ball.  It adds the codrestricted fenced join, a strict-budget
distance equality, and the raw-core specialization.  The target endpoint is
the local E1 Cheeger--Gromov--Taylor route, not a new global completeness
interface.

## Route

- `exists_raw_fenced` applies `rawExtJoin_fenced`, extends the curve slightly
  at its endpoints with the native time-window clip, and codrestricts it to
  `rawPullBall`.  Its inclusion agrees with `rawExtJoin` on `[0,1]` and is a
  raw-pullback geodesic by `rawPull_geo_of_ext`.
- `rawPull_edist_eq` compares the two distances under a strict budget.  The
  forward inequality uses the fenced minimizing join and the two path-length
  identities.  The reverse inequality excludes a shorter pullback curve by
  applying `rawPull_dist_zero` to every point of that curve.
- `rawCore_edist_eq` chooses the midpoint budget between `2*a` and
  `3*R/4`, obtains the extension bound from `rawExt_edist_le`, and applies the
  strict-budget theorem.

The whole-ball radial certificate `hdom` is passed unchanged.  It is the
actual producer input for `rawPull_dist_zero` at arbitrary points of a
competitor curve; endpoint-only certificates do not suffice.  No wrapper
predicate, ambient `CompleteSpace M`, `ConnectedSpace M`, ambient
`SigmaCompactSpace M`, curvature, Jensen, center-of-mass, or placeholder is
introduced.  The local `CompleteSpace E` and pullback sigma-compact instances
are constructed only where existing distance APIs require them.

## Verification status

The source-only integration audit matched every `hdom` binder verbatim with
`rawExtJoin_fenced` and `rawPull_dist_zero`, and confirmed the three public
names have lengths 17, 16, and 16.  Focused verification is warning-free
GREEN after the named `CGTRawExtJoin` artifact refresh.  The one local repair
was to use the existing pullback tangent norm, normed-space, and ENorm-scalar
instances, and to give `IsContinuousRiemannianBundle` its model-space `E`
parameter exactly as in the native intrinsic proof.  No new theorem premise
was introduced.

## Project accounting

- This codrestriction and distance slice: source-written and focused GREEN,
  100% complete.
- E1 endpoint theorem: unstated and unproved, 0%.
- Dedicated P1b machinery: conservatively about 97% verified.
- P1 endpoints: eleven of fourteen, 78.6%; the whole Poincare theorem remains
  unstated, 0%.
