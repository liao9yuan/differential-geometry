# CGTRawExtJoin

## Scope

This file owns the model-space minimizing join for `rawExtMetric`, together
with its first-hit agreement-core fence.  It uses `rawExt_complete` to choose
`minJoin`, and supplies its two endpoint, smoothness, extended-geodesic, and
fenced-core facts.  The zero-dimensional branch is kept internal so the public
interface has no `NeZero` premise.

## Verified route

- `rawExtJoin` installs only the model-space Riemannian, pseudo-emetric,
  uniform, and complete instances needed by the existing `minJoin` API.
- `rawExtJoin_eq_min` is the positive-model-dimension identification with that
  same complete-extension `minJoin`, including its metric-norm witness.  It is
  the low-level bridge for consumers that already have a nonzero-dimension
  proof and must compare `rawExtLaunch` with the canonical minimizing launch.
- `rawExtJoin_zero`, `rawExtJoin_one`, `rawExtJoin_smooth`, and
  `rawExtJoin_geo` are direct specializations of the established complete
  Riemannian minimizing-geodesic API.
- `rawExtJoin_fenced` takes the native raw-pull-ball radial certificate
  `hdom`.  Its first-hit proof restricts the minimizing join to the first
  `3 * R / 4` boundary hit, transfers that prefix to `rawPullBall`, and uses
  `rawPull_dist_zero` at the initial point and hit point to contradict the
  extension distance budget.  `rawExt_edist_le` needs only the two endpoint
  specializations of this same `hdom` certificate.
- The source is warning-free under focused verification and adds no
  `CompleteSpace M`, `ConnectedSpace M`, ambient `SigmaCompactSpace M`,
  curvature, Jensen, center-of-mass, wrapper predicate, or placeholder.

## Verification status

`rawExtJoin_eq_min` is warning-free focused GREEN.  It required one local
repair: the positive-dimension witness is installed in the theorem result as
well as in its proof, so the displayed `minJoin` term elaborates with the same
canonical instance as `rawExtJoin`.  No artifact refresh was requested.

## Fence input boundary

Two endpoint radial certificates alone do not certify the first boundary-hit
point of an arbitrary minimizing join.  The global raw-pull-ball `hdom` is
therefore the honest final raw-route input: it is exactly the certificate
consumed by the native `rawPull_dist_zero` producer at that first-hit point,
not a wrapper assumption.  The file intentionally stops after the fence; it
does not add a codrestriction, an existential fenced curve, or an extended/
pullback distance equality.

## Project accounting

- Complete-extension minimizing-join and fence slice (`rawExtJoin` through
  `rawExtJoin_fenced`): source-written and focused GREEN, 100%.
- Dedicated E1 endpoint theorem: unstated and unproved, 0%.
- Dedicated P1b machinery: conservatively about 97%.
- P1 endpoints: eleven of fourteen, 78.6%; the E1 endpoint remains unstated
  and unproved, 0%.
- Whole Poincare theorem: unstated, 0%.
