# CGTRawBigon

## Scope

This module starts the raw short-bigon route with the fence producer
`rawExt_short_fenced`, its local pinned-exponential consumer
`rawExt_pinned_inj`, and the private compact bad-bigon layer
`rawShort_compact`.  The public short-endpoint injectivity theorem
`rawCore_short_inj` is not yet stated: its global no-return input is still
missing from the raw API.

## Route

For a complete-extension launch, take the first time it reaches the agreement
boundary.  The private prefix-length bound comes from the existing complete
intrinsic-geodesic speed API.  Reparametrizing that prefix into `rawPullBall`
transfers its length through `rawPull_pathLen` and `rawExt_pathLen`.
`rawPull_dist_zero` at the start and first-hit points then gives
`3 * R / 4 ≤ a + L`, contradicting the strict budget.

The theorem keeps the raw whole-ball radial `hdom` certificate unchanged: it
is required at the first-hit point by `rawPull_dist_zero`.  The native
`rawExtLaunch` API is positive-dimensional, so the theorem inherits its
canonical `NeZero (finrank Real E)` instance and no stronger premise.  It adds
no wrapper predicate, ambient completeness/connectedness/sigma-compactness,
curvature, center-of-mass, or unproved declaration.

The available `rawPull_edist_eq` core theorem is deliberately not used: its
core-only `h4aR` hypothesis is stronger than, and not implied by, this launch
budget.  The prefix-length route is the direct raw analogue of the native
short-launch fence and preserves the intended `a + L < 3 * R / 4` interface.

For the pinned consumer, that budget first supplies the raw launch fence, and
`rawExt_no_conj` makes the velocity derivative of the complete-extension
exponential injective.  The native pinned-root map and local inverse theorem
then give an injective neighborhood for `(F z, z.1)`.  This is a local
exponential producer only; it does not state a distance equality or a
short-injectivity endpoint.

`rawShort_compact` is the raw compactness/diagonal step.  It keeps the same
short-bigon data as the endpoint argument and uses the preceding local
injectivity result only to close the deleted diagonal.  The finite-dimensional
box bound is kept an explicit input, so no completeness or compactness
assumption on the original manifold is introduced.

The next honest raw bridge is strict convexity of the squared raw coordinate
radius along fenced extension geodesics (the raw counterpart of
`intrOrigin_strict`).  The available raw APIs prove nonconjugacy and branch
Hessian positivity, but do not identify the origin exponential with the
coordinate radial ray or expose that branch energy as squared coordinate
radius.  Without that bridge, compact bad bigons cannot be excluded globally.

Three source routes were checked.  There is no raw-to-intrinsic extension
metric/launch equality that would permit reuse of `intrCore_short_inj`; the
intrinsic route also has forbidden ambient completeness and compactness
requirements.  Porting `intrExt_edge_core` stops at its use of
`intrOrigin_strict`, whose raw counterpart is absent.  Finally,
`rawCore_min_regular` controls only the canonical minimizing vector and cannot
rule out an arbitrary nonminimal bad-bigon launch.  The smallest semantic next
lemma is a raw-origin strict-convexity theorem, built from the preceding
radial-identity bridge for `rawExtLaunch` at zero; it should live below this
endpoint consumer.

## Verification status

Warning-free focused verification is GREEN.  The first elaboration exposed the
native positive-dimension launch requirement and a local metric-instance
mismatch in the private length bridge; the former is now stated canonically and
the latter is resolved by placing the bridge in the same raw-extension metric
scope as its consumer.  No artifact refresh was requested.

`rawExt_pinned_inj` is warning-free focused GREEN.  Its earlier check
exposed an API leak rather than a geometric obstruction: local pullback
curvature naturality unnecessarily inherited target sigma compactness.  That
canonical lower theorem now transports sigma compactness between its local
source and target opens, while the raw pullback derives base Hausdorffness from
the already-present tangent-bundle instance.  Consequently this theorem keeps
its original weakest assumptions.  The earlier product-topology elaboration
issue was removed by stating the local result with `rawExtLaunch ... 1`, while
keeping the intrinsic exponential only in the proof body.

`rawShort_compact` is warning-free focused GREEN.  It is private support for
the endpoint and has no public assumptions beyond its explicit continuous,
local-injectivity, and box-bound inputs.

## Project accounting

- `rawExt_short_fenced`: warning-free focused GREEN (100% of this helper).
- `rawExt_pinned_inj`: warning-free focused GREEN (100% of this helper).
- `rawShort_compact`: warning-free focused GREEN (100% of this private helper).
- Dedicated raw short-bigon machinery: roughly 25% verified progress; the
  public `rawCore_short_inj` endpoint is unstated and unproved (0%).
- P1 endpoints: eleven of fourteen (78.6%); the whole Poincare theorem remains
  unstated (0%).
