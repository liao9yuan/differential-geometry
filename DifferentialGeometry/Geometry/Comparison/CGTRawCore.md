# CGTRawCore

## Scope

This module contains exactly the four basic raw-core declarations
`rawZero`, `rawZero_mem`, `rawCore_compact`, and `rawPull_dist_zero`.  It does
not start minimizing joins, strict Jensen, center of mass, propeller
iterations, fiber counting, or injectivity assembly.

## Result

Focused verification passed without warnings on the first elaborating check.

- `rawZero` realizes the origin in a positive-radius `rawPullBall`.
- `rawZero_mem` places it in every nonnegative-radius norm core.
- `rawCore_compact` identifies the subtype image of the core with the closed
  finite-dimensional model ball.
- `rawPull_dist_zero` identifies pullback Riemannian distance from `rawZero`
  with the model norm.

## Distance route

For the upper bound, the canonical clamped radial curve `rawFlatRay` stays in
the raw pullback ball.  `rawPull_pathLen` transfers its pullback length to its
raw framed-exponential image, and `rawFlatPath_len` supplies the exact endpoint
norm.

For the lower bound, any hypothetically shorter pullback path is projected to
the model space.  `rawPull_pathLen` identifies its pullback length with the
length of its raw framed-exponential image, while `rawLift_norm_le` applies the
raw Gauss pullback inequality to force the endpoint norm below that length.

The statement therefore keeps radial `expDomain` coverage explicit for every
endpoint of the raw pullback ball.  This is the weakest path-independent input
supported by the current lower-bound API: local diffeomorphism is used for the
pullback metric and exact length transport, but is not treated as a proof of
raw radial-domain coverage.

## Assumptions

No ambient completeness, ambient connectedness, `SigmaCompactSpace M`,
positive-finrank, curvature, minimizing-join, strict-Jensen, or center-of-mass
hypothesis is added.  A sigma-compact instance is constructed locally only for
the finite-dimensional open model ball carrying the pullback metric.

## Proof notes

No mathematical, API, coercion, or verification blocker remains.  No failed
proof route was needed.

## Program accounting

- The four raw-core basics in this module: complete (100%).
- Raw-core strict Jensen and its center-of-mass consumer: not started in this
  module (0%).
- `framedInj_ge_vol`: not yet declared or proved (0%); its dedicated raw P1b
  machinery remains approximately 96% complete.
- P1b endpoints: zero of two (0%).
- P1 overall: eleven of fourteen endpoints (78.6%).
- Final `poincare_of_inputs`: not declared (0%); whole P0--P9 infrastructure
  remains at the program authority's 15--25% estimate.
