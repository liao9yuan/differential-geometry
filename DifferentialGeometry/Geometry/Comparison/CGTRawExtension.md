# CGTRawExtension

## Scope

This file owns only the complete model-space extension of the raw framed-
exponential pullback metric and its inner/restriction agreement on the centered
core.  It does not contain minimizing joins, fences, curvature bounds, Jensen
arguments, or collision assembly.

## Route and reuse

- Reuse `CGTRawPullback.rawPullMetric` as the metric on `ball 0 R`.
- Use a private `ContDiffBump` equal to one on `closedBall 0 (3 * R / 4)` and
  supported in `closedBall 0 (7 * R / 8)`.
- Reuse `bumpExtendOpen_eq_gU_on` for pointwise and restricted agreement.
- Reuse `RiemannianMetricComplete.bumpExtend_complete` and
  `flatModel_complete`; finite-dimensionality supplies model-space completeness.
- No ambient `CompleteSpace M`, `ConnectedSpace M`, `SigmaCompactSpace M`,
  curvature, raw-domain, or positive-finrank hypothesis is introduced.

## Verification

Focused verification passed without warnings.  The first pass exposed only a
missing namespace opening, one malformed lambda arrow, and unused section
instances; the final version removes the unused boundaryless and tangent-bundle
T2 assumptions entirely.  There is no remaining proof or API blocker.

## Project accounting

- This narrow complete-extension producer: 100% implemented and focused GREEN.
- Dedicated P1b machinery: remains conservatively about 96%; this producer is
  one input to the still-unproved raw CGT final assembly.
- P1b endpoints E1/E2: both unstated and unproved, 0%.
- Aggregate P1 endpoints: eleven of fourteen, 78.6%.
- Whole Poincare theorem: unstated, 0%.
