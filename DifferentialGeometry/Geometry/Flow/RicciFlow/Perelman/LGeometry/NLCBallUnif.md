# NLCBallUnif

## Role

This module is the uniform controlled-ball reduced-volume upper-bound assembly
for the compact ordinary smooth-flow L-geometry lane.  It keeps compactness only
at the final L9 consumer, where it supplies completeness of every time-slice
metric through `RiemannianMetricComplete.of_compact`.

## Source state

- `ballVol_local_unif` applies the set-local volume comparison only on the
  terminal closed radius-`1/32` ball.  The moving metric is compared with the
  terminal metric there by `lMetric_ball`; the closed ball is then included in
  the original terminal open ball whose measure is `B.volume`.
- `lRedJac_ball_unif` obtains `lRegRange_unif` once.  Its moving radius-`1/16`
  witness supplies `lRedLen_of_range`, while its terminal radius-`1/32` witness
  controls the image set passed to `lRedJac_set_le`.  The source cutoff is
  `1 / (128 * sqrt eps)`.
- `redVolume_ball_unif` chooses its short-time threshold after `rho` and `eta`
  but before the flow, terminal time, controlled ball, and actual `eps`.  It
  combines the local good-source estimate, `lSrcGauss_unif`,
  `lRedJac_tail_le`, `redVolume_lint`, and `redVolume_split`.

No global curvature bound, noncompact completeness assumption, stronger
consumer hypothesis, new class, frontier wrapper, `sorry`, or `admit` is used.

## Verification

The complete module is warning-free focused green.  Its named artifact was
refreshed once `SmoothNLC` became a real source-written downstream consumer.

## Downstream consumer

The compact smooth-flow `smooth_nlc` assembly now imports this module and
combines `redVolume_ball_unif` with the checked uniform positive lower bound.
That capstone is warning-free focused green and named-refreshed.

## Progress accounting

- `ballVol_local_unif`, `lRedJac_ball_unif`, and `redVolume_ball_unif`: each
  **100%** theorem endpoints and warning-free focused green.
- Their dedicated uniform L9 machinery: **100%** for this reduced-volume upper
  assembly.
- Reused generic infrastructure: **100%** for the declarations consumed here.
- `smooth_nlc`: **100%** as a dimension-generic compact ordinary-flow theorem.
- `redVolume_anti`: **100%**.
- Whole P0--P9 infrastructure: about **15--25%**.
