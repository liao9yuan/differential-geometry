# RawRadialFrame

## Raw interval parallel frame (2026-09-01)

### Mathematical route

`exists_raw_frame` is the raw counterpart of `exists_intrFrame`.  It first
uses `Exponential.exists_raw_ray_ext` to replace a radial exponential curve on
`Icc 0 L` by a globally smooth curve with the same germ at every segment time.
The existing global `exists_parallel_frame` theorem supplies an orthonormal
parallel frame along that extension.  The frame is then retyped through the
common model fiber `E`, and `chartRep_congr_curve` plus
`covDerivAlong_congr_curve` transfer differentiability and parallelism back to
the raw curve.  Point equality from the same germ transfers orthonormality.

The public theorem splits off the zero-dimensional case, so it does not expose
the positive-finrank instance retained by the global transport implementation.
It adds no completeness, metric-space, compactness, or new frame-data
predicate.

### Reuse and rejected routes

The proof reuses the already-checked transfer pattern from `BallVolume` and the
canonical global parallel-frame producer.  Rebuilding parallel transport from
the local chart ODE would duplicate chart stitching and inner-product
preservation.  Moving the generic germ lemmas to a lower module is unnecessary
for this acyclic comparison-layer consumer.

### Verification

The exact upstream `Domain` artifact refresh passed, after which this file
passed focused verification without warnings.  The only source repair was a
dependent-basepoint display normalization in the orthonormality transfer; the
mathematical route and public assumptions were unchanged.  No refresh of this
new module has run because its next consumer is not yet source-written.

### Progress

This is dedicated P1b machinery only.  The exact incomplete-ambient E1 and E2
injectivity endpoints remain unstated and therefore remain at 0% theorem
completion.
