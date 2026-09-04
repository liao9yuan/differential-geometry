# Raw pull volume

## Purpose

`rawPullVol` is the unframed-coordinate pull volume of the normal-frame image
of the Euclidean model ball.  Its integrand is the raw exponential map's
chart-basis `mapJacDensity`, so the pointwise comparison does not detour through
a framed determinant or require completeness/minimizing hypotheses.

`rawPullVol_le_eucl` is the intended P1b producer.  Its hypotheses are exactly
full radial-domain coverage on the image ball, injectivity of the raw
exponential differential at every positive radial time, and nonnegative radial
Ricci curvature.  The conclusion bounds `rawPullVol` by the Euclidean volume of
the model ball.

## Route

For each launch vector, `raw_exp_density` identifies the raw chart-basis map
Jacobian with the radial Jacobi density; that public identity is backed by
`radial_jacobi_dom`.  The all-launch theorem `rawDens_le_of_inj` then bounds the
integrand by the pole density.  Set-lintegral monotonicity reduces the integral
to the constant pole density.  Finally `normalHaar_eq`, evaluation of the
measure map on the measurable image ball, and injectivity of `normalFrame`
transport that constant integral back to ordinary Euclidean ball volume.

This route directly consumes the unframed density theorem.  No further
basis/determinant adapter is needed; the only coordinate-to-measure bridge is
the already-native `normalHaar_eq` identity.

## Verification

The source contains the complete definition and proof and introduces no
`sorry` or new assumptions.  The parallel-window preflight stopped only at the
deliberately stale `rawDens_le_of_inj` export.  After its exact upstream
artifact refresh, the proof elaborated fully; that pass exposed only a
gratuitous `SigmaCompactSpace M` section instance.  The public theorem now
explicitly omits that instance, and the final focused check is warning-free
GREEN under the weaker signature.

## Accounting

`rawPullVol_le_eucl` is stated, proved, and warning-free focused verified.
This completes this dedicated pull-volume producer, but it does not by itself
complete either P1b theorem endpoint; the recorded P1 and whole Poincare
endpoint percentages are unchanged.
