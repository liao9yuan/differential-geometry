# SegmentMeasure

## Purpose

This module changes the exponential-Jacobian integral from the arbitrary chart
basis and `modelHaar` normalization to the center-metric orthonormal basis and
canonical model volume.  The basis determinant and Haar determinant cancel in
one step; no claim that `modelHaar` itself is canonical is made.

It also records that `normalFrame` pulls `gBall` back to the ordinary model
ball.

## Status

`preimage_gBall` and `expJac_normal_int` are proved.  Focused verification
passed without diagnostics.

## Project accounting

These measure-normalization producers are complete (100%).  They are dedicated
machinery for the absolute segment-ball comparison; `segBall_vol_le` and
`segBall_vol_rel` remain theorem-level 0% until their bodies are proved.

## 2026-07-28 framed multiplicity bridge

Added `framed_mul_le_area`, the normal-frame/canonical-volume form of the
multiplicity-weighted area inequality.  Local measurable-space instances keep
the statement at the existing volume-comparison layer and avoid leaking
normalization choices into `CGTInjectivity`.

Focused verification and the exact module refresh passed.  The earlier
`segBall_vol_le` and `segBall_vol_rel` consumers are also already proved; the
stale theorem-level 0% sentence above records the earlier state only.

The framed bridge is 100%, its dedicated normalization machinery is 100%, and
the downstream pointwise CGT theorem is now 100%.
