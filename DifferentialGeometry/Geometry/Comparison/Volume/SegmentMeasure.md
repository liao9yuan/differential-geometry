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
