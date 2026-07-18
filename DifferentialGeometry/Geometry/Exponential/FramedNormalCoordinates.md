# FramedNormalCoordinates

## Purpose

`FramedNormalCoordinates.lean` packages genuine Riemannian normal coordinates
at a fixed center. It first identifies the model space with the tangent space
through the chosen `g_p`-orthonormal `normalFrame`, then applies the exponential
map.

## Status

Focused verification and the targeted module build pass. The file is
sorry-free.

- `framedExpDiffeo` is the raw exponential local diffeomorphism conjugated by
  `normalFrame`.
- `framedChartAt` is its inverse coordinate map.
- `framed_norm_lt_iff` proves that a model Euclidean ball is exactly the
  corresponding `g_p` tangent ball under the frame.
- `framedExp_mem_of_lt` uses the existing intrinsic `expRadiusGp` to place a
  model point in the framed exponential source, without exposing a raw
  model-norm radius.
- `framedExp_zero` and `framedChart_centre` identify the chart center.
- `framedTransition` is the canonical overlap map
  `framedChart_q o framedExp_p`.
- `framedExp_eq_expMap` exposes the underlying exponential map.
- `mfderiv_framedExp` identifies the chart differential as the raw exponential
  differential composed with `normalFrame`.

The construction is pointwise in the center. It intentionally makes no claim
that the classically chosen frames vary smoothly with the center; the current
HCG use chooses charts at finite or discrete center families.

## Next Consumer

The generic injectivity-radius API and the Chapter-4 normal-coordinate input
still use raw model-space balls. Their canonical H6-facing semantics should be
the intrinsic tangent ball, equivalently the model ball transported by
`normalFrame`. This migration must be coordinated with the B/C consumer lane.
