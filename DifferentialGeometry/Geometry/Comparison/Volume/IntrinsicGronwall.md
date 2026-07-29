# IntrinsicGronwall

## Current additions

- `intrJacobi_pair` gives simultaneous metric-norm bounds for an intrinsic
  Jacobi field and its covariant velocity.
- `intrForce_pair` packages the parallel-frame and chart-regularity work for a
  general smooth inhomogeneous field along a complete intrinsic geodesic.

Both additions are source-complete. Focused verification is pending the current
writer handback and exact refresh of the new `covGronwall_pair_at` export.

## 2026-07-27 intrinsic curvature ODE producer

Added `intrJacobi_ode`.  The proof combines the canonical Jacobi equation,
constant intrinsic-geodesic speed, and `riemannOp_sq_le` to produce the exact
second-order inequality consumed by `intrJacobi_bounds`.  Its Gronwall constant
is

`sqrt(dim) * R * g_p(u,u)`,

so launch vectors of size `r` contribute the required `R * r^2` scale.  The
curvature package now covers `Ico 0 1`; this is honest for the sequence
bounded-geometry producer and removes a separate zero-time coercion proof.

Focused verification passed without diagnostics.  The H6 profile theorem
itself remains unstated and therefore 0%; its dedicated zero-order machinery
is now approximately 99%, with scalar radius selection and final assembly
remaining.

## Purpose

This module specializes the abstract covariant Gronwall theorem to complete
intrinsic geodesics and their initial-velocity Jacobi fields. It removes all
chart-radius obligations from the analytic transfer.

## Status

`intrJacobi_bounds` is proved without `sorry`/`admit`/`axiom` and passes focused
verification. It derives:

- global smoothness of the intrinsic geodesic;
- a full parallel orthonormal frame on the requested positive interval;
- differentiability of the Jacobi field and its covariant derivative;
- the initial identities `J(0) = 0` and `D_t J(0) = w`;
- the two-sided covariant Gronwall estimate.

The only remaining input is the pointwise second-order curvature inequality
`|D_t^2 J|^2 <= K^2 |J|^2`.

## Progress

- Intrinsic Gronwall specialization: 100% proved and focused-checked.
- Rm04 fiber norm to intrinsic Jacobi ODE bound: 0%. This is now the single
  zero-order geometric frontier below the final H6 scalar-radius assembly.
- Sequence-uniform H6 relative profile theorem: 0%.

## Next Target

Prove a reusable pointwise curvature-operator estimate at the geometry layer:
the metric norm of `R(J,V)V` is bounded by the `(0,4)` Riemann tensor fiber
norm times `|J| |V|^2`, with the explicit finite-dimensional factor. Instantiate
it with the constant speed of `intrinsicGeodesic` and the sequence-wide
`rm04Bound_of_seq`, then feed `intrJacobi_bounds`.
