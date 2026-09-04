# RawRadialGronwall

## Purpose

This module is the raw-domain replacement for the old small-radius Jacobi
nonvanishing route.  It assembles the existing closed-interval raw Jacobi
regularity, raw parallel frame, curvature-square estimate, and covariant
Gronwall theorem.  The public theorem keeps completeness and the positive-
finrank assumption out of its signature; a nonzero Jacobi launch direction
supplies positive finrank internally.

## Route

- `exists_raw_frame` supplies the fixed orthonormal parallel frame required by
  `covGronwall_ne_zero_at`.
- `radial_jacobi_on`, `radial_jacobi_at0`, `radial_jacobi_reg`, and
  `radial_jacobi_d0` supply the Jacobi equation, pole closure, interval
  regularity, and initial derivative.
- `curv_sq_of_rm04_velocity_Ioo` converts pointwise `Rm04` and speed bounds into
  the second-order inequality; no new curvature operator wrapper is added.
- `gronwallBound_zero_mul_eps` scales the unit initial-data smallness condition
  by the actual nonzero launch norm.

The older `mfderiv_exp_injective_of_jacobi` remains on its small-radius route
and is not reused here.  The next consumer should combine time-one
nonvanishing with `radial_jacobi_dom` to obtain raw exponential derivative
injectivity, then use the existing framed derivative/local-diffeomorphism API.

## Verification

`rawJacobi_ne_of_rm` and its direct `rawExp_mfderiv_inj` consumer are
warning-free focused GREEN.  The newly exported raw pole-Jacobi and raw-frame
dependencies received exact downstream-required refreshes before this check.
The first check exposed only namespace qualification; the second only the
dependent pole equality, both repaired locally.

## Accounting

Both public producers are verified.  P1b endpoint E1 and E2 remain unstated at
0%; this file is dedicated machinery only.  P1 stays
at eleven of fourteen verified endpoints (78.6%), and the whole Poincare
theorem endpoint remains 0%.
