# UnifRealizeRadius.lean — the explicit finite-action realization package

Status 2026-08-05: the finite rank-two package is implemented and awaiting its
dependency-ordered focused check.  The older all-order horizon theorem remains
as compatibility API.

## Content

- `LowRegRealizeData` separates the threshold and radius data from proofs.
- `IsLowRealizeUnif gBase Λ R` states that one pair has positive radius,
  threshold below one, and realizes every order-three class metric.
- `lowRealizeData` is the closed pair built from `morreyTwoC` and
  `unifPtCurvZeroC`.
- `lowRealize_unif_of` proves the package from two supplied fixed-background
  curvature caps.
- `exists_lowRealize` chooses those two caps before the variable class metric,
  producing one honest class-uniform package.
- `horizon_action_pos` inserts the finite-action radius into `lowregHorizon`.

## Route

The live route is finite and rank-specific.  Metric comparability plus jets
through order two give the rank-two Morrey coefficient.  Jets through order
three and fixed-background `R`/`nabla R` caps give `IsCurvAction0 g 2 K`.
`realize_at_action` then supplies the uniform fibre realization statement in
dimension three.  No all-rank curvature family is required.

## Boundary

This closes only the realization face of `IsLowBoundsAt`.  The A2, affine, and
nonlinear coefficient producers remain open, so the actual common envelope
`lowreg_bounds_unif` and the uniform-existence endpoint are still unproved.

## Verification

Pending restoration and verification of the native pointwise curvature-action
dependency, followed by focused checking of this module.
