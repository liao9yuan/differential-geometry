# PrincipalResidualH2

## Purpose

This module defines the canonical zero-based smooth Ricci--DeTurck residual
after subtracting the completed/smooth moving-cometric principal arm.

## Current result

- `principalResidual` is the intrinsic smooth residual with no second
  connection-Laplacian subtraction.
- `principalResidualH2` uses the completed `lowRegPrincipal` operator.
- `residualH2_core` identifies the completed and smooth definitions on the
  smooth metric core.
- `residual_split_h2` gives the exact canonical split
  `residual = (full A2 - principal) + A1` and retains the sharp diagonal
  `H3 -> H2` estimate for `A1`.
- `lowBaseResidual` subtracts the complete canonical `A2`, and
  `lowResidual_diag` proves that it is exactly `A1` with the diagonal
  `H3 -> H2` jet bound.

## Remaining frontier

The requested `H3 -> H2` estimate for the whole principal-subtracted residual
does not follow from the current action split.  Subtracting only
`lowRegPrincipal` leaves the genuine second-order term
`L.a2 T - deTurckPrincipalCometricArm ... T`.  The old all-order decomposition
likewise estimates this term with a small coefficient multiplying two extra
state derivatives.  Therefore an `H3 -> H2` bound for the whole residual would
silently misclassify the extra second-order action as first order.

The correct next step is to include the complete canonical `L.a2` in the
nonautonomous `A2` operator and use `lowBaseResidual` for the rank-one `A1`
time operator.  Pairwise completed `H3 -> H2` continuity of
`lowBaseResidual` is not yet proved; no conditional facade is introduced.

## Verification

Focused verification and the targeted exact module refresh both passed with
no Lean errors.  The source has no `sorry`, `admit`, axiom declaration,
`whnf`, or trace command.

## Progress accounting

- canonical principal-subtracted residual definitions and core split: 100%;
- whole-residual diagonal `H3 -> H2` estimate: 0% because its proposed
  statement omits the remaining second-order action;
- `(N) ricci_flow_unif_existence`: theorem 0%; dedicated machinery remains
  approximately 97%.
