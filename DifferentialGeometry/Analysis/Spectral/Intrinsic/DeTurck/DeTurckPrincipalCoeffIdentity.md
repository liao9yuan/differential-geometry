# DeTurckPrincipalCoeffIdentity

## Role

This small intrinsic module exposes the exact structural identity needed to
compare the Ricci principal coefficient with the canonical DeTurck cometric
coefficient.  It deliberately contains no Sobolev-ball or all-order estimates.

## Current state

- `ricci2_pcc_eq` is the public identity.
- Its proof is the fixed fibrewise multilinear calculation already used by the
  principal-cometric extraction layer.
- Focused verification and the exact targeted module refresh passed.

## Project position

This is a producer for the canonical low-base `C₂` pair estimate.  The final
uniform existence theorem remains unstated and unproved (0%); its dedicated
low-base machinery is approximately 98% complete.
