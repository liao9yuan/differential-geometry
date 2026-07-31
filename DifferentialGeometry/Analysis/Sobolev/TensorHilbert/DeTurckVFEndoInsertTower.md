# DeTurckVFEndoInsertTower

## Current status

- The existing endomorphism-insertion tower remains unchanged.
- `wAlphaA_unit_apply` is now public.  It identifies the unit-model value of
  `wAlphaA` with the background-metric lowering of the covariant derivative of
  the DeTurck vector field.
- This is the narrow evaluation bridge needed by the intrinsic first-jet
  DeTurck RHS estimate; it does not add a second coefficient hierarchy.

## Verification

- Focused verification passed.
- The exact module refresh passed and the declaration is available to direct
  consumers.

## Project position

- `ricci_flow_unif_existence`: not proved (0%).
- Dedicated uniform-existence machinery: approximately 78%.
- The remaining E3/E6 frontier is the uniform first covariant jet of the full
  DeTurck RHS, followed by the `j ≤ 1` packet consumed by the extension theorem.
