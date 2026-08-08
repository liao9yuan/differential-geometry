# LowRegBgRungFour.lean

## Role

This sibling ports the complete rung-four Galerkin arm estimate and energy
closure from `LowRegRungFour.lean` to an arbitrary fixed DeTurck background
`g_bg`.  The spectral basis, Sobolev scale, trajectory, and energy remain based
at the state metric `g₀`.

## Source state

The source port contains the five intended public declarations:

* `armOrder3Bg`;
* `galArmMass4OrdBg`;
* `lowregRung4OrdBg`;
* `IsRung4OrdBg`;
* `lowregRung4PackBg`.

The scalar binder order is unchanged from the diagonal theorem.  In particular,
the four absorption constants are selected before the solve radius, fibre
threshold, realization witness, and prior rung-three cap.  Only the DeTurck
background slots were changed.  The private scalar helper `mul4Le` is duplicated
locally because the diagonal copy is private.

Static inspection found no new analytic or geometric API seam.  The port uses
the planned lower declarations `armLadder3Bg`, `galArmVecBg`, and
`galForceArmBg`, the already two-metric `lowData_split`, `lowRegSeedMass`,
`coreN`, and `lowregNfun`, and the arbitrary-background per-index estimates.
After normalizing only the expected declaration names and background arguments,
each of the five source bodies is textually identical to its diagonal source.

## Verification

Focused verification passed without diagnostics after the lower
`LowRegBgRungThree` export became fresh.  The targeted module refresh also
passed, and the resulting `LowRegBgRungFour.olean` is newer than the source.
The file contains no `sorry`, `admit`, added axiom, or heartbeat override.

Accordingly `lowregRung4OrdBg` and this isolated fixed-background rung-four
brick are 100% complete.  This closes only the conditional rung-four producer;
it does not provide the class-first calibration or the low-mass conclusion.

The headline `ricci_flow_unif_existence` remains 0%; this file is conditional
background bootstrap infrastructure and does not itself supply class-first
calibration or the low-mass endpoint.
