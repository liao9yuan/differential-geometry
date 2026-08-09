# LowRegBgRungThree.lean

## Role

This module is the arbitrary-fixed-background mirror of the rung-three
Galerkin energy route.  The state Sobolev scale and spectral basis stay on
`g₀`; the Ricci--DeTurck coefficient and forcing use `g_bg` in their second
metric slot.

## Proved producers

- `armLadder3Bg` combines `a2PerIdxLin g g_bg` and
  `a1PerIdxLinBg g g_bg` into the rung-three jet-window ladder.
- `galArmMassOrdBg` converts that ladder to the ordered Galerkin arm-mass
  estimate.
- `lowregRung3OrdBg` runs the unchanged Grönwall/rider closure using
  `lowRegSeedMass g₀ g_bg`, `lowregNfun g₀ g_bg`, `galArmVecBg`, and
  `galForceArmBg`.
- `IsRung3OrdBg` records one coherent ordered certificate, and
  `lowregRung3PackBg` packages its witnesses.

## Binder-order invariant

`galArmMassOrdBg` selects `Kcap` before `{R δ}`.  Its proof calls
`lowData_split g₀ g_bg` directly; it deliberately does not derive the ordered
theorem from `galArmCapBg`, whose compatibility quantifiers select the cap
after `δ`.

The private scalar monotonicity helper is copied locally because the diagonal
file's private helper is not exported.  No new public algebra API was added,
and `LowRegRungThree.lean` was not modified.

## Verification

The focused four-thread, 6144 MB check passed without warnings.  The targeted
module refresh also passed.  The source contains no `sorry`, `admit`, `axiom`,
or heartbeat override.

## Frontier and accounting

The background rung-three package is complete (100%).  This verifies one of
the three rung-3/4/5 background packages (about 33% of that subphase).  The
next serial consumer is `LowRegBgRungFour.lean`; after rung four is refreshed,
rung five can be checked.

`lowreg_loMassBg` is still unstated (0%), and the later background gate,
adapted-solve, Fatou/path, higher-rung, and all-mass adapters remain.  The
headline `ricci_flow_unif_existence` theorem remains unproved (0%); the work
here is verified infrastructure only.
