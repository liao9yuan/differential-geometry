# LowRegBgHigherRung.lean

## Role

This sibling supplies the arbitrary-fixed-background higher-rung mass brick.
The Sobolev scale, eigenbasis, Galerkin state, and energies remain attached to
`g₀`; only the DeTurck remainder and nonlinear forcing use `g_bg`.

## Verified producers

`galArmMassHmBg` is proved. It consumes `IsHmRungOrdBg`, transports its
all-order remainder estimate through `galArmVecBg`, and uses
`lowData_split g₀ g_bg` to identify the exact `a₂ + a₁` arm.

`lowregHighRungsBg` is also proved. It consumes the verified
`IsRung5PathBg` path certificate and ports the diagonal higher-rung argument
with `galArmMassHmBg`, `galArmVecBg`, `galForceArmBg`,
`lowRegSeedMass g₀ g_bg`, and `lowregNfun g₀ g_bg`. The scalar ordering,
absorption hypothesis, and conclusion are unchanged. No new analytic API or
additional hypothesis was introduced.

Focused verification passed after restoring the two namespace opens used by
the public type aliases. The single-thread targeted refresh also passed, and
the resulting export is newer than the source. The file contains no `sorry`,
`admit`, added axiom, heartbeat override, inferred theorem result, or residual
diagonal background slot.

## Remaining route boundary

This file deliberately stops at the single higher-rung brick. The separate
`lowregAllRungsAtBg` / `lowregAllMassAtBg` composition and the final
`lowreg_loMassBg` endpoint remain outside its scope.

## Accounting

Both declarations are 100% complete, so this minimal HigherRung background
brick is 100%. Route-(c) brick 7 remains partial until the all-rung/all-mass
composition is exported. The broader background/adapted infrastructure is
approximately 70%, while `lowreg_loMassBg` and headline
`ricci_flow_unif_existence` remain unstated and therefore 0%.
