# LowRegBgForceArms.lean

## Role

This module starts the fixed-background Galerkin forcing layer while keeping
the Sobolev scale and eigenbasis attached to the state metric.

## Current producers

`galN_evalBg` is the background-slot version of `galN_eval`.  It identifies
the dense fixed-background nonlinearity on a retracted Galerkin state with
`deTurckSmoothN g₀ g_bg 1` at the exhibited smooth representative.  The proof
uses the existing two-metric `lowRegN_on_smooth`; no new estimate is needed.

`galArmIdBg` rewrites the seed-subtracted forcing as the embedded sum of the
two arms from `lowBaseData g₀ g_bg`.  `galArmCapBg` reads the existing
two-metric `lowData_split` cap along the Galerkin trajectory, and
`galForceArmBg` exposes the resulting seed-plus-arms formula on each truncated
forcing coordinate.  All three are direct ports of the diagonal statements;
no new analytic hypothesis or estimate was introduced.

`galArmVecBg` is the background-slotted arm vector consumed by the rung mass
estimates.  Its Sobolev scale, Galerkin representative, and eigenbasis remain
on `g₀`; only the second `lowBaseData` slot is `g_bg`.

## Frontier

The force-arm layer required by route (c) is complete.  The former A1/C01
frontier has been closed upstream by `a1PerIdxLinBg`; the next consumer is the
proved sibling package in `LowRegBgRungThree.lean`.

## Verification

Focused verification and the targeted module refresh passed after adding
`galArmVecBg`, with the shared-workspace four-thread, 6144 MB limit.  The file
is warning-free and contains no `sorry`.

## Accounting

`galArmVecBg` and this force-arm module are complete (100%).  The verified
background rung stack is one of three rungs after `LowRegBgRungThree` (about
33% of that rung subphase); `lowreg_loMassBg` remains unstated (0%).  The
headline theorem `ricci_flow_unif_existence` remains unproved (0%); these files
are supporting route-(c) machinery, not the theorem itself.
