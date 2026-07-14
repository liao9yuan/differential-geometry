# SolutionTowerHeat

## Purpose

Produce the solution-level `TowerHeatBoundOn` inequality on a strictly
positive-time tail in dimension three.

## Route

At each target `(t,x)`, reindex `smoothOrtho_local` by
`Fin 3 equiv Fin (finrank E)`. Use `resStarSol` for the fixed-cost residual,
`tailFrameTimeReg` and inverse uniqueness for the moving inverse metric,
`nablaKNormHeatAt` for the intrinsic time derivative, and
`nablaKReactionAt_le` for the reaction estimate. The output coefficient is
`towerSolConst k`, built from `resStarCost k`.

## Status

The full proof body for `towerHeatSol` has been written, but the theorem is
not yet verified and therefore counts as **0% complete**. Its dedicated
machinery is about **98%**. Focused verification is blocked before elaboration
by an active shared Spectral/Elliptic build that is temporarily rebuilding
transitive `.olean` files. The next action is the same focused check after that
build settles, followed by local shape repairs only; no new mathematical input
is currently known to be missing.
