# ResidualCost

## Purpose

This module owns the explicit arbitrary-dimensional constructor ledger for the
direct curvature-tower route.  It does not state or assume the missing
arbitrary-dimensional residual theorem.

## Route

`rmResidualCost d 0 = 12 d^2`.  The successor adds two copies of the previous
residual, the existing generic `commStarCost d k`, and the Christoffel-time
cost `d^2 (12 + 3k)`.  `rmTowerCost` then uses the exact coefficient shape
consumed by `nablaKReactionAt_le`.

The specialization theorem `rmResidualCost_three` proves that this recurrence
is exactly the existing checked `resStarCost`, rather than a newly chosen loose
bound.

The level-zero constructor is now separated from the three-dimensional
curvature identity.  `e0Field_cost_any` proves the exact arbitrary-index cost
`12 * card(Idx)^2`; `rmBaseReact` records the eight-term quadratic curvature
expression; and `e0Field_comp_any` proves that `e0Field` realizes this
expression in every finite orthonormal basis.  None of these lemmas uses
Weyl-flatness or `Fin 3`.

## Status

The definitions, nonnegativity/specialization lemmas, and arbitrary-index
level-zero cost/component lemmas pass focused verification.  The
arbitrary-dimensional `residualStarCosted` and `towerHeatSol` theorems remain
theorem-level 0%.

The first missing theorem is the arbitrary-dimensional Hamilton identity
turning `realizedRmBase_timeDeriv`'s expanded `nabla^2 Ric` expression into
`roughLap Rm04 + rmBaseReact`.  The generic Uhlenbeck cancellation theorem
still consumes that pre-Uhlenbeck evolution as an input, while the existing
solution producer `rm04Base_of_sol` is dimension three.  The successor
residual construction is also currently specialized to `Fin 3`; it should be
generalized only after the base identity is settled.

The ledger and level-zero algebra brick is 100%.  Dedicated direct-tower
machinery is about 60-65%, while the whole P4 analytic producer remains
incomplete.
