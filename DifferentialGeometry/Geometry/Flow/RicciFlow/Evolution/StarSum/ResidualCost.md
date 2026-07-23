# ResidualCost

## Purpose

This module exports the explicit arbitrary-dimensional constructor ledger for
the direct curvature-tower route.  The recurrence itself now lives in the
lower `ResidualLedger` module so `TimeRecursion` can consume it without an
import cycle.  This module does not state or assume the missing
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
`12 * card(Idx)^2`; `rmBaseReact` is a compatibility alias for the canonical
static `hamiltonRmReact`; and `e0Field_comp_any` proves that `e0Field` realizes
this reaction in every finite orthonormal basis.  None of these lemmas uses
Weyl-flatness or `Fin 3`.

## Status

The definitions, nonnegativity/specialization lemmas, and arbitrary-index
level-zero cost/component lemmas pass focused verification; the exact targeted
refresh is GREEN (`3798/3798`).  The
arbitrary-dimensional `residualStarCosted` and `towerHeatSol` theorems remain
theorem-level 0%.

The arbitrary-dimensional Hamilton identity and its fixed-basis solution
producer are now exact-current as `hamiltonRm04Id` and
`rm04Base_of_solution_any`.  The solution-facing level-zero join is now
exact-current as `rmResidual_zero` in `ResidualBase.lean`.  The next theorem is
the arbitrary-index successor; the existing successor residual construction
is still specialized to `Fin 3`.

The ledger and level-zero algebra brick is 100%.  Dedicated direct-tower
machinery is about 92%, while `residualStarCosted`, direct `towerHeatSol`, and
the whole P4 analytic producer remain theorem-level 0%.
