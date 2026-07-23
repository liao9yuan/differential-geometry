# ResidualBase

## Purpose

`ResidualBase.lean` is the solution-facing join between the arbitrary-dimensional
Hamilton evolution and the quantitative `StarSum2` ledger.  It stays separate
from `ResidualCost.lean`, which owns only the cost algebra and reaction
realization.

## Current status (2026-07-22)

- `e0Residual` is the fixed-witness level-zero producer for the direct
  arbitrary-dimensional residual recursion.  `rmResidual_zero` remains the
  existential compatibility wrapper.
- The fixed witness is the canonical `e0Field`; its cost is exactly
  `rmResidualCost (Fintype.card Idx) 0`.
- The proof consumes `rm04Base_of_solution_any`, `e0Field_cost_any`, and
  `e0Field_comp_any`; it introduces no new geometric or regularity assumption.
- Focused verification of the fixed-witness API is GREEN with no diagnostics.
  The earlier existential API was exact-current; the next narrow downstream
  refresh is the authoritative exact check for this source change.
- Its axiom audit is the standard `[propext, Classical.choice, Quot.sound]`.

## Remaining frontier

The arbitrary-index successor is now focused-green.  The remaining assembly
work is to make its commutator and Christoffel-correction witnesses explicit
global fields and recurse on that fixed output.  The level-zero producer is
100%; `rmResidual_cost` remains theorem-level 0% until that fixed-witness
induction is assembled.  Dedicated direct-tower machinery is about 94%.
