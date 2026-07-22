# BernsteinShiHigher

## 2026-07-18 noncompact boundary repair

`BernsteinTower` no longer carries `[CompactSpace M]`.  None of its stored
fields or algebraic/telescoping lemmas uses compactness; only the old global
maximum-principle consumers do.  `[CompactSpace M]` now appears directly on
`BernsteinTower.estimate` and `estimate_div`, preserving their closed-manifold
statements and existing callers.

The edited file passes its focused check, and its module was refreshed for the
new `BernsteinComplete` consumer.  This is an API-boundary repair only; it does
not prove the complete-noncompact maximum principle.

Honest accounting: the structural repair is 100%.  The closed estimate remains
100%.  The separate complete-noncompact estimate is theorem-level 0% until its
cutoff/exhaustion maximum principle is proved.  Unconditional
`compactnessSol` remains theorem-level 0%; whole-HCG support machinery remains
about 60%.

## 2026-07-22 reaction-cost monotonicity

`towerReactionSum_mono` and `TowerHeatBoundOn.mono_cost` now expose the
coefficient monotonicity needed by the corrected arbitrary-dimensional P4
producer.  The proof uses only nonnegativity of the three square-root factors;
it does not assume nonnegativity of the tower fields or hide a cost-domination
claim.  Focused verification passed.

This API brick is complete, but it is only routine infrastructure.  The direct
arbitrary-dimensional `towerHeatSol` theorem remains 0%; its dedicated
machinery is about 60-65%, with the level-zero rough-Laplacian/costed-residual
identity as the first genuine proof frontier.  Complete-noncompact Bernstein
also remains theorem-level 0% pending explicit cutoff/Kato localization.
