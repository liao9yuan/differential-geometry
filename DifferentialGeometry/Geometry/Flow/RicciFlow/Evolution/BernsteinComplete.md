# BernsteinComplete

## 2026-07-22 architecture correction

`BernsteinTower.estimate_complete` must not be proved under its current
signature.  Uniform metric equivalence and an evolving-metric Ricci lower
bound do not control the evolving Laplacian of an anchor-distance cutoff, and
an arbitrary scalar subsolution has no growth-free complete-noncompact maximum
principle.  The declaration remains temporarily because `MovingShiOpen` still
calls it, but its docstring now marks it as a legacy unsupported frontier.

Added the canonical consumer predicate `TowerNormGradOn`.  It retains the
geometric estimate

`|∇w_k|² ≤ 4 w_k w_(k+1)`

needed to absorb cutoff-gradient terms against the negative next-level tower
term.  The actual curvature-tower producer is `towerNorm_grad_le` in
`IteratedRmTowerHeatEq.lean`.  Focused verification passed; the only warning is
the pre-existing legacy `sorry`.

## Exact frontier

The replacement chain still needs:

1. generated quantitative parabolic cutoff data for a complete
   bounded-curvature Ricci flow;
2. a localized Bernstein induction that retains the negative `w_(i+1)` terms;
3. migration of `MovingShiOpen.complete_of_heat` away from the current
   truncated tower, whose zeroed `m+1` level cannot satisfy the Kato estimate
   needed at the top level.

This is a substantive analytic/localization frontier, not a coercion issue and
not an HCG input gap.

## Accounting

- corrected complete-noncompact estimate: theorem-level 0%;
- `TowerNormGradOn` and the curvature Kato producer: complete;
- dedicated complete-Bernstein machinery: roughly 30--35%;
- end-to-end complete arbitrary-dimensional Shi producer: theorem-level 0%;
- unconditional `compactnessSol`: theorem-level 0%.
