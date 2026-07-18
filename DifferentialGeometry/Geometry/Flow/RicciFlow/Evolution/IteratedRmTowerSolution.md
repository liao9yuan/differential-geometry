# IteratedRmTowerSolution

## Purpose

This file owns the arbitrary-dimensional, solution-facing boundary between a
Ricci-flow solution and the generic variable-rank `IteratedRmTowerOn` consumer.
It does not import or generalize the dimension-three `StarSum` route.

## Verified interface

The file passes its focused check.

- `exists_rmTowerSol` has the correct no-extra-input statement: it asks an
  actual `IsSolutionOn` to produce component fields indexed by
  `Fin (Module.finrank Real E)` and an `IteratedRmTowerOn` whose scalar fields
  are exactly `nablaKRm04NormSqIntrinsic` and `nablaKNormLap`.
- `towerHeatSol_any` is assembled from that producer and
  `iteratedRmTower_heatBound`.  The generic cardinality reduces to
  `Module.finrank Real E`, giving the coefficient
  `2 * (Module.finrank Real E : Real) ^ (6 + k)` with no `CompactSpace` or
  dimension-three hypothesis.

## Exact frontier

`exists_rmTowerSol` deliberately contains the file's single `sorry`.  The
missing mathematics is not the intrinsic norm heat equation, the Laplacian
term, or the generic contraction estimate; all three are already checked.
The missing result is the all-order solution identity

```text
(partial_t - roughLap) nabla^k Rm
  = sum_{j=0}^k nabla^j Rm * nabla^(k-j) Rm
```

in a form producing one genuine component family `star k j` that
simultaneously satisfies:

1. its sum is the concrete residual/reaction appearing in
   `nablaKRm04NormHeatEquationOn_intrinsic`; and
2. every component obeys the existing `IteratedRmTowerOn.starBound` estimate.

The smallest next theorem is a tensor-first `exists_commStar` lemma for one
solution, level `k`, regular time, and point.  It should output the componentwise
sum identity and the per-`j` bound above.  Its proof must use the one-step
commutation of `partial_t - roughLap` with `nabla`, the solution connection
variation, and the existing all-rank Ricci identity; it must not define a
residual-only `j = 0` filler.

This is a genuine new geometric producer, not a routine elaboration/API gap.

## Honest accounting

- `towerHeatSol_any`: statement and consumer assembly are checked, but the
  theorem is not trusted-complete while `exists_rmTowerSol` depends on
  `sorryAx`; trusted theorem completion is **0%**.
- `exists_rmTowerSol`: statement **100%**, proof **0%**.
- dedicated arbitrary-dimensional tower machinery: about **70%**; the existing
  intrinsic all-order heat equation and generic tower consumer are substantial,
  while the commuted-curvature star decomposition is the central missing
  producer.
- complete-noncompact Bernstein theorem and its Shi wrapper remain separate
  later frontiers and are not counted as completed here.
- unconditional HCG `compactnessSol`: theorem **0%**; whole-HCG support
  machinery remains about **60%**.
