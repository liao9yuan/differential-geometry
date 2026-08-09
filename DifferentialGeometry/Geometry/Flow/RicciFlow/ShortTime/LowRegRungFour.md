# `LowRegRungFour.lean` — notes

Status (2026-08-05): **rung four is stated, proved, and explicitly packaged.**
Focused verification passed warning-free, the named export refresh passed, and
the widened ShortTime axiom census reports only `propext`, `Classical.choice`,
and `Quot.sound` for every new declaration, with no `sorryAx`.

## What landed

* `armOrder3` is the tower-direct `q = 3` regrouping.  After writing
  `Jm = √(∑_{j<m} ‖∇^j T‖²)`, only three terms reach `J6`:
  `Cq·Cδ·J6`, the `a₂` endpoint slot `Cq·K3·J3·J6`, and the `a₁` slot
  `Cq·K1(2)·J3·J6`.  Every other term is bounded by
  `(1+Cδ)(1+Y)^3(1+Z)^2(1+W)`, hence is linear in the `J5` window once the
  lower windows are capped.
* `galArmMass4Ord` transports that split to spectral mass.  Its four gate
  constants are chosen before `R`, `δ`, the realization, and the prior rung
  cap.  After a common `√E3 ≤ R3` input it returns
  `arm_H3 ≤ α·√E5 + Kmid·√E4 + Kadd`, with `Kmid,Kadd` allowed to depend on
  the prior cap but `α` not.
* `lowregRung4Ord` combines that ladder with `two_sum_ladder_add_le` and the
  single-scale Galerkin energy engine.  It consumes a pointwise common rung-three
  cap and proves an `N,t`-uniform `E4` bound on the same horizon.  No additional
  primitive or dissipation-export hypothesis is needed for this fixed rung.
* `IsRung4Ord` and `lowregRung4Pack` retain the exact ordered gate witnesses and
  their continuation.  Downstream calibration must use the stored continuation;
  re-running the existential theorem would lose witness coherence.

## Reuse and route decisions

The module imports only `LowRegRungThree`.  It reuses the public `jetSqrtLe`,
`jetWinMono`, and `armLadder3` boundary; the checked `q ≤ 2` algebra is not
duplicated.  `armOrder3` is public so rung five can reuse the checked q=3 slot
without copying its algebra.  The direct sequential rung route is shorter than the generic
`nDiffHmQ` route here because the latter needs an `H5` radius that is not
available until the fixed bottom rungs close.

The generic dissipation exporter remains useful infrastructure but is not a
logical prerequisite for this fixed rung.  Rung five is the next concrete
producer.  Only after its ordered package exists is it honest to build a common
rungs-3-to-5/high-rung gate envelope and recalibrate the adapted solve once.

## Project position

`lowreg_loMass` is still theorem-level **0%**: its `3 < σ` branch is not yet
proved.  Dedicated all-order low-mass machinery is now approximately **89%**;
the per-metric explicit package lane through rung four is **100%**, rung five is
**0%**, `(N)` `ricci_flow_unif_existence` is **0%**, and the whole HCG project
remains approximately **3%**.
