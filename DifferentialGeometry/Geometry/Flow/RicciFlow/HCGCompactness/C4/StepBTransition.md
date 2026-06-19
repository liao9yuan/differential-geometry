# StepBTransition.lean — B-trans transition limits + cocycle (`lbl394` transition, 2026-06-13)

## Status: generic theorem COMPLETE; HCG `normalTransition` wrapper blocked on `C^∞` smoothness

**Verification PASSED**: focused check + targeted build green (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`) for `exists_transitionLimit_on`.

## Delivered
- `exists_transitionLimit_on` — transition-map limits + limit cocycle, generic
  model-coordinate form. Transition maps `J k : U → E`, `J̄ k : V → E` on nested **open
  Euclidean domains of the same model `E`** (`E^α, Ē^β ⊆ E`), each `C^∞` on its domain,
  satisfying `IsometryDerivBoundsOn` and mutually inverse, get a subsequence with limits
  `Jinf`, `J̄inf` converging in `C^∞` on compacts plus the **limit cocycle**
  `J̄inf (Jinf x) = x` / `Jinf (J̄inf y) = y` — stated **conditionally on domain
  membership** (`Jinf x ∈ V`, `J̄inf y ∈ U`), as in `isometry_seq_diffeo_on`.

This is the `F = E` instance of `isometry_seq_diffeo_on` (B-loc) in transition language —
the book's `lbl394` transition endpoint. No new proof content beyond B-loc; it packages
the same-model-space case under the `J`/`J̄` cocycle names that B-Falpha/B-glue cite.

## Orientation note
Lean types fix the composition order: the cocycle output of `isometry_seq_diffeo_on` is
`J̄inf ∘ Jinf = id` on `U` (conditional `Jinf x ∈ V`) and `Jinf ∘ J̄inf = id` on `V`
(conditional `J̄inf y ∈ U`). The book's `J̄_∞^{βα} ∘ J_∞^{αβ} = id_β` (line 1494) matches
the first with `J := J^{αβ}` (domain `E^α`-side `U`), `J̄ := J̄^{βα}` (domain `V`).

## HCG `normalTransition` wrapper DELIVERED by honest exposure (2026-06-13, frontier-1)

`exists_transitionLimit_normalTransition` (new `section HCGNormalTransition`) wires
`normalTransition` + `ExpInverseDerivBoundInput` + center sequences `x y : ∀ k, (X.obj
k).M` into `exists_transitionLimit_on`. **Verification PASSED** (focused check + targeted
build green; axiom-clean `[propext, Classical.choice, Quot.sound]`). Fixed-pair only, NOT
the finite diagonal over all `α, β`.

Honestly-exposed explicit hypotheses (bare, not renamed):
- `hsmoothJ/hsmoothJbar : ∀ k, ContDiffOn ℝ ⊤ (normalTransition …) U/V` — the genuine
  smoothness; blocked on the **same foundational gap** as B-metric (`expMap` `ContMDiffAt
  ∞` on a uniform ball; the realized `expMapDiffeo` is `C^1`). One upstream fix unblocks
  both wrappers.
- `hovlJ/hovlJbar : ∀ k, NormalOverlapOn (X.obj k) (x k) (y k) U` — new honest
  domain/overlap predicate (the bare condition `z ∈ exp_x.source ∧ exp_x z ∈
  normalChart_y.source` on `U`), bridging `ExpInverseDerivBoundInput`'s overlap bound
  (`input.exp_inv_deriv`, `M = input.derivC r`) to `IsometryDerivBoundsOn U`.
- `hLeft/hRight` — the cocycle, **conditional on `U`/`V`** (the overlap), never global
  (`normalTransition` is junk off the overlap).

### Conditional-cocycle generalization of B-loc (required, this push)
`comp_eq_id_of_cInf_on` and `isometry_seq_diffeo_on` (StepBLocalizedAA) and
`exists_transitionLimit_on` had **global** inverse hypotheses (`∀ k x, …`), which
`normalTransition` cannot satisfy. Generalized them to **domain-conditional** (`∀ k, ∀ x
∈ U, …`) — the honest form matching their already-conditional conclusions. Backward
compatible (the only caller threaded the membership through). All re-verified axiom-clean.
