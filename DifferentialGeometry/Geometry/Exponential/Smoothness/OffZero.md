# OffZero.lean — forward `expMap` `C∞` on a uniform ball (Frontier-1, 2026-06-13)

## Status: forward `expMap ContMDiffAt ∞` on a UNIFORM ball — PROVED, axiom-clean

**Verification PASSED**: focused check + targeted build green; consumer `JacobiVariation`
rebuilt green (no API regression); `#print axioms expMap_contMDiffAt_infty_of_norm_lt` =
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## What landed (the frontier-1 ODE gate)
- `Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_inf` (`SmoothFlow.lean`) —
  the chart-phase flow `Φ` of the (globally `C∞`, bump-cutoff) `chartPhaseVFTime` is
  `ContDiffOn ℝ ∞` on a **single fixed box**, with **no order-dependent shrinking**.
  Mirror of `..._combined_nat`, replacing the per-`n` `exists_contDiffOn_flow_Cnat`
  (shrinking neighbourhood) with `exists_flow_nesting_data` + the fixed-box Hartman
  theorem `IsLocalFlow.contDiffOn_top` (the VF is `C∞` on `univ` via
  `chartPhaseVFTime_uncurry_contDiff`).
- `exists_unified_chartFlow_data_inf` — `C∞` unified chart packaging on the fixed box.
  The old `exists_unified_chartFlow_data_nat` is now a thin `ContDiffOn.of_le` wrapper of
  it (DRY; consumers unchanged).
- `expMap_contMDiffAtN_of_chartData` — the shared, level-parameterised off-zero core
  (radial rescaling + candidate identity), extracted from the old `_nat` proof so both
  `_nat` and `_infty` consume it.
- **`expMap_contMDiffAt_infty_of_norm_lt`** — the headline: a **single** radius `δ > 0`
  with `expMap g p` `ContMDiffAt 𝓘(ℝ,E) I ∞` at every `‖w‖ < δ`.  Built by
  `contMDiffAt_infty` (`∞ ↔ ∀ n`), closing each order `n` at the fixed radius via the
  shared core + `hΦ_cd_inf.of_le`.  The `↑n` vs `((n:ℕ∞):WithTop ℕ∞)` level was defeq.

The planner's corrected verdict (the fixed-domain ODE smooth-dependence theorem already
exists as `IsLocalFlow.contDiffOn_top` / `..._local`) was the key unlock; my earlier
"new ODE theorem needed" audit was wrong.

## Remaining downstream (assessed; NOT this brick)
The forward theorem is the *enabling input* for the Step B `hsmooth` hypotheses, but each
discharge is a separate downstream brick:

1. **B-metric `normalCoordMetric_contDiffOn` (forward).** `normalCoordMetric` is the
   model-coordinate pullback `z ↦ g_{exp z}(d exp_z·, d exp_z·)` (via `mfderiv expMapDiffeo`).
   Its `ContDiffOn ℝ ⊤` follows from this forward `expMap C∞` **plus** a bundle/tensor
   brick: smoothness of the `mfderiv`-pullback section in model coordinates (analogous to
   `Geometry/Metric/Pullback.lean : inner_comp_smooth_along_diffeo`, but as a model-coord
   function `E → (E →L E →L ℝ)`). A real geometry brick, ~100 lines — not a corollary.
2. **B-trans `normalTransition_contDiffOn` (inverse).** Needs the inverse chart
   `normalChartAt = (expMapDiffeo).symm` at `C∞` — the realized `expMapDiffeo` is
   `PartialDiffeomorph … 1`. This requires the **`C∞` inverse function theorem** applied
   to the now-`C∞` forward exp at the (invertible) `d exp_0`. **Separate
   inverse-function-theorem frontier** — the planner's explicit stop point.

Both are now gated on *geometry/IFT wiring*, no longer on the ODE smoothness frontier.
