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

## B-metric `normalCoordMetric_contDiffOn` — feasibility audit (2026-06-13)

**Verdict: FEASIBLE (every lemma exists), but a substantial bundle-assembly (~150–250 lines),
not a corollary.** No new foundational lemma is missing (the planner's hard-stop #1 is NOT
triggered: `ContMDiffOn.contMDiffOn_tangentMapWithin` supplies `mfderiv`-smoothness from
`ContMDiffOn ∞ expMap`).

`normalCoordMetric Y x z = (precomp D).comp ((g.inner (exp z)).comp D)`,
`D = mfderiv (expMapDiffeo x) z : E →L T_{exp z}M`.  The codomain `T_{exp z}M` **varies
with `z`** (a Hom-bundle), so ordinary model `ContDiff` composition does **not** apply
directly — the bundle/`inCoordinates` machinery is required.

### Confirmed reusable tools
- `ContMDiffOn.contMDiffOn_tangentMapWithin` (`Mathlib …/ContMDiffMFDeriv.lean:275`):
  `ContMDiffOn n f s → m+1 ≤ n → UniqueMDiffOn s → ContMDiffOn m (tangentMapWithin I I' f s)`.
- `ContMDiffOn.clm_bundle_apply₂` (the bilinear bundle-apply; used by
  `pullbackGram_jointContMDiffOn_interior` in `ConjugatingFlowProperties.lean:3685`, the
  closest existing pattern — but it is **diffeo-family**-specific, not reusable verbatim).
- `contMDiffOn_iff_contDiffOn {f : E → E'}` (`Mathlib …/ContMDiff/NormedSpace.lean:57`):
  model↔model `ContMDiffOn = ContDiffOn`, for the final conversion.
- `SmoothRiemannianMetric.contMDiff` (the metric inner is a smooth Hom-bundle section).

### Precise 5-step assembly (the focused next commission)
1. **Comparison (C¹→C∞):** `mfderiv (expMapDiffeo x) z = mfderivWithin (expMap x) U z` on
   the open ball `U ⊆ source` — via `expMapDiffeo_apply_eq` (agree on source) +
   `Filter.EventuallyEq.mfderiv_eq` + `mfderivWithin = mfderiv` on open `U`.  (`expMapDiffeo`
   is only `PartialDiffeomorph … 1`; this is the planner's step-3 comparison lemma.)
2. **Forward smoothness on the ball:** `expMap x` `ContMDiffOn ⊤ U` from
   `expMap_contMDiffAt_infty_of_norm_lt` (pointwise `ContMDiffAt ∞` → `ContMDiffWithinAt`).
3. **Pushforward sections:** `z ↦ ⟨exp z, mfderivWithin (exp x) U z v⟩` `ContMDiffOn` via
   `tangentMapWithin (exp x) U` (= `contMDiffOn_tangentMapWithin`) composed with `z ↦ (z,v)`.
4. **CLM-valued (not just scalar):** `exists_metricLimit_normalCoord` needs the **`E →L E →L ℝ`-valued**
   `normalCoordMetric` `ContDiffOn ⊤`, not just scalar entries.  Either assemble the
   Hom-bundle CLM `(precomp D).comp ((g.inner)∘D)` smoothly in `inCoordinates`, or use a
   finite-dim componentwise→CLM bridge (`ContDiffOn` of `z ↦ B z` from `z ↦ B z eᵢ eⱼ`).
   This is the most intricate step.
5. **Convert** the resulting `ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ, E→L E→L ℝ) ⊤` to `ContDiffOn ℝ ⊤`
   via `contMDiffOn_iff_contDiffOn`, and `domain` align with the wrapper's `U`.

The forward theorem (the hard, foundational piece) is done; this remaining brick is pure
geometry/bundle wiring with all tools in hand.  Recommended as the next focused session.
