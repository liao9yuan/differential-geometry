import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Chain-rule bridge: chart-pushed raw scalar versus chart-pulled composition

For a scalar function `u : M → ℝ` on a smooth Riemannian manifold and a chart
`α`, this file relates two views of the iterated Fréchet derivative of `u` at
a Euclidean chart-target point `y ∈ chartTargetEuclid α`:

* **View A** — the iterated Fréchet derivative of the raw chart-pushed function
  `chartPushedRaw I α u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ` at
  `y`, with derivatives valued in continuous multilinear maps on the standard
  Euclidean space.

* **View B** — the iterated Fréchet derivative of the chart-pulled
  composition `u ∘ (extChartAt I α).symm : E → ℝ` at the model-space point
  `(toEuclidean (E := E)).symm y`, with derivatives valued in continuous
  multilinear maps on the model fibre `E`.

Both views are pointwise equal on the chart target after composition with the
continuous-linear-equivalence `(toEuclidean (E := E)).symm : EuclN → E`; their
iterated derivatives differ by the operator-norm chain factor
`‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖^j` (each of the `j`
derivative slots contributes one factor of the operator norm), which when
squared gives `‖…‖^(2j)`.

We package the comparison as the squared-norm bounds at orders `j = 0, 1, 2`:

* `chartPushedRaw_sq_eq_compositionSq` — the order-`0` identity (no
  derivative, just function value composition).
* `fderiv_chartPushedRaw_sq_le_compFderivSq` — the order-`1` squared
  Fréchet-derivative bound.
* `iteratedFDeriv_two_chartPushedRaw_sq_le_compIterSq` — the order-`2`
  squared iterated-Fréchet-derivative bound.

All bounds avoid any chart-locality assumptions: they apply uniformly to any
`α`, any `u`, and any `y` in the chart-α Euclidean target.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Order-0 identity

For `y ∈ chartTargetEuclid α`, the raw chart-pushed value of `u` at `y` equals
the composition `u ∘ (extChartAt I α).symm` evaluated at the model-space point
`(toEuclidean (E := E)).symm y`. Squaring both sides records the
`order-0` form of the chain-rule bridge. -/

/-- **Order-0 bridge.** On the chart-α Euclidean target, the squared raw
chart-pushed value of `u` equals the squared composition value of `u ∘ symm`
at the corresponding model-space point. -/
theorem chartPushedRaw_sq_eq_compositionSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u y) ^ 2 =
      (u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 := by
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
    (I := I) (M := M) α u hy]

/-! ## Order-1 squared Fréchet-derivative bound

The strategy is straightforward: on the open chart target, the raw chart-pushed
function agrees with `(u ∘ (extChartAt I α).symm) ∘ (toEuclidean (E := E)).symm`
in a neighborhood of any chart-target point, so their Fréchet derivatives agree
at that point. The `fderiv` of the right-hand composition is then computed via
the unconditional chain rule for continuous linear equivalences. Taking
operator norms and squaring gives the bound. -/

/-- **Order-1 bridge.** On the chart-α Euclidean target, the squared
Fréchet-derivative norm of the raw chart-pushed function at `y` is bounded by
the operator-norm-squared chain factor times the squared Fréchet-derivative
norm of the composition `u ∘ (extChartAt I α).symm` at the corresponding
model-space point. -/
theorem fderiv_chartPushedRaw_sq_le_compFderivSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    (_hu : ContDiffOn ℝ 1 (u ∘ (extChartAt I α).symm) (extChartAt I α).target)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ‖fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y‖
      ^ 2 ≤
      ‖((toEuclidean (E := E)).symm : EuclN ≃L[ℝ] E).toContinuousLinearMap‖
          ^ 2 *
      ‖fderiv ℝ (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
  classical
  -- Step 1: identify the chart-pushed function with the composition in a
  -- neighborhood of `y`, using openness of the chart target.
  set L : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with hL_def
  set f : E → ℝ := u ∘ (extChartAt I α).symm with hf_def
  -- The chart target is open in `EuclN` under the boundaryless assumption.
  have h_open : IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_nhds_y : DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α ∈ nhds y := h_open.mem_nhds hy
  -- On the chart target, `chartPushedRaw I α u = f ∘ L`.
  have h_eventuallyEq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u =ᶠ[nhds y]
        (f ∘ (L : EuclN → E)) := by
    filter_upwards [h_nhds_y] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α u hz]
    rfl
  -- Step 2: the Fréchet derivative is unchanged under `EventuallyEq`.
  have h_fderiv_eq :
      fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y =
        fderiv ℝ (f ∘ (L : EuclN → E)) y :=
    Filter.EventuallyEq.fderiv_eq h_eventuallyEq
  rw [h_fderiv_eq]
  -- Step 3: chain rule for the continuous linear equivalence `L = toEuclidean.symm`.
  rw [L.comp_right_fderiv (f := f) (x := y)]
  -- Now bound the operator norm of the composition.
  -- `‖(fderiv ℝ f (L y)).comp L‖ ≤ ‖fderiv ℝ f (L y)‖ * ‖L‖`.
  have h_norm_comp_le :
      ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ ≤
        ‖fderiv ℝ f (L y)‖ * ‖(L : EuclN →L[ℝ] E)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  -- Square both sides, using non-negativity of the operator norm.
  have h_lhs_nn : 0 ≤ ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ :=
    norm_nonneg _
  have h_sq_le :
      ‖(fderiv ℝ f (L y)).comp (L : EuclN →L[ℝ] E)‖ ^ 2 ≤
        (‖fderiv ℝ f (L y)‖ * ‖(L : EuclN →L[ℝ] E)‖) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nn h_norm_comp_le 2
  refine h_sq_le.trans (le_of_eq ?_)
  -- `((toEuclidean.symm : EuclN ≃L[ℝ] E) : EuclN →L[ℝ] E) =
  --  ((toEuclidean.symm : EuclN ≃L[ℝ] E)).toContinuousLinearMap`.
  have h_norm_eq :
      ‖(L : EuclN →L[ℝ] E)‖ =
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ := rfl
  rw [h_norm_eq]
  -- Identify `L y = (toEuclidean (E := E)).symm y` and `f = u ∘ (extChartAt I α).symm`.
  change (‖fderiv ℝ f (L y)‖ *
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖) ^ 2 =
      ‖((toEuclidean (E := E)).symm :
          EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 2 *
      ‖fderiv ℝ (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2
  rw [hf_def, hL_def]
  ring

/-! ## Order-2 squared iterated-Fréchet-derivative bound

For the second-order bridge, we use:
* the open-set agreement `chartPushedRaw I α u =ᶠ[nhds y] (u ∘ symm) ∘ L`
  (so the global `iteratedFDeriv` of both sides agree at `y`),
* the unconditional chain rule `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`
  (which avoids any `ContDiff` hypothesis), applied with the open set
  `(extChartAt I α).target` (where `(u ∘ symm)` is `ContDiffOn ℝ 2`), and
* the fact that on open sets `iteratedFDerivWithin` coincides with
  `iteratedFDeriv` (`iteratedFDerivWithin_of_isOpen`).

Finally, the norm bound `‖g.compContinuousLinearMap (fun _ => L)‖
≤ ‖g‖ * ∏ ‖L‖ = ‖g‖ * ‖L‖^2` and squaring yield the result. -/

/-- **Order-2 bridge.** On the chart-α Euclidean target, the squared order-2
iterated-Fréchet-derivative norm of the raw chart-pushed function at `y` is
bounded by the operator-norm-to-the-fourth chain factor times the squared
order-2 iterated-Fréchet-derivative norm of the composition
`u ∘ (extChartAt I α).symm` at the corresponding model-space point. -/
theorem iteratedFDeriv_two_chartPushedRaw_sq_le_compIterSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (u : M → ℝ)
    (_hu : ContDiffOn ℝ 2 (u ∘ (extChartAt I α).symm) (extChartAt I α).target)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y‖
      ^ 2 ≤
      ‖((toEuclidean (E := E)).symm : EuclN ≃L[ℝ] E).toContinuousLinearMap‖
          ^ 4 *
      ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
  classical
  -- Set up abbreviations.
  set L : EuclN ≃L[ℝ] E := (toEuclidean (E := E)).symm with hL_def
  set f : E → ℝ := u ∘ (extChartAt I α).symm with hf_def
  set s : Set E := (extChartAt I α).target with hs_def
  -- Step 1: identify chartPushedRaw with f ∘ L on a neighborhood of y.
  have h_open_target : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_nhds_y : DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α ∈ nhds y := h_open_target.mem_nhds hy
  have h_eventuallyEq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u =ᶠ[nhds y]
        (f ∘ (L : EuclN → E)) := by
    filter_upwards [h_nhds_y] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α u hz]
    rfl
  -- Step 2: iteratedFDeriv preserved under EventuallyEq.
  have h_iter_eq :
      iteratedFDeriv ℝ 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) y =
        iteratedFDeriv ℝ 2 (f ∘ (L : EuclN → E)) y :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ h_eventuallyEq 2).eq_of_nhds
  rw [h_iter_eq]
  -- Step 3: pass from iteratedFDeriv to iteratedFDerivWithin on open sets.
  -- `L ⁻¹' s = chartTargetEuclid α`, which is open in EuclN.
  have h_preimage :
      (L : EuclN → E) ⁻¹' s = DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
    rw [hs_def]
    -- L = toEuclidean.symm; (toEuclidean.symm) ⁻¹' (extChartAt α).target =
    -- chartTargetEuclid α.
    rw [← DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M) α]
  -- The chart target (in E) is open.
  have h_open_s : IsOpen s := by
    rw [hs_def]; exact isOpen_extChartAt_target (I := I) α
  -- The preimage (= chartTargetEuclid α) is open.
  have h_open_preimage : IsOpen ((L : EuclN → E) ⁻¹' s) := by
    rw [h_preimage]; exact h_open_target
  -- y ∈ L ⁻¹' s, since y ∈ chartTargetEuclid α.
  have h_y_in_preimage : y ∈ (L : EuclN → E) ⁻¹' s := by
    rw [h_preimage]; exact hy
  -- L y ∈ s, since (toEuclidean.symm) y ∈ (extChartAt α).target.
  have h_Ly_in_s : (L : EuclN → E) y ∈ s := h_y_in_preimage
  -- Convert iteratedFDeriv on EuclN to iteratedFDerivWithin (L ⁻¹' s).
  have h_iter_within_eucl :
      iteratedFDeriv ℝ 2 (f ∘ (L : EuclN → E)) y =
        iteratedFDerivWithin ℝ 2 (f ∘ (L : EuclN → E))
          ((L : EuclN → E) ⁻¹' s) y := by
    have := iteratedFDerivWithin_of_isOpen
      (n := 2) (f := f ∘ (L : EuclN → E)) (𝕜 := ℝ)
      h_open_preimage h_y_in_preimage
    exact this.symm
  rw [h_iter_within_eucl]
  -- Step 4: unconditional chain rule for ContinuousLinearEquiv.
  have h_uniqueDiffOn_s : UniqueDiffOn ℝ s := h_open_s.uniqueDiffOn
  have h_chain :
      iteratedFDerivWithin ℝ 2 (f ∘ (L : EuclN → E))
          ((L : EuclN → E) ⁻¹' s) y =
        (iteratedFDerivWithin ℝ 2 f s ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E)) :=
    L.iteratedFDerivWithin_comp_right f h_uniqueDiffOn_s h_Ly_in_s 2
  rw [h_chain]
  -- Step 5: convert iteratedFDerivWithin on s (open in E) back to iteratedFDeriv.
  have h_iter_within_E :
      iteratedFDerivWithin ℝ 2 f s ((L : EuclN → E) y) =
        iteratedFDeriv ℝ 2 f ((L : EuclN → E) y) :=
    iteratedFDerivWithin_of_isOpen (n := 2) (f := f) (𝕜 := ℝ)
      h_open_s h_Ly_in_s
  rw [h_iter_within_E]
  -- Step 6: bound the operator norm of the composed multilinear map.
  have h_norm_bound :
      ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ ≤
        ‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
          ∏ _i : Fin 2, ‖(L : EuclN →L[ℝ] E)‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  have h_prod_eq : ∏ _i : Fin 2, ‖(L : EuclN →L[ℝ] E)‖ =
      ‖(L : EuclN →L[ℝ] E)‖ ^ 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_eq] at h_norm_bound
  -- Step 7: square both sides.
  have h_lhs_nn :
      0 ≤ ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ := norm_nonneg _
  have h_sq_le :
      ‖(iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)).compContinuousLinearMap
          (fun _ : Fin 2 => (L : EuclN →L[ℝ] E))‖ ^ 2 ≤
        (‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
          ‖(L : EuclN →L[ℝ] E)‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nn h_norm_bound 2
  refine h_sq_le.trans (le_of_eq ?_)
  -- Identify the operator norm of L with the CLM-norm form in the goal.
  have h_norm_eq :
      ‖(L : EuclN →L[ℝ] E)‖ =
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ := rfl
  rw [h_norm_eq]
  -- Identify L y with toEuclidean.symm y and f with u ∘ symm.
  change (‖iteratedFDeriv ℝ 2 f ((L : EuclN → E) y)‖ *
        ‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 2) ^ 2 =
      ‖((toEuclidean (E := E)).symm :
          EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 4 *
      ‖iteratedFDeriv ℝ 2 (u ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2
  rw [hf_def, hL_def]
  ring

end Connection
end Integral
end DifferentialGeometry

end
