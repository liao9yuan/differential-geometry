import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensorInnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensorInnerLowerBound
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Uniform operator-norm bounds on the chart `(r, s)`-tensor twist over a compact base set

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a fixed base
point `α : M`, this file proves uniform operator-norm bounds on the chart
`(r, s)`-tensor twist `chartRSTwist α b r s` and its inverse
`chartRSTwistInv α b r s`, viewed as continuous linear maps on
`TensorRSModel r s ℝ E`, for `b` ranging over an arbitrary compact subset
`K ⊆ (chartAt H α).source`, under the locality hypothesis
`HasLocallyConstantChartAt H M` on the chart-selection function.

## Strategy

The chart `(r, s)`-tensor twist `chartRSTwist α b r s T` is defined as the
composition `(post-compose with `chartJ α b` on `s` output slots) ∘ T ∘
(pre-compose with `chartJinv α b` on `r` input slots)`. Mathlib's
`norm_compContinuousLinearMap_le` gives, for each `α' : Tensor0SModel r ℝ E`:

* `‖α'.compCLM (chartJinv α b)‖ ≤ ‖α'‖ * ‖chartJinv α b‖^r`
* `‖T (α'.compCLM (chartJinv α b))‖ ≤ ‖T‖ * ‖α'.compCLM (chartJinv α b)‖`
* `‖(T (α'.compCLM (chartJinv α b))).compCLM (chartJ α b)‖
    ≤ ‖T (α'.compCLM (chartJinv α b))‖ * ‖chartJ α b‖^s`

Chaining these,
`‖chartRSTwist α b r s T α'‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖ * ‖α'‖`.
Hence `‖chartRSTwist α b r s T‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`.

Combining this with the previously-shipped uniform bounds
`chartJ_opNorm_isBounded_on_compact` and
`chartJinv_opNorm_isBounded_on_compact` yields the uniform per-tensor
pointwise bound `‖chartRSTwist α b r s T‖ ≤ C * ‖T‖` over any compact subset
of the chart source.

## Main results

* `chartRSTwist_opNorm_le` — pointwise op-norm bound on `chartRSTwist α b r s T`
  in terms of `‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`.
* `chartRSTwistInv_opNorm_le` — analogous bound for the inverse twist.
* `chartRSTwist_pointwise_opNorm_isBounded_on_compact` — uniform pointwise
  bound on `chartRSTwist α b r s T` over any compact `K ⊆ (chartAt H α).source`.
* `chartRSTwistInv_pointwise_opNorm_isBounded_on_compact` — analogous bound for
  the inverse twist.

Both compact-subset headlines carry the locality hypothesis
`HasLocallyConstantChartAt H M` on the chart selection of `M` and require no
Riemannian-metric structure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap ContinuousMultilinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-! ## Step 1: pointwise operator-norm bounds on the twist of a single tensor -/

/-- Pointwise operator-norm bound on `chartRSTwist α b r s T`, as a continuous
linear map `Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E`:
`‖chartRSTwist α b r s T‖ ≤ ‖chartJ α b‖^s * ‖chartJinv α b‖^r * ‖T‖`. -/
lemma chartRSTwist_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwist (I := I) (M := M) α b r s T‖ ≤
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
        ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  -- We prove: for every input `α' : Tensor0SModel r ℝ E`,
  -- ‖(chartRSTwist α b r s T) α'‖ ≤ (‖chartJ‖^s * ‖chartJinv‖^r * ‖T‖) * ‖α'‖.
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s *
        ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  -- Compute (chartRSTwist α b r s T) α' via `chartRSTwist_apply`.
  rw [chartRSTwist_apply]
  -- Step A: ‖α'.compCLM chartJinv‖ ≤ ‖α'‖ * ‖chartJinv‖^r.
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartJinv (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  -- Step B: ‖T (α'.compCLM chartJinv)‖ ≤ ‖T‖ * ‖α'.compCLM chartJinv‖.
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartJinv (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  -- Step C: ‖(T u).compCLM chartJ‖ ≤ ‖T u‖ * ‖chartJ‖^s.
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartJ (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartJ (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  -- Combine.
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖chartJ (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartJ (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartJ (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)‖ ≤
        ‖chartJ (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  -- Reshuffle.
  have h_final :
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ r)) =
        ‖chartJ (I := I) (M := M) α b‖ ^ s *
          ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined

/-- Pointwise operator-norm bound on `chartRSTwistInv α b r s T`:
`‖chartRSTwistInv α b r s T‖ ≤ ‖chartJinv α b‖^s * ‖chartJ α b‖^r * ‖T‖`. -/
lemma chartRSTwistInv_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwistInv (I := I) (M := M) α b r s T‖ ≤
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
        ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s *
        ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  rw [chartRSTwistInv_apply]
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartJ (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartJinv (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖chartJinv (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartJinv (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartJinv (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)‖ ≤
        ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  have h_final :
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartJ (I := I) (M := M) α b‖ ^ r)) =
        ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined

/-! ## Step 2: uniform pointwise bounds on a compact subset of the chart source -/

/-- Uniform pointwise operator-norm bound on the chart-`(α, b)`-twist of any
`(r, s)`-tensor `T`, over any compact `K ⊆ (chartAt H α).source`. There is a
single constant `C > 0` such that
`‖chartRSTwist α b r s T‖ ≤ C * ‖T‖` for every `T` and every `b ∈ K`. -/
theorem chartRSTwist_pointwise_opNorm_isBounded_on_compact
    (h_atlas : HasLocallyConstantChartAt H M)
    (α : M) {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source)
    (r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ T : TensorRSModel r s ℝ E,
      ‖chartRSTwist (I := I) (M := M) α b r s T‖ ≤ C * ‖T‖ := by
  obtain ⟨C₁, hC₁_pos, hC₁_le⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK hKsub
  obtain ⟨C₂, hC₂_pos, hC₂_le⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK hKsub
  refine ⟨C₁ ^ s * C₂ ^ r, by positivity, ?_⟩
  intro b hb T
  have h_bound := chartRSTwist_opNorm_le (I := I) (M := M) α b r s T
  have h_J : ‖chartJ (I := I) (M := M) α b‖ ≤ C₁ := hC₁_le b hb
  have h_Jinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C₂ := hC₂_le b hb
  have h_J_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ := norm_nonneg _
  have h_Jinv_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ := norm_nonneg _
  have h_J_pow : ‖chartJ (I := I) (M := M) α b‖ ^ s ≤ C₁ ^ s :=
    pow_le_pow_left₀ h_J_nn h_J s
  have h_Jinv_pow : ‖chartJinv (I := I) (M := M) α b‖ ^ r ≤ C₂ ^ r :=
    pow_le_pow_left₀ h_Jinv_nn h_Jinv r
  have h_Jpow_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s := by positivity
  have h_C2pow_nn : 0 ≤ C₂ ^ r := by positivity
  have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
  have h_prod_le :
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
          ‖chartJinv (I := I) (M := M) α b‖ ^ r ≤ C₁ ^ s * C₂ ^ r := by
    calc
      ‖chartJ (I := I) (M := M) α b‖ ^ s *
          ‖chartJinv (I := I) (M := M) α b‖ ^ r
          ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s * C₂ ^ r :=
            mul_le_mul_of_nonneg_left h_Jinv_pow h_Jpow_nn
      _ ≤ C₁ ^ s * C₂ ^ r :=
            mul_le_mul_of_nonneg_right h_J_pow h_C2pow_nn
  calc
    ‖chartRSTwist (I := I) (M := M) α b r s T‖
        ≤ ‖chartJ (I := I) (M := M) α b‖ ^ s *
            ‖chartJinv (I := I) (M := M) α b‖ ^ r * ‖T‖ := h_bound
    _ ≤ C₁ ^ s * C₂ ^ r * ‖T‖ :=
          mul_le_mul_of_nonneg_right h_prod_le h_T_nn

/-- Uniform pointwise operator-norm bound on the inverse chart-`(α, b)`-twist
of any `(r, s)`-tensor `T`, over any compact `K ⊆ (chartAt H α).source`. -/
theorem chartRSTwistInv_pointwise_opNorm_isBounded_on_compact
    (h_atlas : HasLocallyConstantChartAt H M)
    (α : M) {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source)
    (r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ T : TensorRSModel r s ℝ E,
      ‖chartRSTwistInv (I := I) (M := M) α b r s T‖ ≤ C * ‖T‖ := by
  obtain ⟨C₁, hC₁_pos, hC₁_le⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK hKsub
  obtain ⟨C₂, hC₂_pos, hC₂_le⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK hKsub
  refine ⟨C₂ ^ s * C₁ ^ r, by positivity, ?_⟩
  intro b hb T
  have h_bound := chartRSTwistInv_opNorm_le (I := I) (M := M) α b r s T
  have h_J : ‖chartJ (I := I) (M := M) α b‖ ≤ C₁ := hC₁_le b hb
  have h_Jinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C₂ := hC₂_le b hb
  have h_J_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ := norm_nonneg _
  have h_Jinv_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ := norm_nonneg _
  have h_J_pow : ‖chartJ (I := I) (M := M) α b‖ ^ r ≤ C₁ ^ r :=
    pow_le_pow_left₀ h_J_nn h_J r
  have h_Jinv_pow : ‖chartJinv (I := I) (M := M) α b‖ ^ s ≤ C₂ ^ s :=
    pow_le_pow_left₀ h_Jinv_nn h_Jinv s
  have h_Jinvpow_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s := by positivity
  have h_C1pow_nn : 0 ≤ C₁ ^ r := by positivity
  have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
  have h_prod_le :
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          ‖chartJ (I := I) (M := M) α b‖ ^ r ≤ C₂ ^ s * C₁ ^ r := by
    calc
      ‖chartJinv (I := I) (M := M) α b‖ ^ s *
          ‖chartJ (I := I) (M := M) α b‖ ^ r
          ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s * C₁ ^ r :=
            mul_le_mul_of_nonneg_left h_J_pow h_Jinvpow_nn
      _ ≤ C₂ ^ s * C₁ ^ r :=
            mul_le_mul_of_nonneg_right h_Jinv_pow h_C1pow_nn
  calc
    ‖chartRSTwistInv (I := I) (M := M) α b r s T‖
        ≤ ‖chartJinv (I := I) (M := M) α b‖ ^ s *
            ‖chartJ (I := I) (M := M) α b‖ ^ r * ‖T‖ := h_bound
    _ ≤ C₂ ^ s * C₁ ^ r * ‖T‖ :=
          mul_le_mul_of_nonneg_right h_prod_le h_T_nn

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
