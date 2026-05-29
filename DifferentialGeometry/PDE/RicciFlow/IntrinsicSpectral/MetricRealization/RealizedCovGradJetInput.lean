import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberToModelOpNormUnconditional
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform

/-!
# The pointwise covariant-gradient jet input for the chart `2`-jet seminorm bound

This file discharges the analytic input `hcovgrad_jet_bound` of
`chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum`: on a compact piece
`K ⊆ interior (extChartAt I α).target`, every chart `∂^j` (`j = 0, 1, 2`) of the chart-frame
component function `reprDiffChartCompOnE g_bg hu₁ hu₂ α l b` of the **fixed** tensor
difference `S = realizableRepr hu₁ − realizableRepr hu₂` is bounded by a single constant
times the iterated covariant-gradient jet sum `iteratedCovGradJetSum g_bg S ((symm) y)`.

## The per-component pointwise bound (leaf-2)

The raw chart-frame scalar component `tensorChartComponentRaw g_bg 0 (2 + i) T α Idx Jdx b`
is, by definition, the `(Idx, Jdx)`-projection of the chart-`α` trivialisation fibre
`tensorTrivProj g_bg 0 (2 + i) T α b` of the underlying tensor section `T.toSection b`.
Hence its absolute value is bounded by `‖projection‖ · ‖tensorTrivProj‖`, with the
projection operator norm bounded uniformly by `chartComponentProjectionUniformBound` and the
trivialisation-fibre norm bounded uniformly on the compact `K` by the **unconditional**
op-norm bound `tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional`, against
the `g_bg`-Riemannian fibre norm `‖T.toSection b‖`.  This produces

  `|tensorChartComponentRaw g_bg 0 (2 + i) T α Idx Jdx b| ≤ C · ‖T.toSection b‖`,

uniformly over the compact base set and over all multi-indices.

## Sign convention

Geometer `Δ_∇ = −∇*∇`; resolvent `(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Leaf-2: the per-component pointwise bound -/

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Pointwise bound on a single raw chart-frame scalar component.**

For a smooth compactly-supported `(0, s)`-tensor `T`, a chart center `α`, and a compact
base set `K ⊆ (chartAt H α).source`, there is a single constant `C ≥ 0` such that for every
base point `b ∈ K` and all frame multi-indices `Jdx`,

  `|tensorChartComponentRaw g_bg 0 s T α (![] : Fin 0 → _) Jdx b| ≤ C · ‖T.toSection b‖`,

where the fibre norm on the right is the `g_bg`-Riemannian bundle norm.  `C` is independent
of `T`, of `Jdx`, and of `b`. -/
theorem tensorChartComponentRaw_abs_le_riemannianFibreNorm
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g_bg 0 s) (b : M), b ∈ K →
      ∀ (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤
          C * ‖T.toSection b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
  -- Unconditional uniform op-norm bound on the chart-`α` forward trivialisation over `K`.
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g_bg 0 s α hK hKsub
  -- The uniform projection operator-norm bound.
  set Cproj : ℝ := chartComponentProjectionUniformBound (E := E) 0 s with hCproj_def
  have hCproj_nn : 0 ≤ Cproj := chartComponentProjectionUniformBound_nonneg (E := E) 0 s
  refine ⟨Cproj * Cop, mul_nonneg hCproj_nn (le_of_lt hCop_pos), ?_⟩
  intro T b hb Jdx
  -- Abbreviate the trivialisation fibre.
  set v : TensorRSModel 0 s ℝ E :=
    tensorTrivProj (I := I) (M := M) g_bg 0 s T α b with hv_def
  -- The raw component is the projection of the trivialisation fibre.
  rw [tensorChartComponentRaw_def]
  -- `|P_IJ v| ≤ ‖P_IJ‖ · ‖v‖ ≤ Cproj · ‖v‖`.
  have h_proj_le :
      |tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v| ≤
        ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := by
    have h := (tensorChartComponentProjection (E := E) 0 s
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx).le_opNorm v
    simpa [Real.norm_eq_abs] using h
  have h_proj_norm_le :
      ‖tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ ≤ Cproj :=
    tensorChartComponentProjection_norm_le_uniform (E := E) 0 s _ Jdx
  -- `‖v‖ ≤ Cop · ‖T.toSection b‖`.
  have h_v_le : ‖v‖ ≤ Cop * ‖T.toSection b‖ := by
    rw [hv_def]
    exact hCop_bound b hb (T.toSection b)
  -- Chain the bounds.
  calc |tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v|
      ≤ ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := h_proj_le
    _ ≤ Cproj * ‖v‖ :=
        mul_le_mul_of_nonneg_right h_proj_norm_le (norm_nonneg _)
    _ ≤ Cproj * (Cop * ‖T.toSection b‖) :=
        mul_le_mul_of_nonneg_left h_v_le hCproj_nn
    _ = Cproj * Cop * ‖T.toSection b‖ := by ring

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
