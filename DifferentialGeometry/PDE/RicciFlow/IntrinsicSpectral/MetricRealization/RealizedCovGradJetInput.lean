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
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

/-! ## Leaf-3: the dictionary `ccTensorBilin = raw chart-frame component` -/

/-- The rank-`0` chart-frame basis element `chartFrameBasisModel α x 0 (![] : Fin 0 → _)`
is the unit `(0, 0)`-tensor `constOfIsEmpty 1`.  Both are `0`-ary continuous multilinear
maps, hence determined by their (unique, empty-tuple) value, which is the empty product
`1` on either side. -/
lemma chartFrameBasisModel_zero_eq_constOfIsEmpty (α x : M) :
    chartFrameBasisModel (I := I) (M := M) α x 0
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [chartFrameBasisModel_apply]
  simp

/-- **The bilinear-form value of a `(0,2)`-tensor section equals its raw chart-frame
component.**  For a smooth compactly-supported `(0,2)`-tensor `S`, a chart center `α`, a base
point `x` in the chart source, and frame indices `l b`, the extracted bilinear form
`ccTensorBilin g_bg S x` evaluated on the chart-`α`-frame vectors `(e_l, e_b)` equals the
raw chart-frame scalar component `tensorChartComponentRaw g_bg 0 2 S α (![]) ![l, b] x`. -/
theorem ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (l b : Fin (Module.finrank ℝ E)) :
    ccTensorBilin (I := I) g_bg S x
        (chartBasisVecFiber (I := I) α l x) (chartBasisVecFiber (I := I) α b x) =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)))
        ![l, b] x := by
  classical
  -- Unfold the right-hand side to the chart-frame closed form.
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2 S α hx
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]]
  -- The `(0,0)`-tensor input is the unit `constOfIsEmpty 1`.
  rw [chartFrameBasisModel_zero_eq_constOfIsEmpty (I := I) (M := M) α x]
  -- The left-hand side: `ccTensorBilin = ccTensorModel ![·,·] = ccTensorMultilinear ![·,·]`.
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  -- `Tensor0SSpace.toModel` is the identity on the underlying carrier.
  change (Tensor0SBundle.Tensor0SSpace.toModel
      (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
      ![chartBasisVecFiber (I := I) α l x, chartBasisVecFiber (I := I) α b x] =
    (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      (fun j : Fin 2 => chartBasisVecFiber (I := I) α (![l, b] j) x)
  rw [Tensor0SBundle.Tensor0SSpace.toModel,
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  -- The two tuples agree pointwise.
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **The chart-frame component function of the realized tensor difference is the
symmetrized raw chart-frame component of `S`.**  At every chart point `y` whose chart
preimage `(extChartAt I α).symm y` lies in the chart source, `reprDiffChartCompOnE` equals
the symmetrization `½ (raw_{l,b} + raw_{b,l})` of the raw chart-frame components of the
fixed tensor difference `S = realizableRepr hu₁ − realizableRepr hu₂`. -/
theorem reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
            ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
            ((extChartAt I α).symm y)) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  rw [reprDiffChartCompOnE, ccTensorBilinSymm_apply]
  rw [ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy l b,
    ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy b l]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
