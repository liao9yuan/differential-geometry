import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def deTurckRHSReanchor (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    SmoothCcTensor g_bg 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).hasCompactSupport

omit [BoundarylessManifold I M] in

@[simp] theorem deTurckRHSReanchor_toSection (g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g_bg 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ) :
    (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ).toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ)).toSection := rfl

private theorem deTurckRHSReanchor_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (k : ℕ) (α : M) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin (2 + k) → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + k)
              (iteratedCovGrad (I := I) g_bg 0 2 k
                (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
                  deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')) α Idx Jdx b) ^ 2) ≤
          Λ ^ 2 * ∑ i ∈ Finset.range (k + 3),
            riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) b
              ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection b) :=
  sorry

theorem deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (k : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) x
            ((iteratedCovGrad (I := I) g_bg 0 2 k
              (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
                deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')).toSection x) ≤
          Λ ^ 2 * ∑ i ∈ Finset.range (k + 3),
            riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) x
              ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection x) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
      deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ' with hS_def
  set Sk : SmoothCcTensor g_bg 0 (2 + k) :=
    iteratedCovGrad (I := I) g_bg 0 2 k S with hSk_def
  set R : M → ℝ := fun b => ∑ i ∈ Finset.range (k + 3),
    riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + i) b
      ((iteratedCovGrad (I := I) g_bg 0 2 i (T - T')).toSection b) with hR_def
  have hR_nn : ∀ b : M, 0 ≤ R b := by
    intro b
    refine Finset.sum_nonneg (fun i _ => ?_)
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g_bg 0 (2 + i) b _
  
  
  
  have hperChart : ∀ α : M, ∃ Kα : ℝ, 0 ≤ Kα ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) b (Sk.toSection b) ≤
          Kα * R b := by
    intro α
    obtain ⟨C, hC_nn, hC⟩ :=
      riemannianFiberNormSq_le_raw_components_on_pouTsupport
        (I := I) (M := M) g_bg 0 (2 + k) α
    obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      deTurckRHSReanchor_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
        (I := I) (M := M) g_bg T T' hδ_lt hδ hδ' k α
    refine ⟨C * Λ ^ 2, mul_nonneg hC_nn (sq_nonneg _), ?_⟩
    intro b hb
    have h1 := hC Sk hb
    have h2 := hΛ b hb
    calc riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) b (Sk.toSection b)
        ≤ C * (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin (2 + k) → Fin (Module.finrank ℝ E),
                (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + k)
                  Sk α Idx Jdx b) ^ 2) := h1
      _ ≤ C * (Λ ^ 2 * R b) := by
          refine mul_le_mul_of_nonneg_left ?_ hC_nn
          simpa only [hSk_def, hS_def, hR_def] using h2
      _ = (C * Λ ^ 2) * R b := by ring
  
  
  choose! Kα hKα_nn hKα using hperChart
  set Ksum : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α with hKsum_def
  have hKsum_nn : 0 ≤ Ksum := Finset.sum_nonneg (fun α _ => hKα_nn α)
  refine ⟨Real.sqrt Ksum, Real.sqrt_nonneg _, ?_⟩
  intro x
  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨x, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hx_tsupport : x ∈ tsupport (fun y : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hα_pos))
  have hsqrt : Real.sqrt Ksum ^ 2 = Ksum := Real.sq_sqrt hKsum_nn
  rw [hsqrt]
  have hKα_le : Kα α ≤ Ksum := by
    rw [hKsum_def]
    exact Finset.single_le_sum (fun β _ => hKα_nn β) hα_finset
  calc riemannianFiberNormSq (I := I) (M := M) g_bg 0 (2 + k) x (Sk.toSection x)
      ≤ Kα α * R x := hKα α hx_tsupport
    _ ≤ Ksum * R x := mul_le_mul_of_nonneg_right hKα_le (hR_nn x)

theorem deTurckRHSSection_iteratedCovGrad_chartComponent_decomposition
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ j ∈ Finset.range (N + 1),
          ‖iteratedCovGrad (I := I) g_bg 0 2 j
            (deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
              deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ')‖ ≤
        C * ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i (T - T')‖ := by
  classical
  set RHSdiff : SmoothCcTensor g_bg 0 2 :=
    deTurckRHSReanchor (I := I) g_bg T hδ_lt hδ -
      deTurckRHSReanchor (I := I) g_bg T' hδ_lt hδ' with hRHSdiff_def
  set Tdiff : SmoothCcTensor g_bg 0 2 := T - T' with hTdiff_def
  
  
  
  have hper : ∀ j ∈ Finset.range (N + 1), ∃ Cj : ℝ, 0 ≤ Cj ∧
      ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖ ≤
        Cj * ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination
        (I := I) (M := M) g_bg T T' hδ_lt hδ hδ' j
    
    
    have hpack :
        ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖ ≤
          Λ * ∑ i ∈ Finset.range (j + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
      have h :=
        tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g_bg
          (c := 2 + j) (N := j + 3)
          (v := fun i => 2 + i)
          (T := fun i => iteratedCovGrad (I := I) g_bg 0 2 i Tdiff)
          (Curv := iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff)
          (C := Λ) hΛ_nn ?_
      · simpa using h
      · intro x
        exact hΛ x
    
    have hwindow : ∑ i ∈ Finset.range (j + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ ≤
        ∑ i ∈ Finset.range (N + 3),
          ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
      exact Finset.range_mono (by omega : j + 3 ≤ N + 3)
    refine ⟨Λ, hΛ_nn, le_trans hpack ?_⟩
    exact mul_le_mul_of_nonneg_left hwindow hΛ_nn
  
  choose! Cj hCj_nn hCj using hper
  refine ⟨∑ j ∈ Finset.range (N + 1), Cj j,
    Finset.sum_nonneg (fun j hj => hCj_nn j hj), ?_⟩
  calc ∑ j ∈ Finset.range (N + 1),
          ‖iteratedCovGrad (I := I) g_bg 0 2 j RHSdiff‖
      ≤ ∑ j ∈ Finset.range (N + 1),
          Cj j * ∑ i ∈ Finset.range (N + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ :=
        Finset.sum_le_sum (fun j hj => hCj j hj)
    _ = (∑ j ∈ Finset.range (N + 1), Cj j) *
          ∑ i ∈ Finset.range (N + 3),
            ‖iteratedCovGrad (I := I) g_bg 0 2 i Tdiff‖ := by
        rw [Finset.sum_mul]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
