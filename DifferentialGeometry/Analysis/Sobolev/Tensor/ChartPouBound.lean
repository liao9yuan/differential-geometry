import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBoundChartPouEuclFderiv
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma tensorChartComponent_ae_eq_chartPushed_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2
        =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  filter_upwards [self_mem_ae_restrict (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
    with y hy
  rw [tensorChartComponent_def]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2) hy]
  unfold tensorChartComponentPou
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartSmoothExt_pou_value_bounded
    (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : EuclN, |chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y| ≤ C := by
  classical
  let f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hCD : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α
  have hHCS : HasCompactSupport f :=
    hasCompactSupport_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α
  have hK_compact : IsCompact (closure (Function.support f)) := by
    simpa [tsupport] using hHCS
  by_cases hK_empty : closure (Function.support f) = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have h : y ∉ Function.support f := by
      intro hy
      have hyK : y ∈ closure (Function.support f) := subset_closure hy
      rw [hK_empty] at hyK
      exact absurd hyK (Set.notMem_empty y)
    have hf : f y = 0 := by
      by_contra hfy
      exact h (by simp [Function.support, hfy])
    simpa [f] using hf
  · have hK_ne : (closure (Function.support f)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hK_empty
    have h_abs_cont : ContinuousOn (fun y : EuclN => |f y|) (closure (Function.support f)) :=
      continuous_abs.comp_continuousOn (hCD.continuous.continuousOn)
    obtain ⟨y0, _hy0, hmax⟩ := hK_compact.exists_isMaxOn hK_ne h_abs_cont
    have hmax' : ∀ x, x ∈ closure (Function.support f) → |f x| ≤ |f y0| := hmax
    refine ⟨|f y0|, abs_nonneg _, ?_⟩
    intro y
    by_cases hy : y ∈ closure (Function.support f)
    · exact hmax' y hy
    · have h : y ∉ Function.support f := by
        intro hsupport
        have hyK : y ∈ closure (Function.support f) := subset_closure hsupport
        exact hy hyK
      have hf : f y = 0 := by
        by_contra hfy
        exact h (by simp [Function.support, hfy])
      rw [show chartSmoothExt (I := I) (M := M) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y = 0 by simpa [f] using hf]
      simp

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_eq_zero_of_notMem_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ x : M, x ∉ (chartAt H α).source →
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x = 0 := by
  classical
  intro x hx_src
  have hbase : (trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α).baseSet = (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
      (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hx_base : x ∉ (trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α).baseSet := by
    rw [hbase]
    exact hx_src
  have hzero : tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x = 0 := by
    have hx_base' : x ∉ (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).toPretrivialization.baseSet := by
      change x ∉ (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet
      exact hx_base
    rw [tensorChartComponentRaw_def]
    unfold tensorTrivProj
    have hCLM_zero : (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).continuousLinearMapAt ℝ x = 0 := by
      have hlin : (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).linearMapAt ℝ x = 0 :=
        Bundle.Trivialization.linearMapAt_def_of_notMem
          (e := (trivializationAt (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x) α)) (R := ℝ) hx_base
      ext y
      simp [Bundle.Trivialization.continuousLinearMapAt, hlin]
    rw [hCLM_zero]
    simp
  exact hzero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma norm_iteratedFDerivWithin_mul_le_of_bounded
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {η u : EuclN → ℝ} {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_bound : ∀ l ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ l η x‖ ≤ C)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ω,
      ‖iteratedFDerivWithin ℝ m (fun y => η y * u y) Ω x‖ ≤
        K * ∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ l u Ω x‖ := by
  classical
  set K : ℝ := ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C with hK_def
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) hC)
  · intro x hx
    have hn_top : (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
    have hbound := norm_iteratedFDerivWithin_mul_le
      (𝕜 := ℝ) (f := η) (g := u) (s := Ω) (x := x) (n := m)
      hη.contDiffOn hu hΩ_open.uniqueDiffOn hx
      hn_top
    have hη_le : ∀ l ∈ Finset.range (m + 1),
        ‖iteratedFDerivWithin ℝ l η Ω x‖ ≤ C := by
      intro l hl
      have hl' : l ≤ m := by
        rw [Finset.mem_range] at hl
        omega
      have h_eq : iteratedFDerivWithin ℝ l η Ω x = iteratedFDeriv ℝ l η x := by
        exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
          (hη.contDiffAt.of_le (by
            exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))) hx
      rw [h_eq]
      exact hη_bound l hl' x hx
    have hA_nonneg : 0 ≤ ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) hC)
    have hreindex :
        (∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖) =
        (∑ l ∈ Finset.range (m + 1),
          ‖iteratedFDerivWithin ℝ l u Ω x‖) := by
      simpa using (Finset.sum_range_reflect
        (fun l => ‖iteratedFDerivWithin ℝ l u Ω x‖) (m + 1))
    have hterm : ∀ l ∈ Finset.range (m + 1),
        (m.choose l : ℝ) * C * ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ ≤
          (∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * C) *
            ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := by
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun r => (m.choose r : ℝ) * C)
          (fun r _ => mul_nonneg (by positivity) hC) hl) (norm_nonneg _)
    calc
      ‖iteratedFDerivWithin ℝ m (fun y => η y * u y) Ω x‖
          ≤ ∑ l ∈ Finset.range (m + 1),
              (m.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l η Ω x‖ *
                ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := hbound
      _ ≤ ∑ l ∈ Finset.range (m + 1),
              (m.choose l : ℝ) * C * ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hη_le_l := hη_le l hl
            have hnn : 0 ≤ (m.choose l : ℝ) := by positivity
            have hnn' : 0 ≤ ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖ := norm_nonneg _
            have hstep : (m.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l η Ω x‖ ≤
                (m.choose l : ℝ) * C :=
              mul_le_mul_of_nonneg_left hη_le_l hnn
            exact mul_le_mul_of_nonneg_right hstep hnn'
      _ ≤ (∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C) *
              (∑ l ∈ Finset.range (m + 1),
                ‖iteratedFDerivWithin ℝ (m - l) u Ω x‖) := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum hterm
      _ = (∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C) *
              (∑ l ∈ Finset.range (m + 1),
                ‖iteratedFDerivWithin ℝ l u Ω x‖) := by
            rw [hreindex]
      _ = K * ∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDerivWithin ℝ l u Ω x‖ := by
            rw [hK_def]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartAtlasPOU_sum_eq_one_on_chartTarget
    (α : M) (y : EuclN) :
    (∑ γ ∈ chartAtlasPOU_finset (I := I) (M := M),
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = 1 := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hsum_fin : (∑ᶠ γ : M,
      ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = 1 :=
    SmoothPartitionOfUnity.sum_eq_one (f := chartAtlasPOU I M)
      (x := x) (by simp : x ∈ (univ : Set M))
  rw [← hsum_fin]
  exact (finsum_eq_sum_of_support_subset
    (f := fun γ : M => ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    (s := chartAtlasPOU_finset (I := I) (M := M))
    (by
      intro γ hγ_supp
      by_contra hγ
      have hzero : ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
        chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hγ x
      exact hγ_supp (by simpa [Function.support] using hzero))).symm
end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
