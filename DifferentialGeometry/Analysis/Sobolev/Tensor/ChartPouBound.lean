import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBoundChartPouEuclFderiv
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponentRawNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundChartPushedPartialDeriv
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma eLpNorm_iterWeakPartial_le_basis
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω)
    {m : ℕ} (β : Fin m → Fin (Module.finrank ℝ E)) :
    eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β u Ω) 2
        (volume.restrict Ω) ≤
      eLpNorm (fun y => Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖) 2
        (volume.restrict Ω) := by
  classical
  have hae := iterWeakPartial_smooth_ae_eq_iterClassicalPartial
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open m β
    hu_smooth hu_supp hu_sub
  rw [eLpNorm_congr_ae (p := 2) hae]
  have hpt : ∀ᵐ y ∂(volume.restrict Ω),
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ := by
    filter_upwards with y
    have hle : ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        ‖iteratedFDeriv ℝ m u y‖ :=
      norm_iterClassicalPartial_le_iteratedFDeriv (d := Module.finrank ℝ E) m β hu_smooth y
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (m + 1 : ℝ) := by
      have hle' : (1 : ℝ) ^ 2 ≤ (m + 1 : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      exact (Real.le_sqrt (by positivity : 0 ≤ (1 : ℝ))
        (by positivity : 0 ≤ (m + 1 : ℝ))).2 hle'
    calc
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖
          ≤ ‖iteratedFDeriv ℝ m u y‖ := hle
      _ ≤ Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ := by
            exact le_mul_of_one_le_left (norm_nonneg _) hsqrt
  have hpt' : ∀ᵐ y ∂(volume.restrict Ω),
      ‖iterClassicalPartial (d := Module.finrank ℝ E) m β u y‖ ≤
        ‖(Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m u y‖ : ℝ)‖ := by
    filter_upwards [hpt] with y hy
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)] using hy
  exact eLpNorm_mono_ae hpt'

lemma iteratedWeakSobolevNorm_tensorChartComp_le_rawClassical
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * (∑ m ∈ Finset.range (k + 1),
          eLpNorm (fun y =>
            ‖iteratedFDeriv ℝ m (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)) y‖) 2
            (volume.restrict (tsupport (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set η : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hη_def
  set v : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) with hv_def
  set K : Set EuclN := tsupport η with hK_def
  set f : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T α Idx Jdx with hf_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    rw [hη_def]
    exact chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α
  obtain ⟨Cη, hCη_nn, hη_bound⟩ :=
    exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α k
  have hf_eq : f = fun y : EuclN => η y * v y := by
    rw [hf_def]
    exact tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
      (I := I) (M := M) g r s T α Idx Jdx
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact (tensorChartComponent_contMDiff (I := I) (M := M) g r s T α Idx Jdx).contDiff
  have hf_cpt : HasCompactSupport f := by
    rw [hf_def]
    exact tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  have hf_sub : tsupport f ⊆ Ω := by
    rw [hf_def, tensorChartComp_def, tensorChartComponent_def]
    exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
      (I := I) (M := M)
      (tensorChartComponentPou_support_subset_chart_source (I := I) (M := M) g r s T α Idx Jdx)
  have hts_f_η : tsupport f ⊆ tsupport η := by
    have hsup : Function.support f ⊆ Function.support η := by
      intro z hz
      by_contra hη0
      have hfz : f z = 0 := by
        rw [hf_eq]
        change η z * v z = 0
        have hηz : η z = 0 := by
          by_contra hηz
          exact hη0 (by simpa [Function.support] using hηz)
        simp [hηz]
      exact hz hfz
    exact (closure_mono hsup).trans (by
      simp [tsupport])
  have hPOU_tsupp : tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  have hts_η_Ω : tsupport η ⊆ Ω := by
    set KP : Set EuclN := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      with hKP_def
    have hη_supp_KP : Function.support η ⊆ KP := by
      intro y hy
      by_contra hyK
      apply hy
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
      · obtain ⟨z, hz_target, hzy⟩ := hy_target
        have hy_symm : (toEuclidean (E := E)).symm y = z := by
          rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
        have hval : chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y =
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
          change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else 0) = _
          rw [if_pos (by rw [hy_symm]; exact hz_target)]
        rw [hη_def]
        rw [hval]
        rw [hy_symm]
        by_contra hne
        apply hyK
        have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _ (Function.mem_support.mpr hne)
        have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
          (extChartAt I α).right_inv hz_target
        refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
      · rw [hη_def]
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          else 0) = 0
        rw [if_neg]
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
    have hKP_compact : IsCompact KP :=
      by
      have hts_compact : IsCompact (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
        (isClosed_tsupport _).isCompact
      have hcont_ext : ContinuousOn (extChartAt I α) (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
        refine (continuousOn_extChartAt (I := I) α).mono ?_
        intro x hx
        have hxsrc : x ∈ (chartAt H α).source := hPOU_tsupp hx
        rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hxsrc
        exact hxsrc
      exact (hts_compact.image_of_continuousOn hcont_ext).image
        (toEuclidean (E := E)).continuous
    have hKP_closed : IsClosed KP := hKP_compact.isClosed
    have hη_ts_KP : tsupport η ⊆ KP := by
      rw [tsupport]
      exact hKP_closed.closure_subset_iff.mpr hη_supp_KP
    have hKP_Ω : KP ⊆ Ω := by
      intro y hy
      rcases hy with ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩
      have hxsrc : x ∈ (chartAt H α).source := hPOU_tsupp hx_supp
      have hx_ext : x ∈ (extChartAt I α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]; exact hxsrc
      have hz_target : z ∈ (extChartAt I α).target := by
        rw [← hxz]; exact (extChartAt I α).map_source hx_ext
      exact ⟨z, hz_target, hzy⟩
    exact hη_ts_KP.trans hKP_Ω
  have hv_smooth_Ω : ContDiffOn ℝ (⊤ : ℕ∞) v Ω := by
    rw [hv_def]
    exact chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s T α Idx Jdx
  have hK_meas : MeasurableSet K :=
    (isClosed_tsupport η).measurableSet
  have hK_sub_Ω : K ⊆ Ω := hts_η_Ω
  have hpt_mul : ∀ m ≤ k, ∃ Km : ℝ, 0 ≤ Km ∧ ∀ y ∈ Ω,
      ‖iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y‖ ≤
        Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
    intro m hm
    have hη_bound_m : ∀ l ≤ m, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ l η y‖ ≤ Cη := by
      intro l hl y hy
      exact hη_bound y l (hl.trans hm)
    obtain ⟨Km, hKm_nn, hKm_bound⟩ :=
      norm_iteratedFDerivWithin_mul_le_of_bounded hΩ_open hCη_nn
        hη_smooth hη_bound_m hv_smooth_Ω
    refine ⟨Km, hKm_nn, ?_⟩
    intro y hy
    have hbound := hKm_bound y hy
    have hfc_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : EuclN => η y * v y) y :=
      hη_smooth.contDiffAt.mul (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy))
    have h_within :
        iteratedFDerivWithin ℝ m (fun y : EuclN => η y * v y) Ω y =
          iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y := by
      exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
        (hfc_at.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞)))) hy
    have hv_within : ∀ l ≤ m,
        iteratedFDerivWithin ℝ l v Ω y = iteratedFDeriv ℝ l v y := by
      intro l hl
      exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn
        (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy) |>.of_le (by
          exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))) hy
    rw [← h_within]
    calc
      ‖iteratedFDerivWithin ℝ m (fun y : EuclN => η y * v y) Ω y‖
          ≤ Km * (∑ l ∈ Finset.range (m + 1),
              ‖iteratedFDerivWithin ℝ l v Ω y‖) := hbound
      _ = Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
            have hsum_eq : (∑ l ∈ Finset.range (m + 1),
                  ‖iteratedFDerivWithin ℝ l v Ω y‖) =
                (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
              refine Finset.sum_congr rfl ?_
              intro l hl
              have hl' : l ≤ m := by
                rw [Finset.mem_range] at hl
                omega
              rw [hv_within l hl']
            rw [hsum_eq]
  have hper : ∀ (m : ℕ) (hm : m ≤ k), ∀ β : Fin m → Fin (Module.finrank ℝ E),
      eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
          (volume.restrict Ω) ≤
        ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * (hpt_mul m hm).choose) *
          (∑ l ∈ Finset.range (m + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
    intro m hm β
    let Km : ℝ := (hpt_mul m hm).choose
    have hKm_nn : 0 ≤ Km := (Classical.choose_spec (hpt_mul m hm)).1
    have hKm_bound : ∀ y ∈ Ω,
        ‖iteratedFDeriv ℝ m (fun y : EuclN => η y * v y) y‖ ≤
          Km * (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) :=
      (Classical.choose_spec (hpt_mul m hm)).2
    have hKm_eq : Km = (hpt_mul m hm).choose := rfl
    have hb := eLpNorm_iterWeakPartial_le_basis hΩ_open hf_smooth hf_cpt hf_sub β
    have hder_supp : Function.support (iteratedFDeriv ℝ m f) ⊆ K := by
      intro y hy
      exact hts_f_η ((tsupport_iteratedFDeriv_subset m)
        (subset_tsupport (iteratedFDeriv ℝ m f) hy))
    have hg_supp_K : Function.support (fun y : EuclN =>
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) ⊆ K := by
      intro y hy
      have hder : ‖iteratedFDeriv ℝ m f y‖ ≠ 0 := by
        by_contra hz
        exact hy (by simp [hz])
      exact hder_supp (by
        have hder0 : iteratedFDeriv ℝ m f y ≠ 0 := by
          intro hz
          exact hder (by simp [hz])
        simpa [Function.support] using hder0)
    have hrest : eLpNorm (fun y : EuclN =>
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
          (volume.restrict Ω) =
        eLpNorm (fun y : EuclN =>
          Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
          (volume.restrict K) := by
      have h := eLpNorm_restrict_eq_of_support_subset (p := 2) (μ := volume.restrict Ω)
        (s := K) hg_supp_K
      rw [← h]
      congr 1
      exact Measure.restrict_restrict_of_subset hK_sub_Ω
    have hpt : ∀ᵐ y ∂(volume.restrict K),
        Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖ ≤
          Real.sqrt (m + 1 : ℝ) * Km *
            (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy
      have hyΩ : y ∈ Ω := hK_sub_Ω hy
      have hbound := hKm_bound y hyΩ
      rw [hf_eq]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    calc
      eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
          (volume.restrict Ω)
          ≤ eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
              (volume.restrict Ω) := hb
      _ = eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖) 2
              (volume.restrict K) := hrest
      _ ≤ eLpNorm (fun y : EuclN =>
              Real.sqrt (m + 1 : ℝ) * Km *
                (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
              (volume.restrict K) := by
            have hpt' : ∀ᵐ y ∂(volume.restrict K),
                ‖(Real.sqrt (m + 1 : ℝ) * ‖iteratedFDeriv ℝ m f y‖ : ℝ)‖ ≤
                  ‖(Real.sqrt (m + 1 : ℝ) * Km *
                    (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) : ℝ)‖ := by
              filter_upwards [hpt] with y hy
              have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖ :=
                Finset.sum_nonneg (fun _ _ => norm_nonneg _)
              simpa [Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _),
                abs_of_nonneg hKm_nn, abs_of_nonneg hsum_nn] using hy
            exact eLpNorm_mono_ae hpt'
      _ ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) *
              (∑ l ∈ Finset.range (m + 1),
                eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                  (volume.restrict K)) := by
            have hconst := eLpNorm_const_smul (c := Real.sqrt (m + 1 : ℝ) * Km)
              (f := fun y : EuclN => ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)
              (p := 2) (μ := volume.restrict K)
            have hcont_der : ∀ l : ℕ, ContinuousOn
                (fun y : EuclN => iteratedFDeriv ℝ l v y) Ω := by
              intro l
              have hw : ContinuousOn
                  (fun y : EuclN => iteratedFDerivWithin ℝ l v Ω y) Ω :=
                hv_smooth_Ω.continuousOn_iteratedFDerivWithin (m := l) (by
                  exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))
                  hΩ_open.uniqueDiffOn
              refine hw.congr ?_
              intro y hy
              have hcont_at : ContDiffAt ℝ l v y :=
                (hv_smooth_Ω.contDiffAt (hΩ_open.mem_nhds hy)).of_le (by
                  exact_mod_cast (le_top : (l : ℕ∞) ≤ (⊤ : ℕ∞)))
              exact (iteratedFDerivWithin_eq_iteratedFDeriv hΩ_open.uniqueDiffOn hcont_at hy).symm
            have hfs : ∀ i, i ∈ Finset.range (m + 1) → AEStronglyMeasurable
                (fun y : EuclN => ‖iteratedFDeriv ℝ i v y‖)
                (volume.restrict K) := by
              intro i hi
              exact ContinuousOn.aestronglyMeasurable
                ((hcont_der i).norm.mono (by intro y hy; exact hK_sub_Ω hy)) hK_meas
            have hsum := eLpNorm_sum_le
              (s := Finset.range (m + 1))
              (f := fun l => fun y : EuclN => ‖iteratedFDeriv ℝ l v y‖)
              hfs (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            have hc_nn : 0 ≤ Real.sqrt (m + 1 : ℝ) * Km :=
              mul_nonneg (Real.sqrt_nonneg _) hKm_nn
            have henorm : ‖(Real.sqrt (m + 1 : ℝ) * Km : ℝ)‖ₑ =
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) := by
              rw [← ofReal_norm_eq_enorm (Real.sqrt (m + 1 : ℝ) * Km)]
              congr 1
              rw [Real.norm_eq_abs, abs_of_nonneg hc_nn]
            calc
              eLpNorm (fun y : EuclN =>
                  (Real.sqrt (m + 1 : ℝ) * Km) *
                    (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
                  (volume.restrict K)
                  = ‖(Real.sqrt (m + 1 : ℝ) * Km : ℝ)‖ₑ *
                      eLpNorm (fun y : EuclN =>
                        ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K) := by
                    change eLpNorm ((Real.sqrt (m + 1 : ℝ) * Km) •
                        (fun y : EuclN => ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖)) 2
                        (volume.restrict K) = _
                    exact hconst
              _ = ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Km) *
                      eLpNorm (fun y : EuclN =>
                        ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K) := by
                    rw [henorm]
              _ ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * (hpt_mul m hm).choose) *
                      (∑ l ∈ Finset.range (m + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)) := by
                    rw [hKm_eq]
                    have hsum' : eLpNorm (fun y : EuclN =>
                          ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K) ≤
                        ∑ l ∈ Finset.range (m + 1),
                          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                            (volume.restrict K) := by
                      have hfun_eq : (∑ l ∈ Finset.range (m + 1),
                            fun y : EuclN => ‖iteratedFDeriv ℝ l v y‖) =
                          (fun y : EuclN =>
                            ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l v y‖) := by
                        funext y
                        simp [Finset.sum_apply]
                      rw [← hfun_eq]
                      exact hsum
                    exact mul_le_mul_of_nonneg_left hsum' (zero_le _)
  let Kmfun : (m : ℕ) → m ≤ k → ℝ := fun m hm => (hpt_mul m hm).choose
  have hKmfun_nn : ∀ m hm, 0 ≤ Kmfun m hm := fun m hm =>
    (hpt_mul m hm).choose_spec.1
  let hm_of_mem : ∀ m : ℕ, m ∈ Finset.range (k + 1) → m ≤ k :=
    fun m hm => by rw [Finset.mem_range] at hm; omega
  let C : ℝ := (Finset.range (k + 1)).attach.sum
    (fun ⟨m, hm⟩ =>
      (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) *
        Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm))
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg (fun x hx => mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (hKmfun_nn x.1 (hm_of_mem x.1 x.2)))
  refine ⟨C, hC_nn, ?_⟩
  rw [wkpNorm_eq_sum]
  rw [← Finset.sum_attach]
  have hsum_bdd : (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          ∑ β : Fin m → Fin (Module.finrank ℝ E),
            eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
              (volume.restrict Ω)) ≤
      (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
            ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) *
              (∑ l ∈ Finset.range (m + 1),
                eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                  (volume.restrict K))) := by
    refine Finset.sum_le_sum ?_
    intro ⟨m, hm⟩ _
    have hm_le : m ≤ k := by
      rw [Finset.mem_range] at hm
      omega
    calc
      (∑ β : Fin m → Fin (Module.finrank ℝ E),
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
            (volume.restrict Ω))
          ≤ (∑ β : Fin m → Fin (Module.finrank ℝ E),
              ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m hm_le) *
                (∑ l ∈ Finset.range (m + 1),
                  eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                    (volume.restrict K))) :=
            Finset.sum_le_sum (fun β _ => hper m hm_le β)
      _ = (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
              ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m hm_le) *
                (∑ l ∈ Finset.range (m + 1),
                  eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                    (volume.restrict K)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  have hinner_le : ∀ (m : ℕ) (hm : m ∈ Finset.range (k + 1)),
      (∑ l ∈ Finset.range (m + 1),
        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
          (volume.restrict K)) ≤
        (∑ l ∈ Finset.range (k + 1),
          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
            (volume.restrict K)) := by
    intro m hm
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro l hl; exact Finset.mem_range.mpr (by
        rw [Finset.mem_range] at hl hm
        omega)) (fun _ _ _ => bot_le)
  have hweights_nn : ∀ (m : ℕ) (hm : m ∈ Finset.range (k + 1)),
      0 ≤ (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) := by
    intro m hm
    exact mul_nonneg (by positivity)
      (by positivity : 0 ≤ ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)))
  calc
    (Finset.range (k + 1)).attach.sum
        (fun ⟨m, hm⟩ =>
          ∑ β : Fin m → Fin (Module.finrank ℝ E),
            eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 m β f Ω) 2
              (volume.restrict Ω))
        ≤ (Finset.range (k + 1)).attach.sum
            (fun ⟨m, hm⟩ =>
              (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm)) *
                  (∑ l ∈ Finset.range (m + 1),
                    eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                      (volume.restrict K))) := hsum_bdd
    _ ≤ (Finset.range (k + 1)).attach.sum
            (fun ⟨m, hm⟩ =>
              (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                ENNReal.ofReal (Real.sqrt (m + 1 : ℝ) * Kmfun m (hm_of_mem m hm))) *
          (∑ l ∈ Finset.range (k + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
          have hper : ∀ x ∈ (Finset.range (k + 1)).attach,
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (x.1 + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)) ≤
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (k + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)) := by
            intro x hx
            exact mul_le_mul_of_nonneg_left (hinner_le x.1 x.2) (hweights_nn x.1 x.2)
          calc
            (∑ x ∈ (Finset.range (k + 1)).attach,
              (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                    (∑ l ∈ Finset.range (x.1 + 1),
                      eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                        (volume.restrict K)))
                ≤ (∑ x ∈ (Finset.range (k + 1)).attach,
                    (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                      ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                        (∑ l ∈ Finset.range (k + 1),
                          eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                            (volume.restrict K))) :=
                  Finset.sum_le_sum hper
            _ = (∑ x ∈ (Finset.range (k + 1)).attach,
                    (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                      ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) *
                  (∑ l ∈ Finset.range (k + 1),
                    eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                      (volume.restrict K)) := by
                  have hmul : (∑ x ∈ (Finset.range (k + 1)).attach,
                        (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                          ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) *
                      (∑ l ∈ Finset.range (k + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)) =
                    (∑ x ∈ (Finset.range (k + 1)).attach,
                      (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                        ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)) *
                          (∑ l ∈ Finset.range (k + 1),
                            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                              (volume.restrict K))) := by
                    exact Finset.sum_mul
                      (s := (Finset.range (k + 1)).attach)
                      (f := fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                        (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                          ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2)))
                      (a := (∑ l ∈ Finset.range (k + 1),
                        eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
                          (volume.restrict K)))
                  rw [← hmul]
    _ = ENNReal.ofReal C * (∑ l ∈ Finset.range (k + 1),
            eLpNorm (fun y => ‖iteratedFDeriv ℝ l v y‖) 2
              (volume.restrict K)) := by
          congr 1
          have hsum_eq : (Finset.range (k + 1)).attach.sum
                (fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                  (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) *
                    ENNReal.ofReal (Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) =
              ENNReal.ofReal ((Finset.range (k + 1)).attach.sum
                (fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                  (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) *
                    Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))) := by
            rw [ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.range (k + 1)).attach)
              (f := fun x : {m : ℕ // m ∈ Finset.range (k + 1)} =>
                (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) *
                  Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2))
              (fun x hx => mul_nonneg
                (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
                (hKmfun_nn x.1 (hm_of_mem x.1 x.2)))]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hnn : 0 ≤ Real.sqrt (x.1 + 1 : ℝ) * Kmfun x.1 (hm_of_mem x.1 x.2) :=
              mul_nonneg (Real.sqrt_nonneg _) (hKmfun_nn x.1 (hm_of_mem x.1 x.2))
            have hcard : (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ≥0∞) =
                ENNReal.ofReal (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ) := by
              exact (ENNReal.ofReal_natCast
                (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)))).symm
            rw [hcard]
            rw [← ENNReal.ofReal_mul (by positivity :
              0 ≤ (Fintype.card (Fin x.1 → Fin (Module.finrank ℝ E)) : ℝ))]
            congr 1
            ring
          rw [hsum_eq]
end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
