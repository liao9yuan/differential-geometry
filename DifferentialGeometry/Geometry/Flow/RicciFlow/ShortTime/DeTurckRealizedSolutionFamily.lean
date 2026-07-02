import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPartialSumJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegSolutionJointlySmooth
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem smoothRiemannianMetric_ext_inner {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext x
    ext v w
    exact h x v w
  cases g with
  | mk gi gsymm gpos gvon gcont =>
    cases g' with
    | mk gi' gsymm' gpos' gvon' gcont' =>
      cases hinner
      rfl

theorem ccTensorBilinSymm_zero_apply (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring

theorem gFibreOpBound_ccTensorBilinSymm_zero (g : SmoothRiemannianMetric I M) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  rw [ccTensorBilinSymm_zero_apply]
  simp only [abs_zero, zero_mul, le_refl]

theorem realizedDeTurck_timeRegular_family
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (ha_eq : a = 4 * Module.finrank ℝ E + 10)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ (T₁ : ℝ), 0 < T₁ ∧ T₁ ≤ T ∧
      ∃ (T_rep : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (T_rep t)) δ),
      T_rep 0 = 0 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T₁,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (T_rep t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (T_rep s) x v w)
          (deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ (T_rep t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T₁
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (T_rep t) hδ_lt (hδ t)) := by
  
  
  
  
  obtain ⟨T₁, hT₁_pos, hT₁_le, F, δ, hδ_lt, hδ, hF_zero, hF_pin_icc, hF_flow, hF_joint⟩ :=
    maxreg_solution_jointly_smooth_representative (I := I) (M := M) g₀ g_bg a ha_super
      ha_eq hT hT1 hTT₀ u gforce hduh hforce hgforce htrace
  refine ⟨T₁, hT₁_pos, hT₁_le, F, δ, hδ_lt, hδ, hF_zero, ?_, hF_flow, hF_joint⟩
  intro t ht
  exact hF_pin_icc t ⟨ht.1.le, le_of_lt ht.2⟩

theorem realizedDeTurckFamily_exists
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
        (T_rep : ℝ → SmoothCcTensor g₀ 0 2),
      0 < T ∧
      g_DT 0 = g₀ ∧
      (∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
        (g_DT t).inner x v w =
          g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_rep t) x v w) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (T_rep s) x v w)
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T g_DT := by
  classical
  
  
  
  
  
  
  set a : ℕ := 4 * Module.finrank ℝ E + 10 with ha_def
  have ha_super : 2 * Module.finrank ℝ E + 10 ≤ a := by omega
  have ha_eq : a = 4 * Module.finrank ℝ E + 10 := ha_def
  
  
  set T₀ : ℝ := (deTurckRicci_quasilinear_maxreg_solution
    (I := I) (M := M) g₀ g_bg a ha_super).choose with hT₀_def
  obtain ⟨_, hT₀_pos, hsol⟩ :=
    (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M) g₀ g_bg a ha_super).choose_spec
  set T : ℝ := min T₀ 1 with hT_def
  have hT_pos : 0 < T := lt_min hT₀_pos one_pos
  have hT_le₀ : T ≤ T₀ := min_le_left _ _
  have hT_le1 : T ≤ 1 := min_le_right _ _
  obtain ⟨u, gforce, hduh, hforce, htrace, _hderiv, hgforce⟩ := hsol hT_pos hT_le₀ hT_le1
  
  
  
  obtain ⟨T₁, hT₁_pos, _hT₁_le, T_rep, δ, hδ_lt, hδ, hrep_zero, _htrep_pin, hflow, hJ⟩ :=
    realizedDeTurck_timeRegular_family (I := I) (M := M) g₀ g_bg a ha_super ha_eq hT_pos hT_le1
      hT_le₀ u gforce hduh hforce hgforce htrace
  
  
  refine
    ⟨T₁, fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (T_rep t) hδ_lt (hδ t),
      T_rep, hT₁_pos, ?_, ?_, hflow, hJ⟩
  · have hrep0 : T_rep 0 = (0 : SmoothCcTensor g₀ 0 2) := hrep_zero
    refine smoothRiemannianMetric_ext_inner (fun x v w => ?_)
    rw [tensorSectionRealizeMetric_inner, hrep0, ccTensorBilinSymm_zero_apply, add_zero]
  · intro t x v w
    rw [tensorSectionRealizeMetric_inner]

end DifferentialGeometry.PDE.RicciFlow
