import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFixedPointParabolicSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedVariables false in
theorem maxRegSolField_parabolicInterior_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i :=
  sorry

set_option linter.unusedVariables false in
private theorem deTurckForcing_smoothForcingDriver
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    maxRegSolField_parabolicInterior_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super hT hd₂_pos hd₂_le
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨d₂, hd₂_pos, hd₂_le, ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₂_le
  have hforce_coeff : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  exact hforce_coeff.trans (hψ_ae i)

set_option linter.unusedVariables false in
private theorem deTurckForcing_solCoeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothForcingDriver (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
      gforce hforce
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_top (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) (hf_smooth i)
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le_d₀, hball_W⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₀_pos f
      (fun i => (hf_smooth i).continuous) (B := B0) hB0_sum
      (fun i s hs => by
        have h := hB0_le i s hs
        rwa [iteratedDeriv_zero] at h)
      (deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super)
  have hd₂_le : d₂ ≤ T := le_trans hd₂_le_d₀ hd₀_le
  have hd₂_le_d₀' : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) d₀ :=
    Set.Icc_subset_Icc le_rfl hd₂_le_d₀
  refine ⟨d₂, hd₂_pos, hd₂_le, φ, ⟨hφ_smooth, ?_⟩, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₀) hd₀_pos.le f hf_smooth hf_mass j τ hτ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t (hd₂_le_d₀' ht)
  · have hsolcoeff_ae : ∀ i,
        (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
      intro i
      have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hd₂_le
      have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) hT hT1 hc gforce i)
      have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
        have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
              (fun s => (gforce s).coeff i) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
            (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
        exact htmc.trans
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
            hd₂_le_d₀' (hf_ae i))
      have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
        exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hforce_ae ht
      exact hstep1.trans hstep2
    have hcoeff_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t :=
      (MeasureTheory.ae_all_iff).2 hsolcoeff_ae
    filter_upwards [hcoeff_eq, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht_coeff ht_mem
    refine hball_W t ht_mem
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t) ?_
    intro i
    exact ht_coeff i
  · intro i
    have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hd₂_le
    have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
          (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) hT hT1 hc gforce i)
    have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
      have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun s => (gforce s).coeff i) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
      exact htmc.trans
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
          hd₂_le_d₀' (hf_ae i))
    have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
      rw [hφ_def]
      exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
        hforce_ae ht
    exact hstep1.trans hstep2

set_option linter.unusedVariables false in
private theorem deTurckForcing_fixedPoint_coeff_smooth_and_mass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (c i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] c i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    deTurckForcing_solCoeff_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
  exact deTurckForcing_ballForcing_admits_smoothDriver (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 gforce hforce d₂ hd₂_pos hd₂_le φ hφ_ctrl hφ_ball hφ_ae

theorem deTurckForcing_timeModeCoeff_smooth_allOrderJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] g i) :=
  deTurckForcing_fixedPoint_coeff_smooth_and_mass (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce

theorem deTurckForcing_smoothCoordinate_aeTimeJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJet (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
  refine ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, fun i => ?_⟩
  have htmc : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd₂_le) ?_
    exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  exact htmc.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
