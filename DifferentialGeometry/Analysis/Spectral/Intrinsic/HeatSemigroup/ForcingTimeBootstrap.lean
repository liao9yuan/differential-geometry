import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingCoordinateTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem deTurckForcing_smoothTimeCoordinateField
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[timeMeasure T] F) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJet (I := I) (M := M) g₀ g_bg a ha_super ha_even hT hT1
      hTT₀ gforce hforce
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (a : ℝ) (Nat.cast_nonneg a)
  
  
  have hslab_sum : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (f i t) ^ 2) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)) (sq_nonneg _)
    · have := hB_le i t ht
      rwa [iteratedDeriv_zero] at this
  
  
  set F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) T then
      ⟨fun i => f i t, hslab_sum t ht⟩ else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t := by
    intro t ht i
    simp only [hF_def, dif_pos ht]
  refine ⟨f, F, hf_smooth, hf_mass, ?_, hF_coeff⟩
  
  
  
  have hjoint : ∀ᵐ t ∂timeMeasure T, ∀ i, (gforce t).coeff i = f i t :=
    (MeasureTheory.ae_all_iff).2 hf_ae
  have hrestrict : ∀ᵐ t ∂timeMeasure T, t ∈ Set.Icc (0 : ℝ) T := by
    rw [show timeMeasure T = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) from rfl]
    exact MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hjoint, hrestrict] with t ht_eq ht_mem
  refine tensorHs.ext ?_
  funext i
  rw [ht_eq i, hF_coeff t ht_mem i]

theorem deTurckForcing_forcingMass_partialSum_contraction
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (d : ℝ) (hda : (a : ℝ) ≤ d)
    (_hd : Summable (forcingMass (I := I) (M := M) gforce d)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
      ∀ s : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        ∑ i ∈ s, forcingMass (I := I) (M := M) gforce (d + 2) i ≤
          θ * (∑ i ∈ s, forcingMass (I := I) (M := M) gforce (d + 2) i) + Kd := by
  classical
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hd2_nonneg : (0 : ℝ) ≤ d + 2 := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith [hda, ha0]
  
  
  obtain ⟨f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJet (I := I) (M := M) g₀ g_bg a ha_super ha_even hT hT1
      hTT₀ gforce hforce


  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (d + 2) hd2_nonneg
  
  
  
  have hmass_le : ∀ i, forcingMass (I := I) (M := M) gforce (d + 2) i ≤ T * B i := by
    intro i
    
    have hae_bound :
        (fun t => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
            (timeModeCoeff (I := I) (M := M) gforce i t) ^ 2)
          ≤ᵐ[timeMeasure T] (fun _ => B i) := by
      have hcoeff := timeModeCoeff_coeFn (I := I) (M := M) gforce i
      have hae_jet : ∀ᵐ t ∂timeMeasure T,
          tensorSobolevWeight (I := I) (M := M) i (d + 2) *
              ((gforce t).coeff i) ^ 2 ≤ B i := by
        have hjet : ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                ((f i) t) ^ 2 ≤ B i := by
          intro t ht
          have := hB_le i t ht
          rwa [iteratedDeriv_zero] at this
        have hjet_ae : ∀ᵐ t ∂timeMeasure T,
            tensorSobolevWeight (I := I) (M := M) i (d + 2) *
                ((f i) t) ^ 2 ≤ B i := by
          rw [show timeMeasure T = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)
              from rfl]
          exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hjet
        filter_upwards [hjet_ae, hf_ae i] with t ht_jet ht_eq
        rwa [ht_eq]
      filter_upwards [hae_jet, hcoeff] with t ht_jet ht_coeff
      rwa [ht_coeff]
    
    
    have hint_lhs : MeasureTheory.Integrable
        (fun t => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
          (timeModeCoeff (I := I) (M := M) gforce i t) ^ 2) (timeMeasure T) :=
      (integrable_timeModeCoeff_sq (I := I) (M := M) gforce i).const_mul
        (tensorSobolevWeight (I := I) (M := M) i (d + 2))
    have hint_rhs : MeasureTheory.Integrable (fun _ : ℝ => B i) (timeMeasure T) :=
      MeasureTheory.integrable_const (B i)
    have hint_mono := MeasureTheory.integral_mono_ae hint_lhs hint_rhs hae_bound
    have hconst_int : ∫ _t, B i ∂(timeMeasure T) = T * B i := by
      rw [MeasureTheory.integral_const, smul_eq_mul,
        timeMeasure_real_univ hT0]
    
    have hmass_eq : forcingMass (I := I) (M := M) gforce (d + 2) i =
        ∫ t, tensorSobolevWeight (I := I) (M := M) i (d + 2) *
          (timeModeCoeff (I := I) (M := M) gforce i t) ^ 2 ∂(timeMeasure T) := by
      rw [forcingMass, norm_timeModeCoeff_sq_eq_integral (I := I) (M := M) gforce i,
        ← MeasureTheory.integral_const_mul]
      rfl
    rw [hmass_eq]
    calc ∫ t, tensorSobolevWeight (I := I) (M := M) i (d + 2) *
            (timeModeCoeff (I := I) (M := M) gforce i t) ^ 2 ∂(timeMeasure T)
        ≤ ∫ _t, B i ∂(timeMeasure T) := hint_mono
      _ = T * B i := hconst_int
  
  have hsummable : Summable (forcingMass (I := I) (M := M) gforce (d + 2)) :=
    Summable.of_nonneg_of_le
      (fun i => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i)
      hmass_le (hB_sum.mul_left T)
  
  
  refine ⟨0, le_refl 0, by norm_num, ∑' i, forcingMass (I := I) (M := M) gforce (d + 2) i,
    tsum_nonneg (fun i => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i), fun s => ?_⟩
  rw [zero_mul, zero_add]
  exact hsummable.sum_le_tsum s
    (fun i _ => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i)

theorem deTurckForcing_forcingMass_summable_succ
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (d : ℝ) (hda : (a : ℝ) ≤ d)
    (hd : Summable (forcingMass (I := I) (M := M) gforce d)) :
    Summable (forcingMass (I := I) (M := M) gforce (d + 2)) := by
  classical
  obtain ⟨θ, hθ_nn, hθ_lt, Kd, hKd_nn, hcontract⟩ :=
    deTurckForcing_forcingMass_partialSum_contraction (I := I) (M := M) g₀ g_bg a ha_super ha_even
      hT hT1 hTT₀ gforce hforce d hda hd
  have hone_sub_θ_pos : 0 < 1 - θ := by linarith
  refine summable_of_sum_le (c := Kd / (1 - θ))
    (fun i => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i) (fun s => ?_)
  have hS := hcontract s
  rw [le_div_iff₀ hone_sub_θ_pos]
  nlinarith [hS]

theorem deTurckForcing_allOrderForcingMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  
  
  have hbase : Summable (forcingMass (I := I) (M := M) gforce (a : ℝ)) :=
    summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) gforce h_compact
  
  
  have hstep : ∀ n : ℕ,
      Summable (forcingMass (I := I) (M := M) gforce ((a : ℝ) + 2 * n)) := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ k ih =>
      have hda : (a : ℝ) ≤ (a : ℝ) + 2 * (k : ℝ) := by
        have : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        linarith
      have hadv := deTurckForcing_forcingMass_summable_succ (I := I) (M := M) g₀ g_bg a
        ha_super ha_even hT hT1 hTT₀ gforce hforce ((a : ℝ) + 2 * (k : ℝ)) hda ih
      have hrw : (a : ℝ) + 2 * (k : ℝ) + 2 = (a : ℝ) + 2 * ((k : ℕ) + 1 : ℕ) := by
        push_cast; ring
      rwa [hrw] at hadv
  
  
  
  intro c _hc
  obtain ⟨n, hn⟩ := exists_nat_ge (c - a)
  have hc_le : c ≤ (a : ℝ) + 2 * (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (n : ℝ) ≤ 2 * (n : ℝ) := by linarith
    linarith
  refine Summable.of_nonneg_of_le
    (fun i => forcingMass_nonneg (I := I) (M := M) gforce c i)
    (fun i => ?_) (hstep n)
  have hwle : tensorSobolevWeight (I := I) (M := M) i c ≤
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2 * (n : ℝ)) :=
    tensorSobolevWeight_mono (I := I) (M := M) i hc_le
  simpa only [forcingMass] using
    mul_le_mul_of_nonneg_right hwle (sq_nonneg _)

theorem deTurckForcing_smoothTimeCoordinateFamily
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[timeMeasure T] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) := by
  obtain ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateField (I := I) (M := M) g₀ g_bg a ha_super ha_even hT hT1
      hTT₀ gforce hforce
  have hF_coord_cont : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContinuousOn.congr (f := fun t => f i t) ?_ ?_
    · exact (hf_smooth i).continuous.continuousOn
    · intro t ht
      exact hF_coeff t ht i
  refine ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, ?_, hF_coeff⟩
  exact deTurckForcing_allOrderForcingMass (I := I) (M := M) g₀ g_bg a ha_super ha_even hT hT1
    hTT₀ gforce hforce

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
