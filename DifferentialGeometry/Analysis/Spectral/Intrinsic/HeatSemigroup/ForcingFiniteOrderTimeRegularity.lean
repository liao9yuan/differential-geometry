import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval

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
theorem deTurckForcing_solCoeff_continuous_smallTimeBase
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      (∀ i, ∃ c : ℝ → ℝ, Continuous c ∧
          c =ᵐ[timeMeasure T]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))) ∧
      (∀ τ : ℝ, 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ B i) ∧
      (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)),
        ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
          deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
      (∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  have hhalf_pos : (0 : ℝ) < R₀ ^ 2 / 2 := div_pos (pow_pos hR₀_pos 2) (by norm_num)
  set ρ : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρ_def
  have hρ_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρ := by rw [hρ_def]; linarith
  set σ' : ℝ := ((a : ℝ) + 2) + ρ with hσ'_def
  obtain ⟨Cσ', hCσ'⟩ := hspatial σ'
  set B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => Cσ' * tensorSobolevWeight (I := I) (M := M) i (-ρ) with hB_def
  have hB_sum : Summable B :=
    (tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_left Cσ'
  have hweight_split : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
          * tensorSobolevWeight (I := I) (M := M) i σ' := by
    intro i
    rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) σ']
    congr 1
    rw [hσ'_def]; ring
  have hB_le : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ B i := by
    intro i t htT
    obtain ⟨hsum_t, hbd_t⟩ := hCσ' t htT
    have hterm : tensorSobolevWeight (I := I) (M := M) i σ'
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ' :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j σ') (sq_nonneg _))) hbd_t
    calc tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
            * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
            * (tensorSobolevWeight (I := I) (M := M) i σ'
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) := by
          rw [hweight_split i]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * Cσ' :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
      _ = B i := by rw [hB_def]; ring
  have hpmc_contOn : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) T) := fun i =>
    continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le
  have htend : Filter.Tendsto
      (fun s : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2) => ∑ i ∈ s, B i)
      Filter.atTop (nhds (∑' i, B i)) := hB_sum.hasSum
  obtain ⟨s₀, hs₀⟩ :=
    ((tendsto_order.1 htend).1 _ (by linarith [hhalf_pos] :
      (∑' i, B i) - R₀ ^ 2 / 2 < ∑' i, B i)).exists
  have htail_B_small :
      (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x)
        ≤ R₀ ^ 2 / 2 := by
    have hcompl : (∑ i ∈ s₀, B i)
        + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x)
        = ∑' i, B i := hB_sum.sum_add_tsum_compl (s := s₀)
    linarith [hcompl, hs₀]
  have hg_contOn : ContinuousOn
      (fun t => ∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2)
      (Set.Icc (0 : ℝ) T) :=
    continuousOn_finset_sum s₀ (fun i _ =>
      ContinuousOn.mul continuousOn_const ((hpmc_contOn i).pow 2))
  have hg0 : (∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) 0) ^ 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [perModeConv_zero_left]; ring)
  have hcwa := hg_contOn 0 ⟨le_rfl, hT.le⟩
  rw [Metric.continuousWithinAt_iff] at hcwa
  obtain ⟨δ, hδ_pos, hδ⟩ := hcwa (R₀ ^ 2 / 2) hhalf_pos
  set d : ℝ := min T (δ / 2) with hd_def
  have hd_pos : 0 < d := lt_min hT (by linarith)
  have hd_le : d ≤ T := min_le_left _ _
  have hd_le2 : d ≤ δ / 2 := min_le_right _ _
  have hcont_head : ∀ t ∈ Set.Icc (0 : ℝ) d,
      (∑ i ∈ s₀, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ≤ R₀ ^ 2 / 2 := by
    intro t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      have : t ≤ δ / 2 := le_trans ht.2 hd_le2
      linarith
    have hh := hδ htT hdist
    simp only [hg0, Real.dist_eq, sub_zero] at hh
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hh)
  have hball_d : ∀ t ∈ Set.Icc (0 : ℝ) d,
      (∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ≤ R₀ ^ 2 := by
    intro t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    set f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
      fun i => tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 with hf_def
    have hf_le_B : ∀ i, f i ≤ B i := fun i => hB_le i t htT
    have hf_nonneg : ∀ i, 0 ≤ f i := fun i =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i ((a : ℝ) + 2)) (sq_nonneg _)
    have hf_sum : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le_B hB_sum
    have hhead_le : (∑ i ∈ s₀, f i) ≤ R₀ ^ 2 / 2 := hcont_head t ht
    have htail_le :
        (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x)
          ≤ (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), B ↑x) :=
      Summable.tsum_le_tsum (fun x => hf_le_B ↑x) (hf_sum.subtype _) (hB_sum.subtype _)
    have hsplit_f : (∑' i, f i)
        = (∑ i ∈ s₀, f i)
          + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x) :=
      (hf_sum.sum_add_tsum_compl (s := s₀)).symm
    calc (∑' i, f i)
        = (∑ i ∈ s₀, f i)
            + (∑' x : ↑((↑s₀ : Set (TensorEigenIdx (I := I) (M := M) g₀ 0 2))ᶜ), f ↑x) :=
          hsplit_f
      _ ≤ R₀ ^ 2 / 2 + R₀ ^ 2 / 2 :=
          add_le_add hhead_le (le_trans htail_le htail_B_small)
      _ = R₀ ^ 2 := by ring
  refine ⟨d, hd_pos, hd_le, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) p.1), ?_, ?_⟩
    · exact Continuous.Icc_extend' ((hpmc_contOn i).restrict)
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
      exact Set.IccExtend_of_mem hT.le _ ht
  · intro τ hτ
    obtain ⟨Cτ, hCτ⟩ := hspatial (τ + ρ)
    refine ⟨fun i => Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρ),
      (tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_left Cτ, ?_⟩
    intro i t ht
    have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hd_le⟩
    obtain ⟨hsum_t, hbd_t⟩ := hCτ t htT
    have hterm : tensorSobolevWeight (I := I) (M := M) i (τ + ρ)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cτ :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j (τ + ρ)) (sq_nonneg _))) hbd_t
    have hsplit_τ : tensorSobolevWeight (I := I) (M := M) i τ
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
          * tensorSobolevWeight (I := I) (M := M) i (τ + ρ) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) (τ + ρ)]
      congr 1; ring
    calc tensorSobolevWeight (I := I) (M := M) i τ
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρ)
            * (tensorSobolevWeight (I := I) (M := M) i (τ + ρ)
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) := by
          rw [hsplit_τ]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * Cτ :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
      _ = Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρ) := by ring
  · have hae_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        (Set.Icc_subset_Icc le_rfl hd_le)
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc gforce i)
    have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i
          = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t :=
      (MeasureTheory.ae_all_iff).2 hae_coeff
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht_coeff ht_mem
    have hnorm_sq : ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ^ 2
        = ∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2)
            * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 := by
      rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
      exact tsum_congr (fun i => by rw [ht_coeff i])
    have hWsq_le : ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ^ 2 ≤ R₀ ^ 2 := by
      rw [hnorm_sq]; exact hball_d t ht_mem
    nlinarith [norm_nonneg (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t), hR₀_pos.le, hWsq_le]
  · intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le)
      (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc gforce i)

private theorem perModeConv_contDiff_succ_of_contDiff (lam : ℝ) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (k : ℕ) f) : ContDiff ℝ ((k + 1 : ℕ)) (perModeConv lam f) := by
  have hfcont : Continuous f := hf.continuous
  have hphi_low : ContDiff ℝ (k : ℕ) (perModeConv lam f) :=
    perModeConv_contDiff_of_contDiff (k : ℕ∞) lam f hf
  have hderiv_eq : deriv (perModeConv lam f)
      = fun t => f t - lam * perModeConv lam f t :=
    deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
  have hdiff : Differentiable ℝ (perModeConv lam f) :=
    fun t => (perModeConv_hasDerivAt lam hfcont t).differentiableAt
  rw [Nat.cast_succ, contDiff_succ_iff_deriv]
  refine ⟨hdiff, fun hω => absurd hω (by simp), ?_⟩
  rw [hderiv_eq]
  exact hf.sub (contDiff_const.mul hphi_low)

private theorem perModeConv_iteratedDeriv_succ_finiteOrder (lam : ℝ) {f : ℝ → ℝ}
    (p : ℕ) (hf : ContDiff ℝ (p : ℕ) f) :
    iteratedDeriv (p + 1) (perModeConv lam f)
      = fun t => iteratedDeriv p f t - lam * iteratedDeriv p (perModeConv lam f) t := by
  have hfcont : Continuous f := hf.continuous
  have hphi_smooth : ContDiff ℝ (p : ℕ) (perModeConv lam f) :=
    perModeConv_contDiff_of_contDiff (p : ℕ∞) lam f hf
  have hderiv_eq : deriv (perModeConv lam f)
      = fun t => f t - lam * perModeConv lam f t :=
    deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
  rw [iteratedDeriv_succ', hderiv_eq]
  funext t
  have hcd_f : ContDiffAt ℝ (p : WithTop ℕ∞) f t := hf.contDiffAt
  have hcd_phi : ContDiffAt ℝ (p : WithTop ℕ∞) (perModeConv lam f) t :=
    hphi_smooth.contDiffAt
  have hcd_lp : ContDiffAt ℝ (p : WithTop ℕ∞)
      (fun t => lam * perModeConv lam f t) t :=
    hcd_phi.const_smul lam
  have hsub :
      iteratedDeriv p (fun t => f t - lam * perModeConv lam f t) t
        = iteratedDeriv p f t
          - iteratedDeriv p (fun t => lam * perModeConv lam f t) t := by
    have hshow :
        (fun t => f t - lam * perModeConv lam f t)
          = f - fun t => lam * perModeConv lam f t := by
      funext u; simp
    rw [hshow, iteratedDeriv_sub hcd_f hcd_lp]
  rw [hsub]
  have hconst :
      iteratedDeriv p (fun t => lam * perModeConv lam f t) t
        = lam * iteratedDeriv p (perModeConv lam f) t := by
    have hsmul := iteratedDeriv_const_smul (𝕜 := ℝ) (F := ℝ) (R := ℝ)
      (n := p) (f := perModeConv lam f) hcd_phi lam
    simp only [smul_eq_mul] at hsmul
    exact hsmul
  rw [hconst]

private theorem perModeConv_sq_le_T_mul_int (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ}
    {c : ℝ → ℝ} (hc : Continuous c) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (perModeConv lam c t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hbase : (perModeConv lam c t) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 :=
    perModeConv_sq_le_time_mul_integral' lam hlam hc ht0
  have hint_t_nn : 0 ≤ ∫ s in (0 : ℝ)..t, (c s) ^ 2 :=
    intervalIntegral.integral_nonneg ht0 (fun s _ => sq_nonneg _)
  have hint_le : (∫ s in (0 : ℝ)..t, (c s) ^ 2) ≤ ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := t) (c := T)
        ((hc.pow 2).intervalIntegrable 0 t)
        ((hc.pow 2).intervalIntegrable t T)]
    have htail : 0 ≤ ∫ s in t..T, (c s) ^ 2 :=
      intervalIntegral.integral_nonneg htT (fun s _ => sq_nonneg _)
    linarith
  calc (perModeConv lam c t) ^ 2
      ≤ t * ∫ s in (0 : ℝ)..t, (c s) ^ 2 := hbase
    _ ≤ T * ∫ s in (0 : ℝ)..T, (c s) ^ 2 := by
        exact mul_le_mul htT hint_le hint_t_nn hT

private theorem perModeConv_finiteOrder_timeDeriv_spectralMass_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {T : ℝ} (hT : 0 ≤ T) (k : ℕ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ (k : ℕ) (f i))
    (hf_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i) :
    ∀ (m : ℕ), m ≤ k + 1 → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv m
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i)) t) ^ 2
            ≤ Cmaj i := by
  intro m
  induction m with
  | zero =>
      intro _ σ hσ
      obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (Nat.zero_le k) σ hσ
      refine ⟨fun i => T * (T * B i), (hB_sum.mul_left T).mul_left T, ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hcont : Continuous (f i) := (hf_smooth i).continuous
      have hbound : (perModeConv lam (f i) t) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f i s ^ 2 :=
        perModeConv_sq_le_T_mul_int lam hlam_nn hcont hT ht
      have hintegral_le :
          tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ T * B i := by
        have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2 ≤ B i := by
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2)
            volume 0 T :=
          ((hcont.pow 2).const_mul _).intervalIntegrable 0 T
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) volume 0 T :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..T,
              tensorSobolevWeight (I := I) (M := M) i σ * f i s ^ 2
            ≤ ∫ _s in (0 : ℝ)..T, B i := by
          refine intervalIntegral.integral_mono_on hT hi_lhs hi_const ?_
          intro s hs
          exact hpoint s hs
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
        calc tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2
            ≤ (T - 0) * B i := hmono
          _ = T * B i := by ring
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv 0 (perModeConv lam (f i)) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ * (perModeConv lam (f i) t) ^ 2 := by
            rw [iteratedDeriv_zero]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ * (T * ∫ s in (0 : ℝ)..T, f i s ^ 2) :=
            mul_le_mul_of_nonneg_left hbound hwt_nn
        _ = T * (tensorSobolevWeight (I := I) (M := M) i σ * ∫ s in (0 : ℝ)..T, f i s ^ 2) := by
            ring
        _ ≤ T * (T * B i) := by
            apply mul_le_mul_of_nonneg_left hintegral_le hT
  | succ p ih =>
      intro hm σ hσ
      have hp_le_k : p ≤ k := by omega
      obtain ⟨Bf, hBf_sum, hBf_le⟩ := hf_mass p hp_le_k σ hσ
      obtain ⟨Cprev, hCprev_sum, hCprev_le⟩ := ih (by omega) (σ + 2) (by linarith)
      refine ⟨fun i => 2 * Bf i + 2 * Cprev i,
        (hBf_sum.mul_left 2).add (hCprev_sum.mul_left 2), ?_⟩
      intro i t ht
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
      have hwtσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      have hfp : ContDiff ℝ (p : ℕ) (f i) := (hf_smooth i).of_le (by exact_mod_cast hp_le_k)
      have hrec := perModeConv_iteratedDeriv_succ_finiteOrder lam p hfp
      have hval : iteratedDeriv (p + 1) (perModeConv lam (f i)) t
          = iteratedDeriv p (f i) t - lam * iteratedDeriv p (perModeConv lam (f i)) t := by
        rw [hrec]
      have hexpand_sq :
          (iteratedDeriv (p + 1) (perModeConv lam (f i)) t) ^ 2
            ≤ 2 * (iteratedDeriv p (f i) t) ^ 2
              + 2 * (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
        rw [hval]
        nlinarith [sq_nonneg (iteratedDeriv p (f i) t
            + lam * iteratedDeriv p (perModeConv lam (f i)) t),
          sq_nonneg (iteratedDeriv p (f i) t
            - lam * iteratedDeriv p (perModeConv lam (f i)) t)]
      have hforce_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv p (f i) t) ^ 2 ≤ Bf i :=
        hBf_le i t ht
      have hphi_term :
          tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 ≤ Cprev i :=
        hCprev_le i t ht
      have hweight_step :
          tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2
            ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) := by
        have h1le : (1 : ℝ) ≤ 1 + lam := by linarith
        have hlamsq_le : lam ^ 2 ≤ (1 + lam) ^ 2 := by nlinarith [hlam_nn]
        have hwtσ_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
          tensorSobolevWeight_pos (I := I) (M := M) i σ
        have hsplit : tensorSobolevWeight (I := I) (M := M) i (σ + 2)
            = tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam) ^ 2 := by
          unfold tensorSobolevWeight
          rw [hlam_def] at *
          rw [Real.rpow_add (by linarith)]
          congr 1
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hlamsq_le hwtσ_nn
      have hlam_sq_term :
          tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            ≤ Cprev i := by
        have heq : (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            = lam ^ 2 * (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by ring
        calc tensorSobolevWeight (I := I) (M := M) i σ *
              (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2
            = (tensorSobolevWeight (I := I) (M := M) i σ * lam ^ 2) *
                (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
              rw [heq]; ring
          _ ≤ tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
                (iteratedDeriv p (perModeConv lam (f i)) t) ^ 2 := by
              apply mul_le_mul_of_nonneg_right hweight_step (sq_nonneg _)
          _ ≤ Cprev i := hphi_term
      calc tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv (p + 1) (perModeConv lam (f i)) t) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (2 * (iteratedDeriv p (f i) t) ^ 2
                + 2 * (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2) :=
            mul_le_mul_of_nonneg_left hexpand_sq hwtσ_nn
        _ = 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv p (f i) t) ^ 2)
              + 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (lam * iteratedDeriv p (perModeConv lam (f i)) t) ^ 2) := by ring
        _ ≤ 2 * Bf i + 2 * Cprev i := by
            have h1 := mul_le_mul_of_nonneg_left hforce_term (by norm_num : (0 : ℝ) ≤ 2)
            have h2 := mul_le_mul_of_nonneg_left hlam_sq_term (by norm_num : (0 : ℝ) ≤ 2)
            linarith

set_option linter.unusedVariables false in
theorem perModeConv_finiteOrder_timeJet_spectralMass_gain
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {T : ℝ} (hT : 0 ≤ T) (k : ℕ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ (k : ℕ) (f i))
    (hf_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiff ℝ ((k + 1 : ℕ))
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i))) ∧
    (∀ (j : ℕ), j ≤ k + 1 → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i)) t) ^ 2 ≤ B i) := by
  refine ⟨fun i =>
    perModeConv_contDiff_succ_of_contDiff (TensorEigenIdx.lambda (I := I) (M := M) i) k
      (hf_smooth i), ?_⟩
  intro j hj τ hτ
  exact perModeConv_finiteOrder_timeDeriv_spectralMass_le (I := I) (M := M)
    g hT k f hf_smooth hf_mass j hj τ hτ

private theorem exists_smoothCcTensor_of_allOrder_spectralMass_local
    (g₀ : SmoothRiemannianMetric I M)
    (d : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i) :
    ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = d i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  obtain ⟨B0, hB0s, hB0le⟩ := hmass 0 le_rfl
  set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
    tensorHs_of_spectralMass_majorant (I := I) (M := M) d B0 hB0s hB0le with hv0_def
  set u : TensorL2 0 2 g₀ :=
    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
  have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = d i := by
    intro i
    rw [hu_def, tensorHsToL2_tensorL2Coeff]
    simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff]
  have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hBs
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hu_coeff i]; exact hBle i
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
    allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
  obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
  refine ⟨S, fun i => ?_⟩
  have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
        = (S : TensorL2 0 2 g₀) from rfl, hS]
  rw [hSL2, hu_coeff i]

private def deTurckRHSReconSectionFO (g₀ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ)).hasCompactSupport }

private theorem fiber_contDiffOn_Icc_finiteOrder
    (f : M → ℝ → ℝ) {T : ℝ} {n : WithTop ℕ∞}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (x : M) :
    ContDiffOn ℝ n (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) n (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have hcomp := hf.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

private theorem partialSnd_contMDiffOn_Icc_finiteOrder
    (f : M → ℝ → ℝ) {T : ℝ} (N : ℕ)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N : WithTop ℕ∞) + 1)
      (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞)
      (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt T 0 with hT0 | hT0
  · have hzero : Set.EqOn
        (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (fun _ : M × ℝ => (0 : ℝ)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
      intro p hp
      have hnacc : ¬ AccPt p.2 (Filter.principal (Set.Icc (0 : ℝ) T)) := by
        rw [accPt_principal_iff_nhdsWithin]
        have hempty : Set.Icc (0 : ℝ) T \ {p.2} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hy.2 (Set.mem_singleton_iff.mpr
            ((Set.subsingleton_Icc_of_ge hT0) hy.1 hp.2))
        rw [hempty, nhdsWithin_empty]
        exact not_neBot.mpr rfl
      exact derivWithin_zero_of_not_accPt hnacc
    exact (contMDiffOn_const (c := (0 : ℝ))).congr hzero
  have hUM : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) T) :=
    (uniqueDiffOn_Icc hT0).uniqueMDiffOn
  have hrw : (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) =
      fun p : M × ℝ =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact (fderivWithin_derivWithin (𝕜 := ℝ) (f := fun s => f p.1 s)
      (s := Set.Icc (0 : ℝ) T) (x := p.2)).symm
  rw [hrw]
  intro p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      ((N : WithTop ℕ∞) + 1)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        ((N : WithTop ℕ∞) + 1)
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨Set.mem_univ _, hq.2⟩
    exact (hf (p₀.1, p₀.2) ⟨Set.mem_univ _, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (N : WithTop ℕ∞) + 1) (m := (N : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

private theorem hasDerivWithinAt_integral_param_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
      (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => ∫ x, f x t ∂μ)
      (∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ) (Set.Icc (0 : ℝ) T) t₀ := by
  set s : Set ℝ := Set.Icc (0 : ℝ) T with hs_def
  have hconv : Convex ℝ s := convex_Icc 0 T
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hT
  set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) s t with hFd
  have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hf.continuousOn
  have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((0 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => Fd p.1 p.2) ((Set.univ : Set M) ×ˢ s) :=
    partialSnd_contMDiffOn_Icc_finiteOrder f 0
      (by rw [Nat.cast_zero, zero_add]; exact hf)
  have hFd_cont : ContinuousOn (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hFd_joint.continuousOn
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ s) :=
    isCompact_univ.prod (isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont
  have hfiber_deriv : ∀ x : M, ∀ y ∈ s, HasDerivWithinAt (fun u => f x u) (Fd x y) s y := by
    intro x y hy
    have hcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (fun u : ℝ => f x u) s :=
      fiber_contDiffOn_Icc_finiteOrder f hf x
    exact ((hcd.differentiableOn one_ne_zero y hy)).hasDerivWithinAt
  have hfiber : ∀ x : M, HasDerivWithinAt (fun u => f x u) (Fd x t₀) s t₀ :=
    fun x => hfiber_deriv x t₀ ht₀
  have hbound : ∀ x : M, ∀ t ∈ s, ‖f x t - f x t₀‖ ≤ C * ‖t - t₀‖ := by
    intro x t ht
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => hfiber_deriv x y hy) (fun y hy => ?_) hconv ht₀ ht
    exact hC (x, y) ⟨Set.mem_univ _, hy⟩
  have hf_slice_cont : ∀ t ∈ s, Continuous (fun x : M => f x t) := by
    intro t ht
    have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ s) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have := (hf_cont.comp harg hmaps)
    rw [continuousOn_univ] at this
    exact this
  have hf_int : ∀ t ∈ s, Integrable (fun x : M => f x t) μ := by
    intro t ht
    exact integrableOn_univ.mp
      ((hf_slice_cont t ht).continuousOn.integrableOn_compact isCompact_univ)
  set G : ℝ → ℝ := fun t => ∫ x, f x t ∂μ with hG
  set G' : ℝ := ∫ x, Fd x t₀ ∂μ with hG'
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope_eq : ∀ t : ℝ, t ∈ s \ {t₀} →
      slope G t₀ t = ∫ x, slope (fun u => f x u) t₀ t ∂μ := by
    intro t ht
    have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
    rw [slope_def_field, hG]
    simp only []
    rw [show (∫ x, f x t ∂μ) - ∫ x, f x t₀ ∂μ
        = ∫ x, (f x t - f x t₀) ∂μ from
      (integral_sub (hf_int t ht.1) (hf_int t₀ ht₀)).symm]
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [slope_def_field, div_eq_inv_mul]
  have heq : (fun t => ∫ x, slope (fun u => f x u) t₀ t ∂μ) =ᶠ[𝓝[s \ {t₀}] t₀]
      slope G t₀ := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨s \ {t₀}, self_mem_nhdsWithin, fun t ht => (hslope_eq t ht).symm⟩
  refine Filter.Tendsto.congr' heq ?_
  · have hmeas : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        AEStronglyMeasurable (fun x : M => slope (fun u => f x u) t₀ t) μ := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      have : Continuous (fun x : M => slope (fun u => f x u) t₀ t) := by
        simp only [slope_def_field]
        exact ((hf_slice_cont t ht.1).sub (hf_slice_cont t₀ ht₀)).div_const _
      exact this.aestronglyMeasurable
    have hbnd : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        ∀ᵐ x ∂μ, ‖slope (fun u => f x u) t₀ t‖ ≤ C := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      refine Filter.Eventually.of_forall (fun x => ?_)
      have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
      have hpos : 0 < ‖t - t₀‖ := by
        rw [norm_pos_iff]; exact sub_ne_zero.mpr htne
      rw [slope_def_field, norm_div, div_le_iff₀ hpos]
      exact hbound x t ht.1
    have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
        (fun t => slope (fun u => f x u) t₀ t) (𝓝[s \ {t₀}] t₀)
        (𝓝 (Fd x t₀)) :=
      Filter.Eventually.of_forall (fun x => (hasDerivWithinAt_iff_tendsto_slope.mp (hfiber x)))
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : M => C)
      (F := fun t x => slope (fun u => f x u) t₀ t)
      (f := fun x => Fd x t₀)
      hmeas hbnd (integrable_const C) hlim
    simpa [hG'] using this

private theorem contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (N : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞) (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ContDiffOn ℝ (N : WithTop ℕ∞) (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro N
  induction N with
  | zero =>
      intro f hf
      rw [Nat.cast_zero] at hf
      rw [Nat.cast_zero, contDiffOn_zero]
      have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := hf.continuousOn
      obtain ⟨C, hC⟩ :=
        (isCompact_univ.prod isCompact_Icc).exists_bound_of_continuousOn hf_cont
      have hf_slice_cont : ∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (fun x : M => f x t) := by
        intro t ht
        have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
        have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
            ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun x _ => ⟨Set.mem_univ _, ht⟩
        have := (hf_cont.comp harg hmaps)
        rw [continuousOn_univ] at this
        exact this
      have hfib : ∀ x : M, ContinuousOn (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
        intro x
        have hcd := fiber_contDiffOn_Icc_finiteOrder (n := (0 : WithTop ℕ∞)) f hf x
        rw [contDiffOn_zero] at hcd
        exact hcd
      intro t₀ ht₀
      have hkey : Filter.Tendsto (fun t : ℝ => ∫ x, f x t ∂μ)
          (nhdsWithin t₀ (Set.Icc (0 : ℝ) T)) (𝓝 (∫ x, f x t₀ ∂μ)) := by
        refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (μ := μ) (bound := fun _ : M => C)
          (F := fun (t : ℝ) (x : M) => f x t) (f := fun x : M => f x t₀)
          ?_ ?_ (integrable_const C) ?_
        · refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
          exact (hf_slice_cont t ht).aestronglyMeasurable
        · refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
          exact Filter.Eventually.of_forall (fun x => hC (x, t) ⟨Set.mem_univ _, ht⟩)
        · exact Filter.Eventually.of_forall (fun x => hfib x t₀ ht₀)
      exact hkey
  | succ n ih =>
      intro f hf
      have hf1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hfsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
        rw [Nat.cast_succ] at hf
        exact hf
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hUD]
      refine ⟨?_, ?_, ?_⟩
      · exact fun t₀ ht₀ =>
          (hasDerivWithinAt_integral_param_Icc_finiteOrder
            μ f hT hf1 ht₀).differentiableWithinAt
      · intro hcontra; exact absurd hcontra (by simp)
      · have hderiv_eq : Set.EqOn
            (derivWithin (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
            (fun t : ℝ => ∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t ∂μ)
            (Set.Icc (0 : ℝ) T) := by
          intro t₀ ht₀
          exact (hasDerivWithinAt_integral_param_Icc_finiteOrder
            μ f hT hf1 ht₀).derivWithin (hUD t₀ ht₀)
        refine ContDiffOn.congr ?_ hderiv_eq
        exact ih (fun x t => derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t)
          (partialSnd_contMDiffOn_Icc_finiteOrder f n hfsucc)

private local instance tensorRSModelNormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModelNormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2

private theorem clm_comm_iteratedDerivWithin_finiteOrder {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (γ : ℝ → V) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (j : ℕ)
    (hγ : ContDiffWithinAt ℝ (j : WithTop ℕ∞) γ (Set.Icc (0 : ℝ) T) t) :
    iteratedDerivWithin j (fun s => L (γ s)) (Set.Icc (0 : ℝ) T) t =
      L (iteratedDerivWithin j γ (Set.Icc (0 : ℝ) T) t) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hcomp : (fun s => L (γ s)) = L ∘ γ := rfl
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hcomp,
    L.iteratedFDerivWithin_comp_left hγ hUD ht le_rfl,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedDerivWithin_eq_iteratedFDerivWithin]
  rfl

private theorem iteratedDerivWithin_integral_param_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (j : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (j : WithTop ℕ∞) (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) t₀ =
          ∫ x, iteratedDerivWithin j (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro j
  induction j with
  | zero =>
      intro f _ t₀ _
      simp only [iteratedDerivWithin_zero]
  | succ n ih =>
      intro f hf t₀ ht₀
      have hf1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hfsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
        rw [Nat.cast_succ] at hf
        exact hf
      rw [iteratedDerivWithin_succ']
      set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) t
        with hFd
      have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n : WithTop ℕ∞)
          (fun p : M × ℝ => Fd p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        partialSnd_contMDiffOn_Icc_finiteOrder f n hfsucc
      have hderiv_eqOn : Set.EqOn (derivWithin (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
          (fun t => ∫ x, Fd x t ∂μ) (Set.Icc (0 : ℝ) T) := by
        intro t ht
        exact (hasDerivWithinAt_integral_param_Icc_finiteOrder μ f hT hf1 ht).derivWithin
          (hUD t ht)
      rw [iteratedDerivWithin_congr hderiv_eqOn ht₀, ih Fd hFd_joint t₀ ht₀]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (iteratedDerivWithin_succ').symm

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem smoothCcTensor_path_toFun_contDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} {N : WithTop ℕ∞}
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    (x : M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContDiffWithinAt ℝ N (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 2
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) N (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun s : ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x ((Sfam s).toSection x))
      (Set.Icc (0 : ℝ) T) :=
    hSfam.comp harg hmaps
  have h2 := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)
    (IB := I) (IM := 𝓘(ℝ, ℝ))).mp (h1 t ht) |>.2
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at h2
  set e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x with he
  have hxbase : x ∈ e.baseSet := by
    rw [he]
    change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) x).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) x).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change x ∈ (trivializationAt E (TangentSpace I) x).baseSet
        rw [show (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source from
          TangentBundle.trivializationAt_baseSet (I := I) x]
        exact mem_chart_source H x
  set L : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    (Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) 0 2 x).comp (e.symmL ℝ x) with hL
  have hLeq : ∀ s : ℝ, L ((e ⟨x, (Sfam s).toSection x⟩).2) = (Sfam s).toFun x := by
    intro s
    have h3 : e.continuousLinearMapAt ℝ x ((Sfam s).toSection x)
        = (e ⟨x, (Sfam s).toSection x⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Trivialization.coe_linearMapAt_of_mem _ hxbase]
    rw [hL, ContinuousLinearMap.comp_apply, ← h3,
      Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]
    rfl
  have h4 : ContDiffWithinAt ℝ N (fun s : ℝ => L ((e ⟨x, (Sfam s).toSection x⟩).2))
      (Set.Icc (0 : ℝ) T) t :=
    L.contDiff.comp_contDiffWithinAt h2
  exact h4.congr (fun s _ => (hLeq s).symm) (hLeq t).symm

section FiniteOrderSpectralPathEngine

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth
  tensorChartComponentRaw tensorChartComponentProjection tensorChartBasisElement
  toEuclidean_extChartAt_mem_chartTargetEuclid)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (d : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (hd : ∀ i, tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S) i = d i)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x =
      ∑' i, d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  set u : TensorL2 0 2 g := SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S with hu_def
  have hcoeff_u : ∀ i, tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i = d i := hd
  have hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u := by
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g u (fun σ hσ => ?_)
    obtain ⟨B, hB_sum, hB_le⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hcoeff_u i]; exact hB_le i
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  have hcauchy : ∀ kc : ℕ, CauchySeq (fun n =>
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g) (r := 0) (s := 2) (2 * kc) (F n)) :=
    fun kc => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * kc)
  have hF_L2 : Filter.Tendsto (fun n => (F n : TensorL2 0 2 g)) Filter.atTop (nhds u) :=
    spectralPartialSum_toL2_tendsto (I := I) (M := M) g u
  have hTrep : (S : TensorL2 0 2 g) = u := rfl
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hexists : ∃ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 < ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) β : M → ℝ) x = 0 := by
      intro β hβ
      have hle := hcon β hβ
      have hnn := (chartAtlasPOU I M).nonneg β x
      linarith
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨β, _hβmem, hβpos⟩ := hexists
  set ρ : ℝ := ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x with hρ_def
  have hx_src : x ∈ (chartAt H β).source := by
    have hsub := chartAtlasPOU_isSubordinate (I := I) (M := M) β
    apply hsub
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hβpos))
  set yx : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (extChartAt I β x) with hyx_def
  have hyx_mem := toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) β hx_src
  rw [← hyx_def] at hyx_mem
  have hround : (extChartAt I β).symm (toEuclidean.symm yx) = x := by
    rw [hyx_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I β).left_inv (by rw [extChartAt_source (I := I)]; exact hx_src)
  have hcomp_eq : ∀ (Z : SmoothCcTensor g 0 2) (Q : CompIdx E 0 2),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent
          (I := I) (M := M) g 0 2 Z β Q.1 Q.2 yx =
        ρ * tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x := by
    intro Z Q
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hyx_mem, hround]
    rfl
  have hraw_tendsto : ∀ Q : CompIdx E 0 2,
      Filter.Tendsto
        (fun n => tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x)
        Filter.atTop
        (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S β Q.1 Q.2 x)) := by
    intro Q
    have hct := spectralChartComponent_tendsto (I := I) (M := M) g u hcauchy hF_L2 S hTrep
      β Q hyx_mem
    simp only [hcomp_eq] at hct
    have hρne : ρ ≠ 0 := ne_of_gt hβpos
    have hscaled := hct.const_mul ρ⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hρne, one_mul] at hscaled
    exact hscaled
  have htend_sec : Filter.Tendsto (fun n => ((F n).toSection x :
      Tensor0SBundle.TensorRSSpace 0 2 I x)) Filter.atTop (nhds (S.toSection x)) := by
    have hexpand : ∀ Z : SmoothCcTensor g 0 2, Z.toSection x =
        ∑ Q : CompIdx E 0 2,
          tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x •
            chartBasisFiberSection (I := I) (M := M) 0 2 β Q x :=
      fun Z => toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 Z β hx_src
    simp only [hexpand]
    exact tendsto_finset_sum _ (fun Q _ => (hraw_tendsto Q).smul_const _)
  have hLval : ∀ Z : SmoothCcTensor g 0 2,
      tensorChartComponentRaw (I := I) (M := M) g 0 2 Z α ![] Jdx x =
        (tensorChartComponentProjection (E := E) 0 2 ![] Jdx)
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) α).continuousLinearMapAt
            ℝ x (Z.toSection x)) :=
    fun Z => rfl
  have htend_raw : Filter.Tendsto (fun n =>
      tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) α ![] Jdx x) Filter.atTop
      (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x)) := by
    simp only [hLval]
    exact ((tensorChartComponentProjection (E := E) 0 2 ![] Jdx).continuous.tendsto _).comp
      ((((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) α).continuousLinearMapAt
          ℝ x).continuous.tendsto _).comp htend_sec)
  have hpartial : ∀ n, tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) α ![] Jdx x =
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x := by
    intro n
    have hFn : F n = finiteEigenCombo (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g n)
        (fun i => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) := rfl
    rw [hFn, tensorChartComponentRaw_finiteEigenCombo (I := I) (M := M) g _ _ α ![] Jdx x]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcoeff_u i])
  obtain ⟨CK, pK, hCK_nn, hCK⟩ :=
    exists_rawComponentRaw_eigen_pointwise_le_lambda_pow (I := I) (M := M) g α Jdx hx
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  obtain ⟨B2, hB2_sum, hB2⟩ := hmass (2 * ((pK : ℝ) + (sW : ℝ))) (by positivity)
  have hB2_nn : ∀ i, 0 ≤ B2 i := fun i => by
    have h := hB2 i
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i (2 * ((pK : ℝ) + (sW : ℝ)))
    nlinarith [sq_nonneg (d i), hw.le]
  have hsummable : Summable (fun i => d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) := by
    refine Summable.of_norm_bounded
      (g := fun i => CK * (Real.sqrt (B2 i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))
      (Summable.mul_left CK
        (summable_sqrt_mul_weight_neg (I := I) (M := M) g B2 hB2_sum hB2_nn hsW_gt))
      (fun i => ?_)
    have hd_le := abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pK : ℝ) + (sW : ℝ))
      (hB2 i)
    have hK_le := hCK i
    have hcollapse : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
        * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ)
        = tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
      unfold tensorSobolevWeight
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pK,
        ← Real.rpow_add (hbase_pos i)]
      congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |d i| * |tensorChartComponentRaw (I := I) (M := M) g 0 2
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x|
        ≤ (Real.sqrt (B2 i) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))) *
          (CK * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pK) := by
          refine mul_le_mul hd_le hK_le (abs_nonneg _) ?_
          exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
      _ = CK * (Real.sqrt (B2 i) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
              * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ))) := by ring
      _ = CK * (Real.sqrt (B2 i) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [hcollapse]
  have htend_tsum : Filter.Tendsto (fun n =>
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) Filter.atTop
      (nhds (∑' i, d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x)) :=
    hsummable.hasSum.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  have htend_lhs : Filter.Tendsto (fun n =>
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) Filter.atTop
      (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x)) :=
    htend_raw.congr hpartial
  exact tendsto_nhds_unique htend_lhs htend_tsum

set_option maxHeartbeats 1600000 in
private theorem spectralPathFO_rawCompOnE_euclidean_contDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => rawCompOnE (I := I) (M := M) g (T_rep q.1) α Jdx q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀
  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  have hmajorant := eigenRawIncrementMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (I := I) (M := M) (T := T) g hT kk φ hφ_smooth hmodemass α Jdx
    hBc_compact huniqBc hBc_sub
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun n => if hn : n ≤ kk then Classical.choose (hmajorant n hn) else 0 with hv_def
  have hv_spec : ∀ (n : ℕ) (hn : n ≤ kk), Summable (v n) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ n (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v n i := by
    intro n hn
    have hspec := Classical.choose_spec (hmajorant n hn)
    have hveq : v n = Classical.choose (hmajorant n hn) := by
      rw [hv_def]; exact dif_pos hn
    rw [hveq]
    exact hspec
  have htsum_Bc : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i q)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    have h := DifferentialGeometry.Analysis.contDiffOn_tsum (v := v) (x₀ := ((0 : ℝ), y₀))
      (N := (kk : ℕ∞))
      huniq hconv
      (fun i => ((eigenRawIncrementMode_contDiffOn_ofOrder (I := I) (M := M) (T := T)
        g kk φ hφ_smooth α Jdx i).mono
          (Set.prod_mono (le_refl _) hBc_sub)).of_le (by exact_mod_cast le_rfl))
      (fun n hn => (hv_spec n (by exact_mod_cast hn)).1)
      (fun n i q hq hn => (hv_spec n (by exact_mod_cast hn)).2 i q hq)
      ⟨Set.left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
    exact h.of_le (by exact_mod_cast le_rfl)
  have htsum : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i q)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  intro q hq
  have hq_symm_src : (extChartAt I α).symm q.2 ∈ (chartAt H α).source := by
    have hqt : q.2 ∈ (extChartAt I α).target := interior_subset (hB_sub hq.2)
    have := (extChartAt I α).map_target hqt
    rwa [extChartAt_source (I := I)] at this
  exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
    g (T_rep q.1) (fun i => φ i q.1) (hcoeff q.1 hq.1)
    (fun σ hσ => by
      obtain ⟨B', hB'_sum, hB'_le⟩ := hmodemass 0 (Nat.zero_le kk) σ hσ
      refine ⟨B', hB'_sum, fun i => ?_⟩
      have h := hB'_le i q.1 hq.1
      rwa [iteratedDeriv_zero] at h)
    α Jdx hq_symm_src

set_option maxHeartbeats 1600000 in
private theorem spectralPathFO_rawChartComponent_jointContMDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (kk : ℕ)
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α ![] Jdx p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E => rawCompOnE (I := I) (M := M) g (T_rep q.1) α Jdx q.2 with hG_def
  have hGEuclid : ContDiffOn ℝ (kk : ℕ) G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    spectralPathFO_rawCompOnE_euclidean_contDiffOn_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Jdx
  set f : M × ℝ → ℝ × E := fun p : M × ℝ => (p.2, extChartAt I α p.1) with hf_def
  have hf_smooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) (kk : ℕ) f
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_snd ?_
    refine ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)).of_le (by exact_mod_cast le_top)
  have hmaps : Set.MapsTo f ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨ht, ?_⟩
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx'
  have heq : Set.EqOn
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α ![] Jdx p.1)
      (G ∘ f)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    rintro ⟨x, t⟩ ⟨hx, _⟩
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    simp only [Function.comp, hG_def, hf_def]
    have hraw : rawCompOnE (I := I) (M := M) g (T_rep t) α Jdx (extChartAt I α x) =
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep t) α ![] Jdx
          ((extChartAt I α).symm (extChartAt I α x)) := rfl
    rw [hraw, (extChartAt I α).left_inv hx']
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ (kk : ℕ) G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

private theorem spectralPathFO_rawChartComponent_fibre_contDiffWithinAt_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContDiffWithinAt ℝ (kk : ℕ)
      (fun s : ℝ => tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![] Jdx x)
      (Set.Icc (0 : ℝ) T) t := by
  have hCR := spectralPathFO_rawChartComponent_jointContMDiffOn_local (I := I) (M := M)
    g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Jdx
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (kk : ℕ) (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hx, hu⟩
  have hcomp := hCR.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp t ht

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem spectralPathFO_section_jointContMDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((T_rep p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hSum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
          tensorChartBasisElement (E := E) 0 2 Q.1 Q.2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_finset_sum (fun Q _ => ?_)
    have hQ1 : Q.1 = (![] : Fin 0 → Fin (Module.finrank ℝ E)) := funext fun i0 => i0.elim0
    have hraw := spectralPathFO_rawChartComponent_jointContMDiffOn_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Q.2
    rw [hQ1]
    exact hraw.smul contMDiffOn_const
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1, (T_rep p₀.2).toSection p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfibeq : ∀ p : M × ℝ, p.1 ∈ (chartAt H α).source →
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        ∑ Q : CompIdx E 0 2,
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
            tensorChartBasisElement (E := E) 0 2 Q.1 Q.2 := by
    intro p hpx
    have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hpx
    have h1 : ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt
          ℝ p.1 ((T_rep p.2).toSection p.1) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    rw [h1, toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 (T_rep p.2) α hpx,
      map_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [map_smul]
    congr 1
    have hbs : chartBasisFiberSection (I := I) (M := M) 0 2 α Q p.1 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).symmL ℝ p.1
          (tensorChartBasisElement (E := E) 0 2 Q.1 Q.2) := rfl
    rw [hbs]
    exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hpbase _
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1, (T_rep p.2).toSection p.1⟩).2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
    refine (hSum p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact hfibeq p hp.1
    · exact hfibeq p₀ hx₀src
  exact ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ((kk : ℕ) : WithTop ℕ∞))
    (f := fun p : M × ℝ => (⟨p.1, (T_rep p.2).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem spectralPathFO_toFun_timeJet_eq_of_coeff_jets_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (j : ℕ) (hj : j ≤ kk) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (Rt : SmoothCcTensor g 0 2)
    (hRt : ∀ i, tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) Rt) i = iteratedDeriv j (φ i) t)
    (x : M) :
    Rt.toFun x =
      iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t := by
  classical
  set α : M := x with hα
  have hx : x ∈ (chartAt H α).source := mem_chart_source H x
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hjm : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv j (φ i) t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hB1, hB2⟩ := hmodemass j hj σ hσ
    exact ⟨B, hB1, fun i => hB2 i t ht⟩
  set w : CompIdx E 0 2 → Tensor0SBundle.TensorRSModel 0 2 ℝ E := fun Q =>
    Tensor0SBundle.TensorRSSpace.toModel
      (chartBasisFiberSection (I := I) (M := M) 0 2 α Q x) with hw_def
  set A : (CompIdx E 0 2 → ℝ) →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    ∑ Q : CompIdx E 0 2, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : CompIdx E 0 2 => ℝ) Q).smulRight (w Q) with hA_def
  have hAapply : ∀ c : CompIdx E 0 2 → ℝ, A c = ∑ Q : CompIdx E 0 2, c Q • w Q := by
    intro c
    rw [hA_def, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun Q _ => by
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply])
  have hexp : ∀ Z : SmoothCcTensor g 0 2,
      Z.toFun x = A (fun Q =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 Z α Q.1 Q.2 x) := by
    intro Z
    rw [hAapply]
    have h1 : Z.toFun x = Tensor0SBundle.TensorRSSpace.toModel (Z.toSection x) := rfl
    have h3 : ∀ v : Tensor0SBundle.TensorRSSpace 0 2 I x,
        Tensor0SBundle.TensorRSSpace.toModel v
          = Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) (I := I) 0 2 x v := fun v => rfl
    rw [h1, toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 Z α hx,
      h3, map_sum]
    exact Finset.sum_congr rfl (fun Q _ => by rw [map_smul, ← h3, hw_def])
  set rawγ : ℝ → CompIdx E 0 2 → ℝ := fun s Q =>
    tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x with hrawγ_def
  have hγpath : (fun s => (T_rep s).toFun x) = fun s => A (rawγ s) :=
    funext fun s => hexp (T_rep s)
  have hQ1 : ∀ Q : CompIdx E 0 2, Q.1 = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
    fun Q => funext fun i0 => i0.elim0
  have hraws : ∀ Q : CompIdx E 0 2, ContDiffWithinAt ℝ (j : ℕ)
      (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t := by
    intro Q
    have h := spectralPathFO_rawChartComponent_fibre_contDiffWithinAt_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Q.2 hx ht
    have hfun : (fun s => rawγ s Q) =
        (fun s : ℝ => tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![]
          Q.2 x) := by
      funext s
      show tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x = _
      rw [hQ1 Q]
    rw [hfun]
    exact h.of_le (by exact_mod_cast hj)
  have hγvec : ContDiffWithinAt ℝ (j : ℕ) rawγ (Set.Icc (0 : ℝ) T) t :=
    contDiffWithinAt_pi.2 hraws
  have hstep1 : iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t
      = A (iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t) := by
    rw [hγpath]
    exact clm_comm_iteratedDerivWithin_finiteOrder A rawγ hT ht j hγvec
  have hstep2 : iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t
      = fun Q => iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t := by
    funext Q
    have hproj := clm_comm_iteratedDerivWithin_finiteOrder
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : CompIdx E 0 2 => ℝ) Q)
      rawγ hT ht j hγvec
    simp only [ContinuousLinearMap.proj_apply] at hproj
    exact hproj.symm
  have hstep3 : ∀ Q : CompIdx E 0 2,
      iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t
        = ∑' i, iteratedDeriv j (φ i) t *
            tensorChartComponentRaw (I := I) (M := M) g 0 2
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x := by
    intro Q
    obtain ⟨CK, pK, hCK_nn, hCK⟩ :=
      exists_rawComponentRaw_eigen_pointwise_le_lambda_pow (I := I) (M := M) g α Q.2 hx
    set K : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ := fun i =>
      tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x with hK_def
    set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
    have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
      rw [hsW_def]; push_cast; linarith
    set σ0 : ℝ := 2 * ((pK : ℝ) + (sW : ℝ)) with hσ0_def
    have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
    have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    have hcollapse : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
          * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ)
          = tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
      intro i
      unfold tensorSobolevWeight
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pK,
        ← Real.rpow_add (hbase_pos i)]
      congr 1; ring
    have htimeC : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
        a ≤ kk → Summable Cm ∧
          ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ0 *
              (iteratedDeriv a (φ i) s) ^ 2 ≤ Cm i := by
      intro a
      by_cases ha : a ≤ kk
      · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
        exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨fun _ => 0, fun h => absurd h ha⟩
    choose Cmf hCmf using htimeC
    have hCm_nn : ∀ (a : ℕ), a ≤ kk →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
      intro a ha i
      have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
      have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
      nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
    set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ := fun a i =>
      if a ≤ kk then CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) else 0 with hv_def
    have hveq : ∀ (a : ℕ), a ≤ kk → v a = fun i => CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      intro a ha
      funext i
      show (if a ≤ kk then CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) else 0) = _
      rw [if_pos ha]
    have hv_sum : ∀ a : ℕ, a ≤ kk → Summable (v a) := by
      intro a ha
      rw [hveq a ha]
      exact Summable.mul_left CK (summable_sqrt_mul_weight_neg (I := I) (M := M) g
        (Cmf a) (hCmf a ha).1 (hCm_nn a ha) hsW_gt)
    have hterm_bound : ∀ (a : ℕ), a ≤ kk →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ s ∈ Set.Icc (0 : ℝ) T,
        ‖iteratedFDerivWithin ℝ a (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) s‖
          ≤ v a i := by
      intro a ha i s hs
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_mul_const_field, Real.norm_eq_abs, abs_mul]
      have hwithin : iteratedDerivWithin a (φ i) (Set.Icc (0 : ℝ) T) s
          = iteratedDeriv a (φ i) s :=
        iteratedDerivWithin_eq_iteratedDeriv hUD
          ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast ha)) hs
      rw [hwithin]
      have hmass_s : tensorSobolevWeight (I := I) (M := M) i
          (2 * ((pK : ℝ) + (sW : ℝ))) * (iteratedDeriv a (φ i) s) ^ 2 ≤ Cmf a i := by
        have h := (hCmf a ha).2 i s hs
        rwa [hσ0_def] at h
      have hφ_le := abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i
        ((pK : ℝ) + (sW : ℝ)) hmass_s
      have hK_le := hCK i
      have hva : v a i = CK * (Real.sqrt (Cmf a i) *
          tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
        rw [hveq a ha]
      rw [hva, ← hcollapse i]
      calc |iteratedDeriv a (φ i) s| * |K i|
          ≤ (Real.sqrt (Cmf a i) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))) *
            (CK * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pK) := by
            refine mul_le_mul hφ_le ?_ (abs_nonneg _) ?_
            · rw [hK_def]; exact hK_le
            · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
        _ = CK * (Real.sqrt (Cmf a i) *
              ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
                * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ))) := by ring
    have hfterms : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        ContDiffOn ℝ ((kk : ℕ∞)) (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) :=
      fun i => (((hφ_smooth i).mul contDiff_const).contDiffOn).of_le
        (by exact_mod_cast le_rfl)
    have hEq : ∀ s ∈ Set.Icc (0 : ℝ) T, rawγ s Q = ∑' i, φ i s * K i := by
      intro s hs
      have hfun : rawγ s Q =
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![] Q.2 x := by
        show tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x = _
        rw [hQ1 Q]
      rw [hfun]
      exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
        g (T_rep s) (fun i => φ i s) (hcoeff s hs)
        (fun σ hσ => by
          obtain ⟨B', hB'_sum, hB'_le⟩ := hmodemass 0 (Nat.zero_le kk) σ hσ
          refine ⟨B', hB'_sum, fun i => ?_⟩
          have h := hB'_le i s hs
          rwa [iteratedDeriv_zero] at h)
        α Q.2 hx
    rw [iteratedDerivWithin_congr hEq ht]
    have hFD := DifferentialGeometry.Analysis.iteratedFDerivWithin_tsum
      (f := fun (i : TensorEigenIdx (I := I) (M := M) g 0 2) (u : ℝ) => φ i u * K i)
      (v := v) (s := Set.Icc (0 : ℝ) T) (N := (kk : ℕ∞))
      hUD (convex_Icc 0 T) hfterms
      (fun a ha => hv_sum a (by exact_mod_cast ha))
      (fun a i s hs ha => hterm_bound a (by exact_mod_cast ha) i s hs)
      (Set.left_mem_Icc.mpr hT.le) (k := j) (by exact_mod_cast hj) ht
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hFD]
    have hsumFD : Summable (fun i => iteratedFDerivWithin ℝ j
        (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) t) :=
      Summable.of_norm_bounded (hv_sum j hj) (fun i => hterm_bound j hj i t ht)
    have happly := ContinuousLinearMap.map_tsum
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℝ (fun _ => (1 : ℝ))) hsumFD
    have happly' : (∑' i, iteratedFDerivWithin ℝ j (fun u : ℝ => φ i u * K i)
        (Set.Icc (0 : ℝ) T) t) (fun _ => (1 : ℝ))
        = ∑' i, (iteratedFDerivWithin ℝ j (fun u : ℝ => φ i u * K i)
          (Set.Icc (0 : ℝ) T) t) (fun _ => (1 : ℝ)) := happly
    rw [happly']
    refine tsum_congr (fun i => ?_)
    rw [← iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedDerivWithin_mul_const_field,
      iteratedDerivWithin_eq_iteratedDeriv hUD
        ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast hj)) ht]
  have hRt_exp : ∀ Q : CompIdx E 0 2,
      tensorChartComponentRaw (I := I) (M := M) g 0 2 Rt α Q.1 Q.2 x
        = ∑' i, iteratedDeriv j (φ i) t *
            tensorChartComponentRaw (I := I) (M := M) g 0 2
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x := by
    intro Q
    rw [hQ1 Q]
    exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
      g Rt (fun i => iteratedDeriv j (φ i) t) hRt hjm α Q.2 hx
  calc Rt.toFun x
      = A (fun Q => tensorChartComponentRaw (I := I) (M := M) g 0 2 Rt α Q.1 Q.2 x) :=
        hexp Rt
    _ = A (fun Q => iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t) := by
        congr 1
        funext Q
        rw [hRt_exp Q, ← hstep3 Q]
    _ = A (iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t) := by
        congr 1
        exact hstep2.symm
    _ = iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t :=
        hstep1.symm

end FiniteOrderSpectralPathEngine

set_option linter.unusedVariables false in
private theorem deTurckRHSReconSectionFO_pathCoeff_timeContDiff_spectralJetMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) :=
  sorry

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_path_timeJet_mixed_regularity
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((k : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∧
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ j : ℕ, j ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
        (Rjet j t).toFun x = iteratedDerivWithin j
          (fun s => (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
          (Set.Icc (0 : ℝ) T) t) ∧
      (∀ j : ℕ, j ≤ k → ∀ κ : ℕ,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
          ((0 : ℕ) : WithTop ℕ∞)
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
            ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j p.2)).toSection p.1))
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) := by
  classical
  obtain ⟨hcoeffCk, hjetmass⟩ :=
    deTurckRHSReconSectionFO_pathCoeff_timeContDiff_spectralJetMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hext : ∀ i, ∃ G : ℝ → ℝ, ContDiff ℝ (k : ℕ) G ∧
      Set.EqOn G (fun t => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T) :=
    fun i => DifferentialGeometry.Analysis.exists_contDiff_extend_of_contDiffOn_Icc hT k _
      (hcoeffCk i)
  choose chat hchat_smooth hchat_eq using hext
  have hjets_global : ∀ i (j : ℕ), j ≤ k → ∀ t ∈ Set.Icc (0 : ℝ) T,
      iteratedDeriv j (chat i) t =
        iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
          (Set.Icc (0 : ℝ) T) t := by
    intro i j hj t ht
    rw [← iteratedDerivWithin_eq_iteratedDeriv hUD
      ((hchat_smooth i).contDiffAt.of_le (by exact_mod_cast hj)) ht]
    exact iteratedDerivWithin_congr (hchat_eq i) ht
  have hRcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i =
          chat i t :=
    fun t ht i => (hchat_eq i ht).symm
  have hRmass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (chat i) t) ^ 2 ≤ B i := by
    intro j hj σ hσ
    obtain ⟨B, hB1, hB2⟩ := hjetmass j hj σ hσ
    refine ⟨B, hB1, fun i t ht => ?_⟩
    rw [hjets_global i j hj t ht]
    exact hB2 i t ht
  have h1 := spectralPathFO_section_jointContMDiffOn_local (I := I) (M := M) g₀ hT k
    (fun s => deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
    chat hchat_smooth hRcoeff hRmass
  have hRjet_ex : ∀ (j : ℕ) (t : ℝ), ∃ S : SmoothCcTensor g₀ 0 2,
      j ≤ k → t ∈ Set.Icc (0 : ℝ) T →
        ∀ i, tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          iteratedDeriv j (chat i) t := by
    intro j t
    by_cases h : j ≤ k ∧ t ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨hj, ht⟩ := h
      have hm : ∀ σ : ℝ, 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j (chat i) t) ^ 2 ≤ B i := by
        intro σ hσ
        obtain ⟨B, hB1, hB2⟩ := hRmass j hj σ hσ
        exact ⟨B, hB1, fun i => hB2 i t ht⟩
      obtain ⟨S, hS⟩ := exists_smoothCcTensor_of_allOrder_spectralMass_local (I := I) (M := M)
        g₀ (fun i => iteratedDeriv j (chat i) t) hm
      exact ⟨S, fun _ _ => hS⟩
    · exact ⟨0, fun hj ht => absurd ⟨hj, ht⟩ h⟩
  choose Rjet hRjet using hRjet_ex
  refine ⟨h1, Rjet, ?_, ?_⟩
  · intro j hj t ht x
    exact spectralPathFO_toFun_timeJet_eq_of_coeff_jets_local (I := I) (M := M) g₀ hT k
      (fun s => deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      chat hchat_smooth hRcoeff hRmass j hj ht (Rjet j t) (hRjet j t hj ht) x
  · intro j hj κ
    have hφκ_smooth : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        ContDiff ℝ ((0 : ℕ) : ℕ)
          (fun t => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
            iteratedDeriv j (chat i) t) := by
      intro i
      rw [show (((0 : ℕ) : ℕ) : WithTop ℕ∞) = (0 : WithTop ℕ∞) from rfl, contDiff_zero]
      exact continuous_const.mul
        (ContDiff.continuous_iteratedDeriv j (hchat_smooth i) (by exact_mod_cast hj))
    have hκcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t))) i =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
              iteratedDeriv j (chat i) t := by
      intro t ht i
      rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ hc
        (Rjet j t) i κ, hRjet j t hj ht i]
    have hκmass : ∀ (j' : ℕ), j' ≤ 0 → ∀ (σ : ℝ), 0 ≤ σ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j'
                  (fun u => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
                    iteratedDeriv j (chat i) u) t) ^ 2 ≤ B i := by
      intro j' hj' σ hσ
      have hj'0 : j' = 0 := Nat.le_zero.mp hj'
      subst hj'0
      obtain ⟨B, hB1, hB2⟩ := hRmass j hj (σ + ((2 * κ : ℕ) : ℝ)) (by positivity)
      refine ⟨B, hB1, fun i t ht => ?_⟩
      rw [iteratedDeriv_zero]
      have hwsplit : tensorSobolevWeight (I := I) (M := M) i σ *
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
            iteratedDeriv j (chat i) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ + ((2 * κ : ℕ) : ℝ)) *
            (iteratedDeriv j (chat i) t) ^ 2 := by
        rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ ((2 * κ : ℕ) : ℝ)]
        have hw2κ : tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ)
            = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ) ^ 2 := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast, mul_comm 2 κ, pow_mul]
        rw [hw2κ, mul_pow]
        ring
      rw [hwsplit]
      exact hB2 i t ht
    exact spectralPathFO_section_jointContMDiffOn_local (I := I) (M := M) g₀ hT 0
      (fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t))
      (fun i t => (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ κ *
        iteratedDeriv j (chat i) t)
      hφκ_smooth hκcoeff hκmass

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckRHSReconSectionFO_eigenPairing_jointCk_timeJet_realization
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((k : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
              (I := I) (M := M) g₀ 0 2 i).toFun p.1)
            ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) ∧
    (∀ j : ℕ, j ≤ k → ∃ Rjt : ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ∧
      (∀ κ : ℕ, ContinuousOn
        (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))‖ ^ 2)
        (Set.Icc (0 : ℝ) T))) := by
  classical
  obtain ⟨hjointP, Rjet, hRjet_eq, hRjet_lap⟩ :=
    deTurckRHSReconSectionFO_path_timeJet_mixed_regularity (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hkinf : ((k : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hpairing : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((k : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
              (I := I) (M := M) g₀ 0 2 i).toFun p.1)
            ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F p.2) hδ_lt (hδ p.2)).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
      (I := I) (M := M) g₀ 0 2 i
    have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
          ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
            (I := I) (M := M) g₀ 0 2 i).toSection p.1)) :=
      heigM.comp contMDiff_fst
    exact tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M) hkinf g₀
      (fun _ : ℝ => Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
        (I := I) (M := M) g₀ 0 2 i)
      (fun s : ℝ => deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
      ((heigP.contMDiffOn).of_le hkinf) hjointP
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  refine ⟨hpairing, ?_⟩
  intro j hjk
  have hjW : ((j : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hjk
  refine ⟨Rjet j, ?_, ?_⟩
  · intro i t ht
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig
    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl
    have hγfam : ∀ x : M, ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞)
        (fun s => (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
        (Set.Icc (0 : ℝ) T) t := fun x =>
      (smoothCcTensor_path_toFun_contDiffWithinAt (I := I) (M := M) g₀
        (fun s => deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
        hjointP x ht).of_le hjW
    have hfib : ∀ x : M,
        iteratedDerivWithin j
            (fun s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
              (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
              ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x))
            (Set.Icc (0 : ℝ) T) t
          = DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
              (eig.toFun x) ((Rjet j t).toFun x) := by
      intro x
      have hL := clm_comm_iteratedDerivWithin_finiteOrder
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x))
        (fun s => (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x)
        hT ht j (hγfam x)
      rw [hRjet_eq j hjk t ht x]
      exact hL
    have hLHSfun : (fun s : ℝ => tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
        = (fun s : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
            ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x) ∂μ) :=
      funext fun s => hcoeffInt (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))
    have hinter := iteratedDerivWithin_integral_param_Icc_finiteOrder μ hT j
      (fun x s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x)
        ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)).toFun x))
      ((hpairing i).of_le hjW) t ht
    rw [hLHSfun, hinter, hcoeffInt (Rjet j t)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hfib x))
  · intro κ
    set Sfam : ℝ → SmoothCcTensor g₀ 0 2 :=
      fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjet j t) with hSfam
    have hpair0 := tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M)
      (N := ((0 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_top) g₀ Sfam Sfam
      (hRjet_lap j hjk κ) (hRjet_lap j hjk κ)
    have hnormeq : (fun t : ℝ => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
        = fun t : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x) ∂μ := by
      funext t
      rw [SmoothCcTensor.norm_toL2,
        Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self]
      rfl
    have hcd := contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder μ hT 0
      (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x)) hpair0
    have hfinal : ContinuousOn
        (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
        (Set.Icc (0 : ℝ) T) := by
      rw [hnormeq]
      exact hcd.continuousOn
    exact hfinal

set_option linter.unusedVariables false in
private theorem deTurckRHSRecon_pathCoeff_finiteOrder_timeContDiff_withinMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) := by
  classical
  obtain ⟨hjoint, hjet⟩ :=
    deTurckRHSReconSectionFO_eigenPairing_jointCk_timeJet_realization (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  refine ⟨?_, ?_⟩
  · intro i
    set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
      with heig
    have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
          ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (S.toFun x) ∂μ := by
      intro S
      rw [tensorL2Coeff_eq_inner,
        Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
        ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
        ← SmoothCcTensor.toL2_apply
          (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
        SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
      rfl
    refine ContDiffOn.congr ?_
      (fun t _ => hcoeffInt (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t)))
    exact contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder μ hT k
      (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M)
        g₀ 0 2 x (eig.toFun x)
        ((deTurckRHSReconSectionFO (I := I) g₀ g_bg (F t) hδ_lt (hδ t)).toFun x))
      (hjoint i)
  · intro j hjk σ hσ
    obtain ⟨Rjt, hRjt_coeff, hRjt_norm⟩ := hjet j hjk
    set s : ℝ := (weylSobolevExp (E := E) : ℝ) + 1 with hs_def
    have hs : (weylSobolevExp (E := E) : ℝ) < s := by rw [hs_def]; linarith
    obtain ⟨κ, hκ⟩ := exists_nat_ge ((σ + s) / 2)
    have hκ2 : σ + s ≤ ((2 * κ : ℕ) : ℝ) := by
      push_cast
      have : (σ + s) / 2 ≤ (κ : ℝ) := hκ
      linarith
    obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT.le) (hRjt_norm κ)
    set C : ℝ := ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t₀))‖ ^ 2 with hC_def
    have hC : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) *
            (tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 ≤ C := by
      intro i t ht
      have hweq : tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2 =
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i) ^ 2 := by
        rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M)
            g₀ hc (Rjt t) i κ,
          mul_pow]
        congr 1
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast, mul_comm 2 κ, pow_mul, sq]
      rw [hweq]
      have hsummable := tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t)))
      have hle_tsum : (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i) ^ 2 ≤
          ∑' i' : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
            (tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t))) i') ^ 2 :=
        hsummable.le_tsum i (fun i' _ => sq_nonneg _)
      rw [tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 κ (Rjt t)))] at hle_tsum
      exact le_trans hle_tsum (ht₀_max ht)
    refine ⟨fun i => C * tensorSobolevWeight (I := I) (M := M) i (-s),
      (tensorEigen_summable_negpow (I := I) (M := M) g₀ s hs).mul_left C, ?_⟩
    intro i t ht
    rw [hRjt_coeff i t ht]
    have hnegnn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-s) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (-s)
    have hmono : tensorSobolevWeight (I := I) (M := M) i (σ + s) ≤
        tensorSobolevWeight (I := I) (M := M) i ((2 * κ : ℕ) : ℝ) :=
      tensorSobolevWeight_mono (I := I) (M := M) i hκ2
    have hadd : tensorSobolevWeight (I := I) (M := M) i σ =
        tensorSobolevWeight (I := I) (M := M) i (-s) *
          tensorSobolevWeight (I := I) (M := M) i (σ + s) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-s) (σ + s)]
      ring_nf
    calc tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-s) *
            (tensorSobolevWeight (I := I) (M := M) i (σ + s) *
              (tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjt t)) i) ^ 2) := by
          rw [hadd]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-s) * C := by
          refine mul_le_mul_of_nonneg_left ?_ hnegnn
          refine le_trans (mul_le_mul_of_nonneg_right hmono (sq_nonneg _)) ?_
          exact hC i t ht
      _ = C * tensorSobolevWeight (I := I) (M := M) i (-s) := by ring

set_option linter.unusedVariables false in
private theorem deTurckRemainder_pathCoeff_finiteOrder_timeContDiff_withinMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    (∀ i, ContDiffOn ℝ (k : ℕ)
        (fun t => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDerivWithin j
                (fun s => tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                    (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
                (Set.Icc (0 : ℝ) T) t) ^ 2 ≤ B i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  obtain ⟨hrecon_smooth, hrecon_mass⟩ :=
    deTurckRHSRecon_pathCoeff_finiteOrder_timeContDiff_withinMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  set reconRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hreconRaw_def
  set rawRaw : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (DifferentialGeometry.Integral.Connection.rawTensorConnLapSmooth
          (I := I) g₀ 0 2 (F s))) i with hrawRaw_def
  set cpath : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i with hcpath_def
  have hsplit : ∀ i s, cpath i s = reconRaw i s - rawRaw i s := by
    intro i s
    have hrem :
        deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
          = deTurckRHSReconSectionFO (I := I) g₀ g_bg (F s) hδ_lt (hδ s)
            - DifferentialGeometry.Integral.Connection.rawTensorConnLapSmooth
                (I := I) g₀ 0 2 (F s) := rfl
    simp only [hcpath_def, hreconRaw_def, hrawRaw_def]
    rw [hrem, SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  have hrecon_cd : ∀ i, ContDiffOn ℝ (k : ℕ) (reconRaw i) (Set.Icc (0 : ℝ) T) :=
    hrecon_smooth
  have hraw_eqOn : ∀ i, Set.EqOn (rawRaw i)
      (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) := by
    intro i s hs
    simp only [hrawRaw_def]
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F s) i,
      hcoeff s hs i]
  have hraw_cd : ∀ i, ContDiffOn ℝ (k : ℕ) (rawRaw i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContDiffOn.congr ?_ (hraw_eqOn i)
    exact contDiffOn_const.mul (hφ_smooth i).contDiffOn
  refine ⟨?_, ?_⟩
  · intro i
    exact ContDiffOn.congr ((hrecon_cd i).sub (hraw_cd i)) (fun t _ => hsplit i t)
  · intro j hjk σ hσ
    obtain ⟨Brecon, hBrecon_sum, hBrecon_le⟩ := hrecon_mass j hjk σ hσ
    obtain ⟨Braw, hBraw_sum, hBraw_le⟩ := hmodemass j hjk (σ + 2) (by linarith)
    refine ⟨fun i => 2 * Brecon i + 2 * Braw i,
      (hBrecon_sum.mul_left 2).add (hBraw_sum.mul_left 2), ?_⟩
    intro i t ht
    have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hcds : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (reconRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hrecon_cd i) t ht).of_le (by exact_mod_cast hjk)
    have hcdr : ContDiffWithinAt ℝ (j : WithTop ℕ∞) (rawRaw i) (Set.Icc (0 : ℝ) T) t :=
      ((hraw_cd i) t ht).of_le (by exact_mod_cast hjk)
    have hderivEq : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
        iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t -
          iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t := by
      have hcongr : iteratedDerivWithin j (cpath i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => reconRaw i s - rawRaw i s)
            (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (fun s _ => hsplit i s) ht
      rw [hcongr]
      have hsub := iteratedDerivWithin_sub (f := reconRaw i) (g := rawRaw i)
        (n := j) ht hUDO hcds hcdr
      simpa only [Pi.sub_apply] using hsub
    have hrawDerivEq : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
        -i.lambda * iteratedDeriv j (φ i) t := by
      have hcongr : iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t =
          iteratedDerivWithin j (fun s => -i.lambda * φ i s) (Set.Icc (0 : ℝ) T) t :=
        iteratedDerivWithin_congr (hraw_eqOn i) ht
      rw [hcongr,
        iteratedDerivWithin_const_mul ht hUDO (-i.lambda)
          (((hφ_smooth i).contDiffOn.of_le (by exact_mod_cast hjk)) t ht),
        iteratedDerivWithin_eq_iteratedDeriv hUDO
          ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast hjk)) ht]
    rw [hderivEq]
    set a : ℝ := iteratedDerivWithin j (reconRaw i) (Set.Icc (0 : ℝ) T) t with ha_def
    set b : ℝ := iteratedDerivWithin j (rawRaw i) (Set.Icc (0 : ℝ) T) t with hb_def
    have hwσ_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    have hsq : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
    have hweighted : tensorSobolevWeight (I := I) (M := M) i σ * (a - b) ^ 2 ≤
        2 * (tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hwσ_nn
      nlinarith [this]
    refine le_trans hweighted ?_
    have hterm_recon : tensorSobolevWeight (I := I) (M := M) i σ * a ^ 2 ≤ Brecon i :=
      hBrecon_le i t ht
    have hterm_raw : tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2 ≤ Braw i := by
      have hbsq : b ^ 2 = i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2 := by
        rw [hrawDerivEq]; ring
      have hlam_sq_le : i.lambda ^ 2 ≤ tensorSobolevWeight (I := I) (M := M) i 2 := by
        have hw2 : tensorSobolevWeight (I := I) (M := M) i 2 = (1 + i.lambda) ^ 2 := by
          unfold tensorSobolevWeight
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hw2]
        have hlam_nn : 0 ≤ i.lambda := tensor_lambda_nonneg (I := I) (M := M) i
        nlinarith [hlam_nn]
      have hmm : tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          (iteratedDeriv j (φ i) t) ^ 2 ≤ Braw i := hBraw_le i t ht
      have hsplitw : tensorSobolevWeight (I := I) (M := M) i (σ + 2) =
          tensorSobolevWeight (I := I) (M := M) i σ *
            tensorSobolevWeight (I := I) (M := M) i 2 :=
        tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2
      have hdjsq_nn : 0 ≤ (iteratedDeriv j (φ i) t) ^ 2 := sq_nonneg _
      calc tensorSobolevWeight (I := I) (M := M) i σ * b ^ 2
          = tensorSobolevWeight (I := I) (M := M) i σ *
              (i.lambda ^ 2 * (iteratedDeriv j (φ i) t) ^ 2) := by rw [hbsq]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i σ *
              (tensorSobolevWeight (I := I) (M := M) i 2 *
                (iteratedDeriv j (φ i) t) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hwσ_nn
            exact mul_le_mul_of_nonneg_right hlam_sq_le hdjsq_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
              (iteratedDeriv j (φ i) t) ^ 2 := by rw [hsplitw]; ring
        _ ≤ Braw i := hmm
    nlinarith [hterm_recon, hterm_raw]

set_option linter.unusedVariables false in
private theorem deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ (ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2),
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ψ i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i) ∧
      (∀ (j : ℕ), j ≤ k → ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        iteratedDeriv j (ψ i) t =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (q : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ K) := by
  classical
  obtain ⟨hcpath_smooth, hcpath_mass⟩ :=
    deTurckRemainder_pathCoeff_finiteOrder_timeContDiff_withinMass (I := I) (M := M)
      g₀ g_bg hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  have hext : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ∃ G : ℝ → ℝ, ContDiff ℝ (k : ℕ) G ∧
        Set.EqOn G
          (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)
          (Set.Icc (0 : ℝ) T) := fun i =>
    DifferentialGeometry.Analysis.exists_contDiff_extend_of_contDiffOn_Icc hT k _ (hcpath_smooth i)
  choose ψ hψ_cd hψ_eqOn using hext
  have hconstruct : ∀ (j : ℕ) (t : ℝ),
      ∃ S : SmoothCcTensor g₀ 0 2,
        (j ≤ k → t ∈ Set.Icc (0 : ℝ) T → ∀ i,
          tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
            iteratedDerivWithin j
              (fun s => tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
              (Set.Icc (0 : ℝ) T) t) := by
    intro j t
    by_cases hjk : j ≤ k
    · by_cases ht : t ∈ Set.Icc (0 : ℝ) T
      · obtain ⟨S, hS⟩ := exists_smoothCcTensor_of_allOrder_spectralMass_local (I := I) (M := M) g₀
          (fun i => iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t)
          (fun σ hσ => by
            obtain ⟨B, hBs, hBle⟩ := hcpath_mass j hjk σ hσ
            exact ⟨B, hBs, fun i => hBle i t ht⟩)
        exact ⟨S, fun _ _ i => hS i⟩
      · exact ⟨0, fun _ ht' => absurd ht' ht⟩
    · exact ⟨0, fun hjk' => absurd hjk' hjk⟩
  choose Rjet hRjet using hconstruct
  have hbridge : ∀ (j : ℕ), j ≤ k → ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      iteratedDeriv j (ψ i) t =
        iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
          (Set.Icc (0 : ℝ) T) t := by
    intro j hjk i t ht
    have hcongr := iteratedDerivWithin_congr (n := j) (hψ_eqOn i) ht
    have heq : iteratedDerivWithin j (ψ i) (Set.Icc (0 : ℝ) T) t = iteratedDeriv j (ψ i) t :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
        ((hψ_cd i).contDiffAt.of_le (by exact_mod_cast hjk)) ht
    rw [← heq, hcongr]
  refine ⟨ψ, Rjet, hψ_cd, ?_, ?_, ?_⟩
  · intro i t ht
    exact hψ_eqOn i ht
  · intro j hjk i t ht
    rw [hbridge j hjk i t ht]
    exact (hRjet j t hjk ht i).symm
  · intro j hjk q
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ q
    obtain ⟨B, hBs, hBle⟩ := hcpath_mass j hjk ((2 * q : ℕ) : ℝ) (by positivity)
    refine ⟨C * Real.sqrt (∑' i, B i),
      mul_nonneg hC_nn (Real.sqrt_nonneg _), fun t ht => ?_⟩
    have hptwise : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 * q : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).coeff i) ^ 2 ≤
          B i := by
      intro i
      have hco : (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).coeff i =
          iteratedDerivWithin j
            (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i)
            (Set.Icc (0 : ℝ) T) t := by
        rw [smoothCcToTensorHs_coeff]; exact hRjet j t hjk ht i
      rw [hco]; exact hBle i t ht
    have hnorm_le :
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)‖ ≤
          Real.sqrt (∑' i, B i) := by
      rw [tensorHs.norm_eq_sqrt_tsum (I := I) (M := M)
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t))]
      exact Real.sqrt_le_sqrt (Summable.tsum_le_tsum hptwise
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)).weighted_summable)
        hBs)
    have hqmem : q ∈ Finset.range (2 * q + 1) := Finset.mem_range.mpr (by omega)
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖
        ≤ ∑ j' ∈ Finset.range (2 * q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ :=
          Finset.single_le_sum
            (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖)
            (fun j' _ => norm_nonneg _) hqmem
      _ ≤ C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * q : ℕ) : ℝ) (Rjet j t)‖ :=
          hCle (Rjet j t)
      _ ≤ C * Real.sqrt (∑' i, B i) := mul_le_mul_of_nonneg_left hnorm_le hC_nn

set_option linter.unusedVariables false in
theorem deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (k : ℕ)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (σ : ℝ), 0 ≤ σ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a (F t) hδ_lt (hδ t)).coeff i = ψ i t) := by
  classical
  obtain ⟨ψ, Rjet, hψ_smooth, hψ_eq, hjet, hcovbnd⟩ :=
    deTurckRemainder_path_coeff_finiteOrder_timeJet_globalSection (I := I) (M := M)
      g₀ g_bg a ha_super hT k F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  refine ⟨ψ, hψ_smooth, ?_, ?_⟩
  · intro j hj σ hσ
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ,
        σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) ≤ (2 * k' : ℕ) := by
      obtain ⟨k', hk'⟩ := exists_nat_gt (σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1))
      exact ⟨k', by push_cast; linarith⟩
    set σ' : ℝ := ((2 * k' : ℕ) : ℝ) with hσ'_def
    have hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by rw [hσ'_def]; linarith
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ k'
    have hcovsum_bnd : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ≤ K := by
      have hbnds : ∀ q ∈ Finset.range (2 * k' + 1), ∃ Kq : ℝ, 0 ≤ Kq ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ Kq :=
        fun q _ => hcovbnd j hj q
      choose! Kq hKq_nn hKq using hbnds
      refine ⟨C * ∑ q ∈ Finset.range (2 * k' + 1), Kq q,
        mul_nonneg hC_nn (Finset.sum_nonneg (fun q hq => hKq_nn q hq)), ?_⟩
      intro t ht
      refine le_trans (hCle (Rjet j t)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hC_nn
      refine Finset.sum_le_sum (fun q hq => ?_)
      exact hKq q hq t ht
    obtain ⟨K, hK_nn, hKle⟩ := hcovsum_bnd
    refine ⟨fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2, ?_, ?_⟩
    · exact (tensorEigen_summable_negpow (I := I) (M := M) g₀ (σ' - σ) hσσ').mul_right (K ^ 2)
    · intro i t ht
      rw [hjet j hj i t ht]
      set u : ℝ := tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i with hu_def
      have hcoeff_eq : (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).coeff i = u := by
        rw [smoothCcToTensorHs_coeff]
      have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
      have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
          tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
            tensorSobolevWeight (I := I) (M := M) i σ' := by
        unfold tensorSobolevWeight
        rw [← Real.rpow_add hbase, show -(σ' - σ) + σ' = σ from by ring]
      have hterm_le : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤ K ^ 2 := by
        have hmass : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ^ 2 := by
          rw [tensorHs.norm_sq_eq_tsum]
          have hsummable :=
            (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable
          have hle := hsummable.le_tsum i (fun i' _ =>
            mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i' σ') (sq_nonneg _))
          rw [hcoeff_eq] at hle
          exact hle
        refine le_trans hmass ?_
        have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ := norm_nonneg _
        have := hKle t ht
        nlinarith [this, hnn, hK_nn]
      calc tensorSobolevWeight (I := I) (M := M) i σ * u ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
              (tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2) := by rw [hsplit]; ring
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2 :=
            mul_le_mul_of_nonneg_left hterm_le
              (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  · intro t ht i
    rw [deTurckSmoothN_coeff]
    exact (hψ_eq i t ht).symm

set_option linter.unusedVariables false in
theorem deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (k : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i) := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  have hmass0 : ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have := hBle i t ht
    rwa [iteratedDeriv_zero] at this
  have hsum_pt : ∀ t, t ∈ Set.Icc (0 : ℝ) d₂ →
      ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2) := by
    intro t ht σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => hBle i t ht) hBs
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  set ct : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => φ i t with hct_def
  have hreconstruct : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = φ i t := by
    intro t ht
    obtain ⟨B0, hB0s, hB0le⟩ := hmass0 0 le_rfl
    set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
      tensorHs_of_spectralMass_majorant (I := I) (M := M) (ct t) B0 hB0s
        (fun i => by
          have := hB0le i t ht
          simpa [hct_def] using this) with hv0_def
    set u : TensorL2 0 2 g₀ :=
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
    have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = φ i t := by
      intro i
      rw [hu_def, tensorHsToL2_tensorL2Coeff]
      simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff, hct_def]
    have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
      intro σ hσ
      refine (hsum_pt t ht σ hσ).congr (fun i => ?_)
      rw [hu_coeff i]
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
      allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
    refine ⟨S, fun i => ?_⟩
    have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
      rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
          = (S : TensorL2 0 2 g₀) from rfl, hS]
    rw [hSL2, hu_coeff i]
  choose! S₀ hS₀ using hreconstruct
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) d₂ then S₀ t else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    simp only [hF_def, ht, if_pos]
    exact hS₀ t ht i
  have hF_smoothCc_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) d₂) := by
    set σ : ℝ := (a : ℝ) + 2 with hσ_def
    set σ' : ℝ := σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) with hσ'_def
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0 σ' (by
      rw [hσ'_def, hσ_def]; positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀
      (σ := σ) (σ' := σ') ?_ (s := Set.Icc (0 : ℝ) d₂)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ
      hF_smoothCc_coeff (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have : σ' - σ = ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by rw [hσ'_def]; ring
    rw [this]; linarith
  have hball_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (w t).coeff i = φ i t := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      exact hw i
    have hae_mem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        t ∈ Set.Icc (0 : ℝ) d₂ := MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hw_ball, hae_all, hae_mem] with t hwball_t htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) = w t := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [hF_smoothCc_coeff t htmem i, ← htall i]
    rw [heq]; exact hwball_t
  have hcont_norm : ContinuousOn
      (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖)
      (Set.Icc (0 : ℝ) d₂) := continuous_norm.comp_continuousOn hfield_cont
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_le : ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) d₂)),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ≤ R₀ := hball_ae
    have hg_cont : ContinuousOn
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀)
        (Set.Icc (0 : ℝ) d₂) := hcont_norm.inf continuousOn_const
    have hfg : (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) d₂)]
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀) := by
      filter_upwards [hae_le] with s hs
      exact (min_eq_left hs).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hd₂_pos) hfg hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ⊓ R₀ := heq ht
    rw [hmin]; exact inf_le_right
  obtain ⟨δ, hδ_lt, hδ_all⟩ :
      ∃ δ : ℝ, δ < 1 ∧ ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (F t)) δ := by
    obtain ⟨hp_pos, hp_lt, hp_ball⟩ := Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)
    have hsmoothZero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h0 : (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2) :=
        (zero_smul ℝ _).symm
      rw [h0, smoothCcToTensorHs_smul, zero_smul]
    refine ⟨(Classical.choose (deTurckSobolevNHa2_exists_of_super
      (I := I) (M := M) g₀ a ha_super)).2,
      lt_of_le_of_lt hp_lt (by norm_num : (1 : ℝ) / 3 < 1), fun t => ?_⟩
    by_cases ht : t ∈ Set.Icc (0 : ℝ) d₂
    · exact hp_ball (F t) (hball_pt t ht)
    · have hF0 : F t = 0 := by simp only [hF_def, ht, if_neg, not_false_iff]
      refine hp_ball (F t) ?_
      rw [hF0, hsmoothZero, norm_zero]
      exact hp_pos.le
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hd₂_pos k F hδ_lt hδ_all φ hφ_smooth
      hF_coeff hφ_mass
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact hw j
  have hae_mem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      t ∈ Set.Icc (0 : ℝ) d₂ := MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hae_all, hae_mem] with t htall htmem
  have hwF : w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, ← hF_smoothCc_coeff t htmem j]
  rw [hwF,
    deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super
      (F t) hδ_lt (hδ_all t) (by
        have hle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ :=
          hball_pt t htmem
        have hpf : (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1 = R₀ := rfl
        rw [hpf]; exact hle)]
  exact hψ_coeff t htmem i

set_option linter.unusedVariables false in
theorem deTurckForcing_finiteOrderSmoothDriver
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
        (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
        (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
              tensorSobolevWeight (I := I) (M := M) i τ *
                  (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
        (∀ i, (fun t => (gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hs_cont, hs_mass, hball, hcoeff_id⟩ :=
    deTurckForcing_solCoeff_continuous_smallTimeBase (I := I) (M := M)
      g₀ a ha_super hT hT1 gforce hspatial
  choose c hc_cont hc_ae using hs_cont
  have hae_d : ∀ i, c i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le) (hc_ae i)
  have hcont_pmc : ∀ i, ContinuousOn
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    (continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le).mono (Set.Icc_subset_Icc le_rfl hd_le)
  have heqOn_d : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (ne_of_lt hd_pos) (hae_d i) (hc_cont i).continuousOn (hcont_pmc i)
  refine ⟨d, hd_pos, hd_le, ?_⟩
  have hsub : Set.Icc (0 : ℝ) d ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hd_le
  have hforce_coeff : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  have hgforce_tmc : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  intro k
  induction k with
  | zero =>
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball 0
        c
        (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
        (fun j hj τ hτ => by
          obtain rfl := Nat.le_zero.mp hj
          obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
          refine ⟨B, hBs, fun i t ht => ?_⟩
          rw [iteratedDeriv_zero, heqOn_d i ht]
          exact hBle i t ht)
        (fun i => (hcoeff_id i).trans (hae_d i).symm)
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g₀ hd_pos.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (fk i) :=
        (hgforce_tmc i).symm.trans (hfk_ae i)
      have hbridge : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
        exact perModeConv_timeL2_congr (T := d) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hfk_tmc ht
      exact (hcoeff_id i).trans hbridge
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball (k + 1)
        (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
        hφ_cont hφ_mass hw_coeff
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
