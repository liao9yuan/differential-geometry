import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

theorem galerkinForcing_eq_galerkinCoordEmbed
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2) =
      galerkinCoordEmbed (I := I) (M := M) g₀ a (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1)) := by
  apply tensorHs.ext
  funext i
  rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · rw [if_pos hi, dif_pos hi]
    rfl
  · rw [if_neg hi, dif_neg hi]

theorem continuousOn_galerkinForcing_field
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))
      (Set.Icc (0 : ℝ) T) := by
  have hcoord : ContinuousOn
      (fun t => (EuclideanSpace.equiv
          {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
        (fun j => U N t j.1)) (Set.Icc (0 : ℝ) T) := by
    apply (EuclideanSpace.equiv
      {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm.continuous.comp_continuousOn
    refine continuousOn_pi.2 (fun j => hUcont j.1 j.2)
  have hcomp : ContinuousOn
      (fun t => galerkinCoordEmbed (I := I) (M := M) g₀ a
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv
            {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1))) (Set.Icc (0 : ℝ) T) :=
    (galerkinCoordEmbed (I := I) (M := M) g₀ a
      (eigenIdxFinset (I := I) (M := M) g₀ N)).continuous.comp_continuousOn hcoord
  refine hcomp.congr (fun t _ => ?_)
  rw [galerkinForcing_eq_galerkinCoordEmbed]

theorem continuousOn_galerkinForcing
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N hUcont
    have hcoeff : ContinuousOn
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))))
          (Set.Icc (0 : ℝ) T) :=
        (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.comp_continuousOn hN_cont
      simpa only [tensorHsCoeffL_apply] using hcoeff_cont
    refine hcoeff.congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_pos hi]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_neg hi]

theorem galerkinPerMode_eq_perModeConv
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U N t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N hUcont i).restrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N x i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) = -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      simp only [NNReal.coe_mk, le_refl]
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => U N s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hUcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hUderiv s hs i hi
    have hforce_eq : fForce s = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -(lam) * U N s i + deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hUinit i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

theorem perModeConv_timeL2_sub (lam : ℝ) (f₁ f₂ : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    perModeConv lam (fun s => f₁ s) t - perModeConv lam (fun s => f₂ s) t =
      perModeConv lam (fun s => (f₁ - f₂) s) t := by
  have hcongr : perModeConv lam (fun s => (f₁ - f₂) s) t =
      perModeConv lam (fun s => f₁ s - f₂ s) t :=
    perModeConv_timeL2_congr lam
      (by filter_upwards [Lp.coeFn_sub f₁ f₂] with r hr using hr) ht
  rw [hcongr]
  unfold perModeConv
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_kernel_mul_timeL2 lam t f₁ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)
    (intervalIntegrable_kernel_mul_timeL2 lam t f₂ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem tendsto_perModeConv_of_tendsto_timeL2 (lam : ℝ) (hlam : 0 ≤ lam)
    {fseq : ℕ → timeL2 ℝ T} {flim : timeL2 ℝ T}
    (hconv : Tendsto fseq atTop (𝓝 flim))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => perModeConv lam (fun s => (fseq N) s) t) atTop
      (𝓝 (perModeConv lam (fun s => flim s) t)) := by
  rcases le_or_gt 0 T with hT0 | hT0
  · rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε hε
    rcases eq_or_lt_of_le hT0 with hT00 | hTpos
    · have htval : t = 0 := by
        obtain ⟨ht1, ht2⟩ := ht
        rw [← hT00] at ht2
        exact le_antisymm ht2 ht1
      refine ⟨0, fun N _ => ?_⟩
      rw [htval]
      simp only [perModeConv_zero_left, dist_self]
      exact hε
    · set δ : ℝ := ε / (Real.sqrt T + 1) with hδ_def
      have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
      have hδ_pos : 0 < δ := by
        rw [hδ_def]; positivity
      obtain ⟨Nε, hNε⟩ := hconv δ hδ_pos
      refine ⟨Nε, fun N hN => ?_⟩
      have hdist : dist (fseq N) flim < δ := hNε N hN
      have hsub_eq :
          perModeConv lam (fun s => (fseq N) s) t - perModeConv lam (fun s => flim s) t =
            perModeConv lam (fun s => (fseq N - flim) s) t :=
        perModeConv_timeL2_sub lam (fseq N) flim ht
      have hbound : |perModeConv lam (fun s => (fseq N - flim) s) t| ≤
          Real.sqrt T * ‖fseq N - flim‖ :=
        abs_perModeConv_timeL2_le lam hlam (fseq N - flim) ht
      have hnorm : ‖fseq N - flim‖ < δ := by
        rw [← dist_eq_norm]; exact hdist
      rw [Real.dist_eq, hsub_eq]
      calc |perModeConv lam (fun s => (fseq N - flim) s) t|
          ≤ Real.sqrt T * ‖fseq N - flim‖ := hbound
        _ ≤ Real.sqrt T * δ :=
            mul_le_mul_of_nonneg_left (le_of_lt hnorm) hsqrt_nn
        _ < ε := by
            have hden : (0 : ℝ) < Real.sqrt T + 1 := by positivity
            rw [hδ_def,
              show Real.sqrt T * (ε / (Real.sqrt T + 1))
                = (Real.sqrt T * ε) / (Real.sqrt T + 1) by ring,
              div_lt_iff₀ hden]
            nlinarith [hsqrt_nn, hε]
  · have htval : t = 0 := by
      obtain ⟨ht1, ht2⟩ := ht
      have : t ≤ 0 := le_trans ht2 (le_of_lt hT0)
      exact le_antisymm this ht1
    rw [htval]
    simp only [perModeConv_zero_left]
    exact tendsto_const_nhds

theorem unifIntegrable_of_uniform_norm_bound {α β : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [NormedAddCommGroup β] [IsFiniteMeasure μ]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) :
    UnifIntegrable f 2 μ := by
  refine unifIntegrable_of (by norm_num) (by norm_num) hf (fun ε hε => ?_)
  refine ⟨(max C 0).toNNReal + 1, fun n => ?_⟩
  have hzero : { x | (max C 0).toNNReal + 1 ≤ ‖f n x‖₊ }.indicator (f n) =ᵐ[μ] 0 := by
    filter_upwards [hC n] with x hx
    have hle : ‖f n x‖₊ < (max C 0).toNNReal + 1 := by
      have hxle : ‖f n x‖ ≤ (max C 0) := le_trans hx (le_max_left _ _)
      have : (‖f n x‖₊ : ℝ) ≤ (max C 0).toNNReal := by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]; exact hxle
      have hlt : (‖f n x‖₊ : ℝ) < ((max C 0).toNNReal : ℝ) + 1 := by linarith
      exact_mod_cast hlt
    rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_le]; exact hle)]
    rfl
  rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
  exact zero_le _

theorem tendsto_finiteEigenComboHs_of_coeff_tendsto_of_succWeighted_bound
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (W : tensorHs (I := I) (M := M) g 0 2 σ) (B : ℝ)
    (hbound : ∀ N, ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 ≤ B)
    (hcoeff : ∀ i, Tendsto
        (fun N => (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i)
        atTop (𝓝 (W.coeff i))) :
    Tendsto (fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ)
      atTop (𝓝 W) :=
  sorry

theorem perMode_aeTendsto_of_galerkinODE
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop
        (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) :=
  sorry

theorem galerkinSolField_aeTendsto_maxRegSolField_core
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) :
    ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))
        atTop
        (𝓝 (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) := by
  classical
  haveI hcount : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  have hpermode : ∀ i, ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) :=
    fun i => perMode_aeTendsto_of_galerkinODE (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 gforce hforce U hUinit hUcont hUderiv i
  have hpermode' : ∀ᵐ t ∂(timeMeasure T), ∀ i,
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) :=
    ae_all_iff.2 hpermode
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScale (I := I) (M := M) g₀ g_bg a ha_super (T := T) U hUinit
  obtain ⟨Bound, hBound⟩ :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U) (Fseq := deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB 3
  filter_upwards [hpermode', ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t ht_coeff ht_mem
  have ht_mem' : t ∈ Set.Icc (0 : ℝ) T := ht_mem
  refine tendsto_finiteEigenComboHs_of_coeff_tendsto_of_succWeighted_bound
    (I := I) (M := M) g₀ ((a : ℝ) + 2) (eigenIdxFinset (I := I) (M := M) g₀)
    (fun N => U N t)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
    Bound (fun N => ?_) ht_coeff
  have h := hBound N t ht_mem'
  unfold galerkinEnergy at h
  rw [show (a : ℝ) + ((3 : ℕ) : ℝ) = (a : ℝ) + 2 + 1 by push_cast; ring] at h
  exact h

theorem galerkinSolField_tendsto_maxRegSolField_timeL2
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) :
    Tendsto (fun N => TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
      atTop
      (𝓝 (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)) := by
  classical
  set L := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce with hL_def
  set f : ℕ → ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
    fun N t => finiteEigenComboHs (I := I) (M := M) g₀
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2) with hf_def
  have hf_meas : ∀ N, AEStronglyMeasurable (f N) (timeMeasure T) := by
    intro N
    simp only [hf_def]
    unfold timeMeasure
    exact (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N
      (hUcont N)).aestronglyMeasurable measurableSet_Icc
  have hf_coe : ∀ N, ⇑(TimeSobolev.ofContinuousOn
      (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
      =ᵐ[timeMeasure T] f N :=
    fun N => TimeSobolev.coeFn_ofContinuousOn _
  have hconv : ∀ᵐ t ∂(timeMeasure T), Tendsto (fun N => f N t) atTop (𝓝 (L t)) :=
    galerkinSolField_aeTendsto_maxRegSolField_core (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 gforce hforce U hUinit hUcont hUderiv
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScale (I := I) (M := M) g₀ g_bg a ha_super (T := T) U hUinit
  obtain ⟨Bound, hBound⟩ :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U) (Fseq := deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB 2
  have hC : ∀ N, ∀ᵐ t ∂(timeMeasure T), ‖f N t‖ ≤ Real.sqrt Bound := by
    intro N
    unfold timeMeasure
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun t ht => ?_))
    have hEbound : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + 2) t ≤ Bound := by
      have h := hBound N t ht
      rwa [show (a : ℝ) + ((2 : ℕ) : ℝ) = (a : ℝ) + 2 by norm_num] at h
    have hVnorm_sq : ‖f N t‖ ^ 2 = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + 2) t := by
      simp only [hf_def]
      rw [finiteEigenCombo_spectral_normSq]
      rfl
    have h1 : ‖f N t‖ ^ 2 ≤ Bound := by rw [hVnorm_sq]; exact hEbound
    calc ‖f N t‖ = Real.sqrt (‖f N t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt Bound := Real.sqrt_le_sqrt h1
  have hui : UnifIntegrable f 2 (timeMeasure T) :=
    unifIntegrable_of_uniform_norm_bound hf_meas hC
  have hL_memLp : MemLp (⇑L) 2 (timeMeasure T) := Lp.memLp L
  have heLp : Tendsto (fun N => eLpNorm (f N - ⇑L) 2 (timeMeasure T)) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hf_meas hL_memLp hui hconv
  have heLp' : Tendsto (fun N => eLpNorm
      (⇑(TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))) - ⇑L)
      2 (timeMeasure T)) atTop (𝓝 0) := by
    refine heLp.congr (fun N => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hf_coe N] with t ht
    simp only [Pi.sub_apply, ht]
  have hL_eq : L = hL_memLp.toLp (⇑L) := Lp.ext (hL_memLp.coeFn_toLp).symm
  rw [hL_eq]
  exact Lp.tendsto_Lp_of_tendsto_eLpNorm (⇑L) hL_memLp heLp'

theorem deTurckGalerkinForcing_field_tendsto_force_timeL2
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (hcontField : ∀ N, ContinuousOn
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N t) ((a : ℝ) + 2))) (Set.Icc (0 : ℝ) T)) :
    Tendsto (fun N => TimeSobolev.ofContinuousOn (hcontField N)) atTop (𝓝 gforce) := by
  classical
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hsol := galerkinSolField_tendsto_maxRegSolField_timeL2 (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 gforce hforce U hUinit hUcont hUderiv
  have hcomp := ((nemytskii_lipschitzWith (I := I) (M := M) hK).continuous.tendsto
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)).comp hsol
  have hB : gforce = nemytskii (I := I) (M := M) hK
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) := by
    refine Lp.ext ?_
    have hnem := nemytskii_coeFn (I := I) (M := M) hK
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    filter_upwards [hforce, hnem] with t htf htn
    rw [htf, htn]
  have hA : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
      nemytskii (I := I) (M := M) hK
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))) := by
    intro N
    refine Lp.ext ?_
    have h1 := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
    have h2 := nemytskii_coeFn (I := I) (M := M) hK
      (TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
    have h3 := TimeSobolev.coeFn_ofContinuousOn
      (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
    filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
    rw [ht1, ht2, ht3]
  rw [hB]
  exact hcomp.congr (fun N => (hA N).symm)

theorem galerkinForcing_ofContinuousOn_tendsto_timeModeCoeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    Tendsto (fun N => TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i))
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hcontField : ∀ N, ContinuousOn
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N t) ((a : ℝ) + 2))) (Set.Icc (0 : ℝ) T) :=
    fun N => hK.continuous.comp_continuousOn
      (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
  have hfield := deTurckGalerkinForcing_field_tendsto_force_timeL2 (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 gforce hforce U hUinit hUcont hUderiv hcontField
  have hmode : Tendsto
      (fun N => timeModeCoeff (I := I) (M := M) (TimeSobolev.ofContinuousOn (hcontField N)) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) :=
    (((tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto
      gforce).comp hfield
  refine hmode.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N :=
    eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
  refine Lp.ext ?_
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (TimeSobolev.ofContinuousOn (hcontField N)) i
  have hF := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
  have hG := TimeSobolev.coeFn_ofContinuousOn
    (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i)
  refine hL.trans (Filter.EventuallyEq.trans ?_ hG.symm)
  filter_upwards [hF] with t ht
  rw [ht, deTurckGalerkinForcing_apply, if_pos hi]

theorem galerkin_perMode_aeTendsto_maxRegCoeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop
        (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hforcing := galerkinForcing_ofContinuousOn_tendsto_timeModeCoeff
    (I := I) (M := M) g₀ g_bg a ha_super hT hT1 gforce hforce U hUinit hUcont hUderiv i
  have hmaxid := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M)
    (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
    (a := (a : ℝ)) hT hT1 gforce i
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  filter_upwards [hmaxid, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htmaxid htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hpconv := tendsto_perModeConv_of_tendsto_timeL2 (T := T) lam hlam_nonneg hforcing htmem'
  have hev : (fun N => perModeConv lam
        (fun s => (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N
            (hUcont N) i)) s) t)
      =ᶠ[atTop]
      (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N :=
      eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
    rw [finiteEigenComboHs_coeff, if_pos hi,
      galerkinPerMode_eq_perModeConv (I := I) (M := M) g₀ g_bg a ha_super hT U N
        (hUinit N) (hUcont N) (hUderiv N) i hi htmem']
    refine perModeConv_timeL2_congr lam ?_ htmem'
    have hcoe := TimeSobolev.coeFn_ofContinuousOn
      (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i)
    have hcoe' : ⇑(TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) := hcoe
    have hext : (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
      simpa using Set.IccExtend_of_mem hT.le
        (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i) hs
    exact hcoe'.trans hext.symm
  have hfinal : Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
      atTop (𝓝 (perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) :=
    hpconv.congr' hev
  rwa [htmaxid]

theorem galerkinSolField_aeTendsto_maxRegSolField
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) :
    ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))
        atTop
        (𝓝 (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) := by
  classical
  haveI hcount : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  have hpermode : ∀ i, ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) :=
    fun i => galerkin_perMode_aeTendsto_maxRegCoeff (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 gforce hforce U hUinit hUcont hUderiv i
  have hpermode' : ∀ᵐ t ∂(timeMeasure T), ∀ i,
      Tendsto (fun N => (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)).coeff i)
        atTop (𝓝 ((maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)) :=
    ae_all_iff.2 hpermode
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScale (I := I) (M := M) g₀ g_bg a ha_super (T := T) U hUinit
  obtain ⟨Bound, hBound⟩ :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U) (Fseq := deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB 3
  filter_upwards [hpermode', ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t ht_coeff ht_mem
  have ht_mem' : t ∈ Set.Icc (0 : ℝ) T := ht_mem
  refine tendsto_finiteEigenComboHs_of_coeff_tendsto_of_succWeighted_bound
    (I := I) (M := M) g₀ ((a : ℝ) + 2) (eigenIdxFinset (I := I) (M := M) g₀)
    (fun N => U N t)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
    Bound (fun N => ?_) ht_coeff
  have h := hBound N t ht_mem'
  unfold galerkinEnergy at h
  rw [show (a : ℝ) + ((3 : ℕ) : ℝ) = (a : ℝ) + 2 + 1 by push_cast; ring] at h
  exact h

theorem deTurckGalerkinNonlinearity_aeTendsto_force
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) :
    ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
            (U N t) ((a : ℝ) + 2)))
        atTop (𝓝 (gforce t)) := by
  classical
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hsol := galerkinSolField_aeTendsto_maxRegSolField (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 gforce hforce U hUinit hUcont hUderiv
  filter_upwards [hsol, hforce] with t ht_sol ht_force
  have hcomp := (hK.continuous.tendsto
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).comp ht_sol
  rw [ht_force]
  simpa only [Function.comp_def] using hcomp

theorem deTurckForce_timeModeCoeff_continuousRep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∃ gRep : ℝ → ℝ, ContinuousOn gRep (Set.Icc (0 : ℝ) T) ∧
      timeModeCoeff (I := I) (M := M) gforce i =ᵐ[timeMeasure T] gRep :=
  sorry

theorem galerkinForcing_aeTendsto_modeRep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∃ gRep : ℝ → ℝ, ContinuousOn gRep (Set.Icc (0 : ℝ) T) ∧
      (timeModeCoeff (I := I) (M := M) gforce i =ᵐ[timeMeasure T] gRep) ∧
      (∀ᵐ t ∂(timeMeasure T),
        Tendsto (fun N => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          atTop (𝓝 (gRep t))) := by
  classical
  obtain ⟨gRep, hRep_cont, hRep_ae⟩ :=
    deTurckForce_timeModeCoeff_continuousRep (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      gforce hforce U hUinit hUcont hUderiv i
  refine ⟨gRep, hRep_cont, hRep_ae, ?_⟩
  have hfield := deTurckGalerkinNonlinearity_aeTendsto_force (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 gforce hforce U hUinit hUcont hUderiv
  have hcoeFn := timeModeCoeff_coeFn (I := I) (M := M) gforce i
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  filter_upwards [hfield, hRep_ae, hcoeFn] with t ht_field ht_ae ht_coeFn
  have hgRep_eq : gRep t = (gforce t).coeff i := ht_ae.symm.trans ht_coeFn
  rw [hgRep_eq]
  have hcoeff : Tendsto (fun N => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N t) ((a : ℝ) + 2))).coeff i) atTop (𝓝 ((gforce t).coeff i)) := by
    have hcont := (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.tendsto (gforce t)
    have hcomp := hcont.comp ht_field
    simpa only [Function.comp_def, tensorHsCoeffL_apply] using hcomp
  refine hcoeff.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [deTurckGalerkinForcing_apply, if_pos (eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀)]

theorem galerkinForcing_uniformOn_tendsto_modeRep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∃ gRep : ℝ → ℝ, ContinuousOn gRep (Set.Icc (0 : ℝ) T) ∧
      (timeModeCoeff (I := I) (M := M) gforce i =ᵐ[timeMeasure T] gRep) ∧
      (∀ᵐ t ∂(timeMeasure T),
        Tendsto (fun N => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          atTop (𝓝 (gRep t))) ∧
      ∃ C : ℝ, ∀ N, ∀ᵐ t ∂(timeMeasure T),
        ‖deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i‖ ≤ C := by
  classical
  obtain ⟨gRep, hRep_cont, hRep_ae, hRep_conv⟩ :=
    galerkinForcing_aeTendsto_modeRep (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      gforce hforce U hUinit hUcont hUderiv i
  refine ⟨gRep, hRep_cont, hRep_ae, hRep_conv, ?_⟩
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScale (I := I) (M := M) g₀ g_bg a ha_super (T := T) U hUinit
  obtain ⟨Bound, hBound⟩ :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U) (Fseq := deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB 2
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  set wi : ℝ := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) with hwi
  have hwi_nonneg : 0 ≤ wi := Real.sqrt_nonneg _
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := NNReal.coe_nonneg K
  set C : ℝ := wi⁻¹ * (‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a 0‖
      + (K : ℝ) * Real.sqrt Bound) with hC
  have hC_nonneg : 0 ≤ C := by
    rw [hC]
    refine mul_nonneg (inv_nonneg.2 hwi_nonneg) ?_
    have h1 : 0 ≤ (K : ℝ) * Real.sqrt Bound := mul_nonneg hKnn (Real.sqrt_nonneg _)
    have h2 : 0 ≤ ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a 0‖ := norm_nonneg _
    linarith
  refine ⟨C, fun N => ?_⟩
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i‖ ≤ C := by
    intro t ht
    rw [deTurckGalerkinForcing_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi]
      set V := finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2) with hV
      have hEbound : galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + 2) t ≤ Bound := by
        have h := hBound N t ht
        rwa [show (a : ℝ) + ((2 : ℕ) : ℝ) = (a : ℝ) + 2 by norm_num] at h
      have hVnorm_sq : ‖V‖ ^ 2 = galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + 2) t := by
        rw [hV, finiteEigenCombo_spectral_normSq]
        rfl
      have hVnorm_le : ‖V‖ ≤ Real.sqrt Bound := by
        have h1 : ‖V‖ ^ 2 ≤ Bound := by rw [hVnorm_sq]; exact hEbound
        calc ‖V‖ = Real.sqrt (‖V‖ ^ 2) := (Real.sqrt_sq (norm_nonneg V)).symm
          _ ≤ Real.sqrt Bound := Real.sqrt_le_sqrt h1
      have hNbound : ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V‖ ≤
          ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a 0‖ + (K : ℝ) * ‖V‖ := by
        have hd := hK.dist_le_mul V 0
        rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
        have hsub := norm_sub_norm_le
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V)
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a 0)
        linarith
      have hcoeff : ‖(deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V).coeff i‖ ≤
          wi⁻¹ * ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V‖ := by
        rw [Real.norm_eq_abs, hwi]
        exact tensorHsAbsCoeffLe (I := I) (M := M)
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V) i
      calc ‖(deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V).coeff i‖
          ≤ wi⁻¹ * ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a V‖ := hcoeff
        _ ≤ wi⁻¹ * (‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a 0‖
              + (K : ℝ) * Real.sqrt Bound) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hwi_nonneg)
            have hKV : (K : ℝ) * ‖V‖ ≤ (K : ℝ) * Real.sqrt Bound :=
              mul_le_mul_of_nonneg_left hVnorm_le hKnn
            linarith
        _ = C := hC.symm
    · rw [if_neg hi, norm_zero]
      exact hC_nonneg
  unfold timeMeasure
  exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun t ht => hpt t ht))

theorem galerkinForcing_ofContinuousOn_tendsto_modeCoeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hcontF : ∀ N, ContinuousOn
      (fun t => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T)) :
    Tendsto (fun N =>
      TimeSobolev.ofContinuousOn (hcontF N))
      atTop
      (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) := by
  classical
  obtain ⟨gRep, hRep_cont, hRep_ae, hRep_conv, C, hC⟩ :=
    galerkinForcing_uniformOn_tendsto_modeRep (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 gforce hforce U hUinit hUcont hUderiv i
  set flim := timeModeCoeff (I := I) (M := M) gforce i with hflim_def
  set f : ℕ → ℝ → ℝ :=
    fun N t => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i with hf_def
  have hf_meas : ∀ N, AEStronglyMeasurable (f N) (timeMeasure T) := by
    intro N
    unfold timeMeasure
    exact (hcontF N).aestronglyMeasurable measurableSet_Icc
  have hf_coe : ∀ N, ⇑(TimeSobolev.ofContinuousOn (hcontF N)) =ᵐ[timeMeasure T] f N :=
    fun N => TimeSobolev.coeFn_ofContinuousOn (hcontF N)
  have hgRep_memLp : MemLp gRep 2 (timeMeasure T) := (Lp.memLp flim).ae_eq hRep_ae
  have hflim_eq : flim = hgRep_memLp.toLp gRep := by
    refine Lp.ext ?_
    exact hRep_ae.trans (hgRep_memLp.coeFn_toLp).symm
  have hui : UnifIntegrable f 2 (timeMeasure T) :=
    unifIntegrable_of_uniform_norm_bound hf_meas hC
  have heLp : Tendsto (fun N => eLpNorm (f N - gRep) 2 (timeMeasure T)) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hf_meas hgRep_memLp hui
      hRep_conv
  have heLp' : Tendsto (fun N =>
      eLpNorm (⇑(TimeSobolev.ofContinuousOn (hcontF N)) - gRep) 2 (timeMeasure T))
      atTop (𝓝 0) := by
    refine heLp.congr (fun N => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hf_coe N] with t ht
    simp only [Pi.sub_apply, ht]
  rw [hflim_eq]
  exact Lp.tendsto_Lp_of_tendsto_eLpNorm gRep hgRep_memLp heLp'

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
