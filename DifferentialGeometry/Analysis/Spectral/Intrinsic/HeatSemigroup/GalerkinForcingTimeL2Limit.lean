import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeL2EigenProjection
import DifferentialGeometry.Analysis.ProjectedContractionFixedPoint
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

private theorem tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ' σ'' : ℝ}
    (hσ'σ'' : σ' < σ'')
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0)) :
    Tendsto (fun n => ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  classical
  set ι := TensorEigenIdx (I := I) (M := M) g r s
  have hnormsq : ∀ n,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ ^ 2 =
        ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ((d n).coeff i) ^ 2 := by
    intro n
    have h := tensorHs.norm_sq_eq_tsum (I := I) (M := M)
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))
    rwa [tensorHsInclusion_coeff] at h
  have hsumm' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) :=
    fun n => tensorHs.weighted_summable_of_le (I := I) (M := M) hσ'σ''.le (d n)
  have hmass'' : ∀ n,
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2
        = ‖d n‖ ^ 2 :=
    fun n => (tensorHs.norm_sq_eq_tsum (I := I) (M := M) (d n)).symm
  suffices hsq : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖ ^ 2) atTop (𝓝 0) by
    have hnn : ∀ n,
        0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ := fun n => norm_nonneg _
    have hsqrt :
        Tendsto (fun n => Real.sqrt
          (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            hσ'σ''.le (d n)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr (fun n => ?_)
    rw [Real.sqrt_sq (hnn n)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hexp : σ' - σ'' < 0 := by linarith
  obtain ⟨Λ, hΛgt1, hΛtail⟩ :
      ∃ Λ : ℝ, 1 < Λ ∧ Λ ^ (σ' - σ'') * C ^ 2 < ε / 2 := by
    set δ : ℝ := (ε / 2) / (C ^ 2 + 1) with hδ_def
    have hδ_pos : 0 < δ := by
      have : (0 : ℝ) < C ^ 2 + 1 := by positivity
      rw [hδ_def]; positivity
    have htend : Tendsto (fun x : ℝ => x ^ (σ' - σ'')) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := σ'' - σ') (by linarith)
      rwa [show -(σ'' - σ') = σ' - σ'' by ring] at h
    have hev : ∀ᶠ x : ℝ in atTop, x ^ (σ' - σ'') < δ :=
      htend.eventually_lt_const hδ_pos
    obtain ⟨Λ, hΛ1, hΛδ⟩ := ((eventually_gt_atTop 1).and hev).exists
    refine ⟨Λ, hΛ1, ?_⟩
    have hΛδ_nn : 0 ≤ Λ ^ (σ' - σ'') := Real.rpow_nonneg (by linarith) _
    have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg C
    have h1 : Λ ^ (σ' - σ'') * C ^ 2 ≤ δ * C ^ 2 :=
      mul_le_mul_of_nonneg_right hΛδ.le hCsq_nn
    have h2 : δ * C ^ 2 < ε / 2 := by
      rw [hδ_def]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
      have hεpos : 0 < ε / 2 := by linarith
      nlinarith [hεpos, hCsq_nn]
    linarith
  set F : Finset ι :=
    (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset
    with hF_def
  have hmemF : ∀ i : ι, i ∈ F ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
    intro i; rw [hF_def, Set.Finite.mem_toFinset]; rfl
  have hcompl_bd : ∀ (n : ℕ) (i : ι), i ∉ F →
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
    intro n i hi
    have hΛle : Λ ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      by_contra hcon
      exact hi ((hmemF i).2 (lt_of_not_ge hcon))
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ' =
        tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
          tensorSobolevWeight (I := I) (M := M) i σ'' := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)]
      congr 1; ring
    have hratio : tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') ≤
        Λ ^ (σ' - σ'') := by
      unfold tensorSobolevWeight
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hΛle hexp.le
    have hw''_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
    have hcoeff_nn : 0 ≤ ((d n).coeff i) ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
            rw [hsplit]; ring
      _ ≤ Λ ^ (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
  have htail : ∀ n,
      ∑' i : { i : ι // i ∉ F },
          tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') * C ^ 2 := by
    intro n
    have hsub_summ' : Summable (fun i : { i : ι // i ∉ F } =>
        tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2) :=
      (hsumm' n).subtype _
    have hsub_summ'' : Summable (fun i : { i : ι // i ∉ F } =>
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2)) :=
      ((d n).weighted_summable.subtype _).mul_left _
    calc
      ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2
          ≤ ∑' i : { i : ι // i ∉ F },
              Λ ^ (σ' - σ'') *
                (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                  ((d n).coeff i) ^ 2) :=
            hsub_summ'.tsum_le_tsum
              (fun i => hcompl_bd n i.1 i.2) hsub_summ''
      _ = Λ ^ (σ' - σ'') *
            ∑' i : { i : ι // i ∉ F },
              tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2 :=
            (tsum_mul_left)
      _ ≤ Λ ^ (σ' - σ'') *
            ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
              ((d n).coeff i) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            refine ((d n).weighted_summable.subtype _).tsum_le_tsum_of_inj
              Subtype.val Subtype.val_injective (fun i _ => ?_) (fun i => le_refl _)
              (d n).weighted_summable
            have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
              tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
            positivity
      _ ≤ Λ ^ (σ' - σ'') * C ^ 2 := by
            rw [hmass'' n]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            have hnn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
            nlinarith [hCbd n, hnn, hC]
  have hfin0 : Tendsto (fun n =>
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (s := F)
      (f := fun i n => tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      (a := fun _ : ι => (0 : ℝ))
      (fun i _ => by
        have hc : Tendsto (fun n => ((d n).coeff i) ^ 2) atTop (𝓝 (0 ^ 2)) :=
          (hcoeff0 i).pow 2
        rw [show (0 : ℝ) ^ 2 = 0 by ring] at hc
        have := hc.const_mul (tensorSobolevWeight (I := I) (M := M) i σ')
        simpa using this)
    simpa using h
  rw [Metric.tendsto_atTop] at hfin0
  obtain ⟨N, hN⟩ := hfin0 (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hsplit_sum :
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) +
          ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 :=
    ((hsumm' n).sum_add_tsum_subtype_compl F).symm
  have hfin_lt : ∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 < ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
        ≤ |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2| :=
          le_abs_self _
      _ < ε / 2 := hd
  have htail_lt : ∑' i : { i : ι // i ∉ F },
      tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 < ε / 2 :=
    lt_of_le_of_lt (htail n) hΛtail
  have hbound : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 < ε := by
    rw [hnormsq n, hsplit_sum]
    linarith
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 := sq_nonneg _
  rwa [abs_of_nonneg hnn]

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
      atTop (𝓝 W) := by
  classical
  set u : ℕ → tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) (σ + 1) with hu_def
  have hu_coeff : ∀ N i, (u N).coeff i =
      (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i := by
    intro N i
    simp only [hu_def, finiteEigenComboHs_coeff]
  have hconv_coeff : ∀ i, Tendsto (fun N => (u N).coeff i) atTop (𝓝 (W.coeff i)) := by
    intro i
    exact (hcoeff i).congr (fun N => (hu_coeff N i).symm)
  have hu_normSq_le : ∀ N, ‖u N‖ ^ 2 ≤ B := by
    intro N
    have heq : ‖u N‖ ^ 2 = ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 := by
      simp only [hu_def]
      rw [finiteEigenCombo_spectral_normSq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rfl
    rw [heq]; exact hbound N
  have hbd_finset : ∀ t : Finset (TensorEigenIdx (I := I) (M := M) g 0 2),
      ∑ i ∈ t, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 ≤ B := by
    intro t
    have hlim : Tendsto
        (fun N => ∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2)
        atTop
        (𝓝 (∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2)) := by
      refine tendsto_finset_sum t (fun i _ => ?_)
      exact ((hconv_coeff i).pow 2).const_mul _
    have hle : ∀ N, ∑ i ∈ t,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2 ≤ B := by
      intro N
      calc ∑ i ∈ t,
            tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2
          = ∑ i ∈ t, (if i ∈ S N then
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hu_coeff, finiteEigenComboHs_coeff]
            by_cases hi : i ∈ S N <;> simp [hi]
        _ = ∑ i ∈ t ∩ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_ite_mem t (S N) _
        _ ≤ ∑ i ∈ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
              (fun i _ _ => mul_nonneg
                (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
        _ ≤ B := hbound N
    exact le_of_tendsto' hlim hle
  have hnn : (0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) ≤
      fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 :=
    fun i => mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _)
  have hWp_summ : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2) :=
    summable_of_sum_le hnn hbd_finset
  set Wp : tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    ⟨W.coeff, hWp_summ⟩ with hWp_def
  have hWp_coeff : ∀ i, Wp.coeff i = W.coeff i := by
    intro i; rw [hWp_def]
  have hWp_normSq_le : ‖Wp‖ ^ 2 ≤ B := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) Wp]
    simp only [hWp_coeff]
    exact Real.tsum_le_of_sum_le hnn hbd_finset
  have hsubcoeff : ∀ (a b : tensorHs (I := I) (M := M) g 0 2 (σ + 1)) i,
      (a - b).coeff i = a.coeff i - b.coeff i := by
    intro a b i
    simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
  have hCbd : ∀ N, ‖u N - Wp‖ ≤ 2 * Real.sqrt B := by
    intro N
    have huN : ‖u N‖ ≤ Real.sqrt B := by
      calc ‖u N‖ = Real.sqrt (‖u N‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt (hu_normSq_le N)
    have hWpn : ‖Wp‖ ≤ Real.sqrt B := by
      calc ‖Wp‖ = Real.sqrt (‖Wp‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hWp_normSq_le
    calc ‖u N - Wp‖ ≤ ‖u N‖ + ‖Wp‖ := norm_sub_le _ _
      _ ≤ Real.sqrt B + Real.sqrt B := add_le_add huN hWpn
      _ = 2 * Real.sqrt B := by ring
  have hcoeff0 : ∀ i, Tendsto (fun N => (u N - Wp).coeff i) atTop (𝓝 0) := by
    intro i
    have h := (hconv_coeff i).sub_const (W.coeff i)
    rw [sub_self] at h
    refine h.congr (fun N => ?_)
    rw [hsubcoeff (u N) Wp i, hWp_coeff i]
  have hlt : (σ : ℝ) < σ + 1 := by linarith
  have hsqrtB_nn : (0 : ℝ) ≤ 2 * Real.sqrt B := by positivity
  have hhelper := tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ' := σ) (σ'' := σ + 1)
    hlt (fun N => u N - Wp) hsqrtB_nn hCbd hcoeff0
  have hincl_uN : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N) = finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ := by
    intro N
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hu_coeff N i]
  have hincl_Wp :
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hlt.le Wp = W := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hWp_coeff i]
  have hincl_eq : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N - Wp) =
        finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W := by
    intro N
    rw [map_sub, hincl_uN N, hincl_Wp]
  have hNorm : Tendsto
      (fun N => ‖finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W‖)
      atTop (𝓝 0) := by
    refine hhelper.congr (fun N => ?_)
    rw [hincl_eq N]
  have hSub := tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  exact tendsto_sub_nhds_zero_iff.mp hSub

theorem galerkinForcing_field_eq_maxRegDuhamel_projTruncation
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
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
    (N : ℕ) :
    TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M)
            (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
              a ha_super)
            (TimeSobolev.ofContinuousOn
              (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))))) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set hLipC := deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set gforceN := nemytskii (I := I) (M := M) hLipC VN with hgforceN_def
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  refine Lp.ext ?_
  have hLco := timeModeCoeff_coeFn (I := I) (M := M) VN i
  have hVco : ⇑VN =ᵐ[timeMeasure T]
      (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hRco := timeModeCoeff_coeFn (I := I) (M := M)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT hT1 (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (VN s)) :=
    nemytskii_coeFn (I := I) (M := M) hLipC VN
  have hPNforcing : ⇑(timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) =ᵐ[timeMeasure T]
      (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) := by
    filter_upwards [hPNco, hPproj, hgco, hVco] with s hs1 hs2 hs3 hs4
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff, deTurckGalerkinForcing_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi, if_pos hi, hs3, hs4]
    · rw [if_neg hi, if_neg hi]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun t => U N t i := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_pos hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam
          (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) t :=
      perModeConv_timeL2_congr lam hPNforcing htmem'
    have hgp := galerkinPerMode_eq_perModeConv (I := I) (M := M) g₀ g_bg a ha_super hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hi htmem'
    rw [← hlam_def] at hgp
    rw [hgp, hcongr1]
    refine perModeConv_timeL2_congr lam ?_ htmem'
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
    rw [Set.IccExtend_of_mem hT.le _ hs]
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun _ => (0 : ℝ) := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_neg hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam (fun _ => (0 : ℝ)) t := by
      refine perModeConv_timeL2_congr lam ?_ htmem'
      filter_upwards [hPNforcing] with s hs
      rw [hs, deTurckGalerkinForcing_apply, if_neg hi]
    rw [hcongr1]
    unfold perModeConv
    simp

private theorem nemytskiiMixedForcingMap_norm_le_ballRadius
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTime (I := I) (M := M) g₀ g_bg a ha_super)
    (G : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hG : ‖G‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super) hT hT1 G‖ ≤
      deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  set hLip := deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLip_def
  set hmix := deTurckSobolevNHa2_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hmix_def
  set C₁ : ℝ≥0 := hmix.choose with hC₁def
  set C₂ : ℝ≥0 := hmix.choose_spec.choose with hC₂def
  set ρ : ℝ := deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hsingle := hmix.choose_spec.choose_spec
  have hρeq : ρ = 1 / (16 * ((C₁ : ℝ) + 1)) := rfl
  have hρpos : 0 < ρ := by rw [hρeq]; positivity
  set M₀ : ℝ := ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTsh (deTurckForceShortTime_le_sq (I := I) (M := M) g₀ g_bg a ha_super)
  have hT_stay : T ≤ (ρ / (2 * (M₀ + 1))) ^ 2 := by
    refine le_trans hTsh ?_
    rw [deTurckForceShortTime]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T_le : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ (C₁ : ℝ) * 2 * ρ * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T_le h1T
      have hρnn : 0 ≤ ρ := hρpos.le
      gcongr
    refine le_trans hle ?_
    rw [hρeq]
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  have hcoef_nn : (0:ℝ) ≤ (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have hcoef_le : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by linarith
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (M₀ + 1)) := by
      rw [show ρ / (2 * (M₀ + 1)) = Real.sqrt ((ρ / (2 * (M₀ + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (M₀ + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (M₀ + 1))) * (M₀ + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (M₀ + 1) ≠ 0 := by positivity
          field_simp
  have hΨ0 : ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤ Real.sqrt T * M₀ := by
    rw [nemytskiiMixedForcingMap_apply,
      maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1]
    refine timeL2_norm_le_of_ae_bound _ (by positivity) ?_
    have hcoe := nemytskii_coeFn (I := I) (M := M) hLip
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    have hzero := Lp.coeFn_zero (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (p := 2) (μ := timeMeasure T)
    filter_upwards [hcoe, hzero] with t ht htz
    rw [ht, htz, Pi.zero_apply]
  have hball := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρpos.le G (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hG
    (by rw [norm_zero]; exact hρpos.le)
  rw [sub_zero] at hball
  calc ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G‖
      = ‖(nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)) +
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ +
          ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := norm_add_le _ _
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖ +
          Real.sqrt T * M₀ := add_le_add hball hΨ0
    _ ≤ (1 / 2) * ρ + ρ / 2 := by
        refine add_le_add ?_ hsqrtTM
        calc ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖
            ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ρ :=
              mul_le_mul_of_nonneg_left hG hcoef_nn
          _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hcoef_le hρpos.le
    _ = ρ := by ring

theorem galerkinODE_solution_unique
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (_hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V' t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hinit : ∀ i ∈ S, V 0 i = V' 0 i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    V t i = V' t i := by
  classical
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordField_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  set e := EuclideanSpace.equiv {i // i ∈ S} ℝ with he_def
  set γ : (ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) →
      ℝ → EuclideanSpace ℝ {i // i ∈ S} :=
    fun W t => e.symm (fun j => W t j.1) with hγ_def
  have hcomp_j : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ)
      (j : {i // i ∈ S}), (γ W t) j = W t j.1 := by
    intro W t j; rfl
  have hembed : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ),
      galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ W t) =
        finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2) := by
    intro W t
    apply tensorHs.ext
    funext i'
    rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
    by_cases hi' : i' ∈ S
    · rw [dif_pos hi', if_pos hi']; rfl
    · rw [dif_neg hi', if_neg hi']
  have hγcont : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ i ∈ S, ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T)) →
      ContinuousOn (γ W) (Set.Icc (0 : ℝ) T) := by
    intro W hWcont
    exact e.symm.continuous.comp_continuousOn (continuousOn_pi.2 (fun j => hWcont j.1 j.2))
  have hγderiv : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => W r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1) =
        galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t) := by
      apply e.injective
      ext j
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change _ = (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) j
      rw [galerkinCoordField_apply, hcomp_j, hembed]
    rw [hval] at hcomp
    exact hcomp
  have hlip_univ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith Klip (galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
        (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})) :=
    fun _ _ => hKlip.lipschitzOnWith
  have heqOn : Set.EqOn (γ V) (γ V') (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
      (s := fun _ => (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})))
      hlip_univ (hγcont V hVcont) (fun s hs => hγderiv V hVderiv s hs)
      (fun _ _ => Set.mem_univ _) (hγcont V' hV'cont) (fun s hs => hγderiv V' hV'deriv s hs)
      (fun _ _ => Set.mem_univ _) ?_
    apply e.injective
    ext j
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact hinit j.1 j.2
  have := heqOn ht
  have hj : (γ V t) ⟨i, hi⟩ = (γ V' t) ⟨i, hi⟩ := by rw [this]
  rw [hcomp_j, hcomp_j] at hj
  exact hj

theorem galerkinForcing_norm_le_ballRadius
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ deTurckForceShortTime (I := I) (M := M) g₀ g_bg a ha_super)
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
    (N : ℕ) :
    ‖nemytskii (I := I) (M := M)
        (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))‖ ≤
      deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  haveI hcount : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) h_compact
  set hLipC := deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set ρ : ℝ := deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, deTurckForceBallRadius]; positivity
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set Ψ' := deTurckForceRetractedMap (I := I) (M := M) g₀ g_bg a ha_super hT hT1 with hΨ'_def
  have hκlt : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
    deTurckForceRetractedMap_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
  have hPΦ : ContractingWith (1 / 2 : ℝ≥0)
      (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
    refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    rw [Function.comp_apply, Function.comp_apply,
      show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num, dist_eq_norm, dist_eq_norm]
    calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
            timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
        = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
      _ ≤ ‖Ψ' x - Ψ' y‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ (1 / 2) * ‖x - y‖ := by
          have hd := hΨ'_lip.dist_le_mul x y
          rw [dist_eq_norm, dist_eq_norm, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at hd
          exact hd
  set yN := ContractingWith.fixedPoint
    (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') hPΦ with hyN_def
  have hyN_fix : (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') yN = yN :=
    ContractingWith.fixedPoint_isFixedPt hPΦ
  have hΨ'stay : ∀ z, ‖Ψ' z‖ ≤ ρ := by
    intro z
    rw [hΨ'_def, deTurckForceRetractedMap_apply]
    refine nemytskiiMixedForcingMap_norm_le_ballRadius (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ _ ?_
    have hmem := recenteredBallRetraction_mapsTo
      (X := timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) (Set.mem_univ z)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hyN_norm : ‖yN‖ ≤ ρ := by
    have h1 := hyN_fix
    rw [Function.comp_apply] at h1
    calc ‖yN‖ = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' yN)‖ := by rw [h1]
      _ ≤ ‖Ψ' yN‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ ρ := hΨ'stay yN
  set vN := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) yN with hvN_def
  have hΨ'yN : Ψ' yN = nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLipC hT hT1 yN := by
    rw [hΨ'_def,
      deTurckForceRetractedMap_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super hT hT1 yN hyN_norm]
  have hyN_eq : yN = timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
      (nemytskii (I := I) (M := M) hLipC vN) := by
    have h1 := hyN_fix
    rw [Function.comp_apply, hΨ'yN, nemytskiiMixedForcingMap_apply] at h1
    exact h1.symm
  set W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t with hW_def
  have hvN_coeff : ∀ i, (fun t => (vN t).coeff i) =ᵐ[timeMeasure T] (fun t => W t i) := by
    intro i
    exact timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1 yN i
  have hyN_mode : ∀ j, ⇑(timeModeCoeff (I := I) (M := M) yN j) =ᵐ[timeMeasure T]
      (fun s => if j ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
        (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (vN s)).coeff j else 0) := by
    intro j
    have hco := timeModeCoeff_coeFn (I := I) (M := M)
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (nemytskii (I := I) (M := M) hLipC vN)) j
    have hproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M) hLipC vN)) =ᵐ[timeMeasure T]
        (fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N
          ((nemytskii (I := I) (M := M) hLipC vN) s)) :=
      ContinuousLinearMap.coeFn_compLpL _ (nemytskii (I := I) (M := M) hLipC vN)
    have hX := nemytskii_coeFn (I := I) (M := M) hLipC vN
    rw [hyN_eq]
    filter_upwards [hco, hproj, hX] with s hs1 hs2 hs3
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff]
    by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hj, if_pos hj, hs3]
    · rw [if_neg hj, if_neg hj]
  have hvN_eq_combo : ∀ᵐ s ∂(timeMeasure T),
      vN s = finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2) := by
    have hall : ∀ᵐ s ∂(timeMeasure T), ∀ j,
        (vN s).coeff j = (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2)).coeff j := by
      refine ae_all_iff.2 (fun j => ?_)
      by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
      · filter_upwards [hvN_coeff j] with s hs
        rw [hs, finiteEigenComboHs_coeff, if_pos hj]
      · filter_upwards [hvN_coeff j, hyN_mode j, ae_restrict_mem (μ := volume) measurableSet_Icc]
          with s hs hmode humem
        have humem' : s ∈ Set.Icc (0 : ℝ) T := humem
        rw [hs, finiteEigenComboHs_coeff, if_neg hj]
        change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
          (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s = 0
        have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
              (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j) (fun _ => (0 : ℝ)) s := by
          refine perModeConv_timeL2_congr _ ?_ humem'
          filter_upwards [hyN_mode j] with u hu
          rw [hu, if_neg hj]
        rw [hcongr]; unfold perModeConv; simp
    filter_upwards [hall] with s hs
    apply tensorHs.ext
    funext j
    exact hs j
  have hWcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T) := by
    intro i _
    exact continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) yN i) hT.le
  have hWderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => W r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    set fForce : ℝ → ℝ := Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W p.1) ((a : ℝ) + 2))).coeff i) with hfForce_def
    have hg_cont : ContinuousOn (fun s => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      refine (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super
        (fun _ => W) N hWcont i).congr (fun s _ => ?_)
      rw [deTurckGalerkinForcing_apply, if_pos hi]
    have hfForce_cont : Continuous fForce := Continuous.Icc_extend' hg_cont.restrict
    have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
        fForce x = (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (W x) ((a : ℝ) + 2))).coeff i := by
      intro x hx
      rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
    have hWrep : ∀ s ∈ Set.Icc (0 : ℝ) T,
        W s i = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s := by
      intro s hs
      change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) yN i) u) s =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s
      refine perModeConv_timeL2_congr (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ hs
      filter_upwards [hyN_mode i, hvN_eq_combo, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with u hu1 hu2 humem'
      have humem : u ∈ Set.Icc (0 : ℝ) T := humem'
      rw [hu1, if_pos hi, hu2, hfForce_mem humem]
    have hIcc_mem : Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici t] t := by
      have h1 : Set.Ici t ∩ Set.Iic T ∈ 𝓝[Set.Ici t] t :=
        inter_mem_nhdsWithin (Set.Ici t) (Iic_mem_nhds ht.2)
      rw [Set.Ici_inter_Iic] at h1
      exact Filter.mem_of_superset h1 (Set.Icc_subset_Icc_left ht.1)
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hWi_eqEv : (fun r => W r i) =ᶠ[𝓝[Set.Ici t] t]
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce) :=
      Filter.eventuallyEq_of_mem hIcc_mem (fun r hr => hWrep r hr)
    have hderiv_pmc : HasDerivWithinAt (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce)
        (fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t) (Set.Ici t) t :=
      (perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i) hfForce_cont t).hasDerivWithinAt
    have hderiv_W := hderiv_pmc.congr_of_eventuallyEq hWi_eqEv (hWrep t htIcc)
    have hval_eq : fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i := by
      rw [hfForce_mem htIcc, ← hWrep t htIcc]; ring
    rw [hval_eq] at hderiv_W
    exact hderiv_W
  have hUderivN : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    have hd := hUderiv N t ht i hi
    rwa [deTurckGalerkinForcing_apply, if_pos hi] at hd
  have hinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = W 0 i := by
    intro i hi
    rw [hUinit N i hi]
    change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) 0
    rw [perModeConv_zero_left]
  have hVN_eq_vN : VN = vN := by
    refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
    refine Lp.ext ?_
    have hL := timeModeCoeff_coeFn (I := I) (M := M) VN i
    have hVco : ⇑VN =ᵐ[timeMeasure T]
        (fun t => finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
      TimeSobolev.coeFn_ofContinuousOn _
    have hR := timeModeCoeff_coeFn (I := I) (M := M) vN i
    refine hL.trans (Filter.EventuallyEq.trans ?_ (hR.trans (hvN_coeff i)).symm)
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · filter_upwards [hVco, ae_restrict_mem (μ := volume) measurableSet_Icc] with t htV htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_pos hi]
      exact galerkinODE_solution_unique (I := I) (M := M) g₀ g_bg a ha_super hT
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) W (hUcont N) hUderivN hWcont hWderiv
        hinit i hi htmem'
    · filter_upwards [hVco, hyN_mode i, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htV hmode htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_neg hi]
      change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t
      have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fun _ => (0 : ℝ)) t := by
        refine perModeConv_timeL2_congr _ ?_ htmem'
        filter_upwards [hyN_mode i] with s hs
        rw [hs, if_neg hi]
      rw [hcongr]; unfold perModeConv; simp
  have hfinal : nemytskii (I := I) (M := M) hLipC VN = Ψ' yN := by
    rw [hVN_eq_vN, hΨ'yN, nemytskiiMixedForcingMap_apply]
  rw [hfinal]
  exact hΨ'stay yN

theorem galerkinForcing_tendsto_force_timeL2_ofProjFixedPoint
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
  have hfield : Tendsto (fun N => TimeSobolev.ofContinuousOn (hcontField N)) atTop (𝓝 gforce) := by
    have hTsh : T ≤ deTurckForceShortTime (I := I) (M := M) g₀ g_bg a ha_super := by
      rw [← deTurckRicci_maxreg_solution_choose_eq_shortTime (I := I) (M := M) g₀ g_bg a ha_super]
      exact hTT₀
    set Ψ' := deTurckForceRetractedMap (I := I) (M := M) g₀ g_bg a ha_super hT hT1 with hΨ'_def
    have hκcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    have hκlt : (1 / 2 : ℝ≥0) < 1 := by
      rw [← NNReal.coe_lt_coe, hκcoe, NNReal.coe_one]; norm_num
    have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
      deTurckForceRetractedMap_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh
    have hcontr : ContractingWith (1 / 2 : ℝ≥0) Ψ' := ⟨hκlt, hΨ'_lip⟩
    have hPtendsto : ∀ x, Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N x)
        atTop (𝓝 x) := fun x => timeL2EigenProj_tendsto (I := I) (M := M) g₀ (a : ℝ) T x
    have hPΦ : ∀ N, ContractingWith (1 / 2 : ℝ≥0)
        (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
      intro N
      refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
      rw [Function.comp_apply, Function.comp_apply, hκcoe, dist_eq_norm, dist_eq_norm]
      calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
              timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
          = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
        _ ≤ ‖Ψ' x - Ψ' y‖ := by
            refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
            exact mul_le_of_le_one_left (norm_nonneg _)
              (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
        _ ≤ (1 / 2) * ‖x - y‖ :=
            deTurckForceRetractedMap_dist_le_half (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh x y
    have hFP := DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction
      hcontr (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) hPtendsto hPΦ
    have hgforce_fix : Ψ' gforce = gforce := by
      rw [hΨ'_def, deTurckForceRetractedMap_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT hT1 gforce hgforce, nemytskiiMixedForcingMap_apply]
      refine Lp.ext ?_
      exact (nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)).trans hforce.symm
    have hFstar_eq : ContractingWith.fixedPoint Ψ' hcontr = gforce :=
      (ContractingWith.fixedPoint_unique hcontr hgforce_fix).symm
    rw [hFstar_eq] at hFP
    have hgforceN_eq : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        nemytskii (I := I) (M := M)
          (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
            a ha_super)
          (TimeSobolev.ofContinuousOn
            (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))) := by
      intro N
      refine Lp.ext ?_
      have h1 := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
      have h2 := nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
      have h3 := TimeSobolev.coeFn_ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      rw [ht1, ht2, ht3]
    have hball : ∀ N, ‖TimeSobolev.ofContinuousOn (hcontField N)‖ ≤
        deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      rw [hgforceN_eq N]
      exact galerkinForcing_norm_le_ballRadius (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh U
        hUinit hUcont hUderiv N
    have hxN_ball : ∀ N, ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))‖ ≤
        deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      refine le_trans ?_ (hball N)
      refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
    have hgforceN_Ψ' : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        Ψ' (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))) := by
      intro N
      rw [hΨ'_def, deTurckForceRetractedMap_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT hT1 _ (hxN_ball N), nemytskiiMixedForcingMap_apply, hgforceN_eq N]
      congr 1
      exact galerkinForcing_field_eq_maxRegDuhamel_projTruncation (I := I) (M := M) g₀ g_bg a
        ha_super hT hT1 U hUinit hUcont hUderiv N
    have hxN_fix : ∀ N, ContractingWith.fixedPoint
          (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') (hPΦ N) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N)) := by
      intro N
      refine (ContractingWith.fixedPoint_unique (hPΦ N) ?_).symm
      change (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ')
          (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
            (TimeSobolev.ofContinuousOn (hcontField N))) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))
      rw [Function.comp_apply, ← hgforceN_Ψ' N]
    have hxN_tendsto : Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))) atTop (𝓝 gforce) :=
      hFP.congr (fun N => hxN_fix N)
    have hcomp := (hΨ'_lip.continuous.tendsto gforce).comp hxN_tendsto
    rw [hgforce_fix] at hcomp
    exact hcomp.congr (fun N => (hgforceN_Ψ' N).symm)
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

theorem perMode_aeTendsto_of_galerkinODE
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
  have hforcing := galerkinForcing_tendsto_force_timeL2_ofProjFixedPoint
    (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
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

theorem galerkinSolField_aeTendsto_maxRegSolField_core
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
      hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
      hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv hcontField
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
      hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv
  filter_upwards [hsol, hforce] with t ht_sol ht_force
  have hcomp := (hK.continuous.tendsto
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).comp ht_sol
  rw [ht_force]
  simpa only [Function.comp_def] using hcomp

theorem galerkinForcing_aeTendsto_modeRep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    ∃ gRep : ℝ → ℝ,
      (timeModeCoeff (I := I) (M := M) gforce i =ᵐ[timeMeasure T] gRep) ∧
      (∀ᵐ t ∂(timeMeasure T),
        Tendsto (fun N => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          atTop (𝓝 (gRep t))) := by
  classical
  refine ⟨fun t => (gforce t).coeff i,
    timeModeCoeff_coeFn (I := I) (M := M) gforce i, ?_⟩
  have hfield := deTurckGalerkinNonlinearity_aeTendsto_force (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  filter_upwards [hfield] with t ht_field
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
    ∃ gRep : ℝ → ℝ,
      (timeModeCoeff (I := I) (M := M) gforce i =ᵐ[timeMeasure T] gRep) ∧
      (∀ᵐ t ∂(timeMeasure T),
        Tendsto (fun N => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          atTop (𝓝 (gRep t))) ∧
      ∃ C : ℝ, ∀ N, ∀ᵐ t ∂(timeMeasure T),
        ‖deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i‖ ≤ C := by
  classical
  obtain ⟨gRep, hRep_ae, hRep_conv⟩ :=
    galerkinForcing_aeTendsto_modeRep (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
  refine ⟨gRep, hRep_ae, hRep_conv, ?_⟩
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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution (I := I) (M := M)
      g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a ha_super)
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
  obtain ⟨gRep, hRep_ae, hRep_conv, C, hC⟩ :=
    galerkinForcing_uniformOn_tendsto_modeRep (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
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
