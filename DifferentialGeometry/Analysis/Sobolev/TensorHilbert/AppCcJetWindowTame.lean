import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckPrincipalCometricCoeff
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
theorem appCcRS_l2_le_of_pointwise_fiberNormSq_bound_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (B : ℝ) (hB : 0 ≤ B)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) ≤ B ^ 2) :
    ‖appCcRS (I := I) (M := M) g a b c Φ W‖ ≤ B * ‖W‖ := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g a b W).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((appCcRS (I := I) (M := M) g a b c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
      (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    exact mul_le_mul_of_nonneg_right (hΦ x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g a b x _)
  have hsq : ‖appCcRS (I := I) (M := M) g a b c Φ W‖ ^ 2 ≤ B ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g a c
      (appCcRS (I := I) (M := M) g a b c Φ W) F hF_int hpt
    rw [hF_def, MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g a b W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ B * ‖W‖ := mul_nonneg hB (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  rw [mul_pow]
  exact hsq

set_option linter.unusedSectionVars false in
theorem appCcRS_l2_le_of_pointwise_fiberNormSq_bound_right
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) ≤ B ^ 2) :
    ‖appCcRS (I := I) (M := M) g a b c Φ W‖ ≤ ‖Φ‖ * B := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g b c Φ).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((appCcRS (I := I) (M := M) g a b c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
      (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    calc riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x)
        ≤ riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) * B ^ 2 :=
          mul_le_mul_of_nonneg_left (hW x)
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g b c x _)
      _ = B ^ 2 * riemannianFiberNormSq (I := I) (M := M) g b c x (Φ.toSection x) := by ring
  have hsq : ‖appCcRS (I := I) (M := M) g a b c Φ W‖ ^ 2 ≤ ‖Φ‖ ^ 2 * B ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g a c
      (appCcRS (I := I) (M := M) g a b c Φ W) F hF_int hpt
    rw [hF_def, MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g b c Φ
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    nlinarith [h1]
  have hrhs_nn : 0 ≤ ‖Φ‖ * B := mul_nonneg (norm_nonneg _) hB
  refine le_of_sq_le_sq ?_ hrhs_nn
  rw [mul_pow]
  exact hsq

set_option linter.unusedSectionVars false in
theorem appCc_l2_le_of_pointwise_fiberNormSq_bound_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (B : ℝ) (hB : 0 ≤ B)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ.toSection x) ≤ B ^ 2) :
    ‖appCc (I := I) (M := M) g r s Φ W‖ ≤ B * ‖W‖ := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g r s Φ W]
  exact appCcRS_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g 0 r s Φ W B hB hΦ

set_option linter.unusedSectionVars false in
theorem appCc_l2_le_of_pointwise_fiberNormSq_bound_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) ≤ B ^ 2) :
    ‖appCc (I := I) (M := M) g r s Φ W‖ ≤ ‖Φ‖ * B := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g r s Φ W]
  exact appCcRS_l2_le_of_pointwise_fiberNormSq_bound_right (I := I) (M := M) g 0 r s Φ W B hB hW

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_iteratedCovGrad_fiberNormSq_le_smoothCcToTensorHs_sq
    (g₀ : SmoothRiemannianMetric I M) (q m : ℕ)
    (h_super : 2 * (2 * (Module.finrank ℝ E / 2 + 1) + q) ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T₀ : SmoothCcTensor g₀ 0 2) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x) ≤
        C ^ 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T₀‖ ^ 2 := by
  classical
  set K : ℕ := Module.finrank ℝ E / 2 + 1 with hK_def
  have hK_super : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK_def]; omega
  set N : ℕ := 2 * (2 * K + q) with hN_def
  have hNm : N ≤ m := by rw [hN_def, hK_def]; omega
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ 0 (2 + q) K 0 hK_super
  obtain ⟨Cit, hCit_nn, hCit⟩ :=
    iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 2 q (2 * K)
  obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * K + q)
  obtain ⟨Cspec, hCspec_nn, hCspec⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ N
  refine ⟨Cemb * Cit * Crev * Cspec, by positivity, fun T₀ x => ?_⟩
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
  set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T₀‖ with hNm_def
  have hNm_nn : 0 ≤ Nm := norm_nonneg _
  have hbridge : ∀ σ : ℝ, smoothCcToTensorHs (I := I) (M := M) g₀ σ T₀ =
      ccSpectralEmbed (I := I) (M := M) g₀ σ T₀ :=
    fun σ => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
      (funext (fun i => rfl))
  have hspecmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (N : ℝ) T₀‖ ≤ Nm := by
    rw [hNm_def, hbridge (N : ℝ), hbridge (m : ℝ)]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T₀
    exact_mod_cast hNm
  have hsumcongr : (∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
        tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j T₀).toFun) =
      ∑ j ∈ Finset.range (N + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ := by
    rw [hN_def]
    exact Finset.sum_congr rfl
      (fun j _ => (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j T₀)).symm)
  have hrev : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) T₀‖ ≤
      Crev * (Cspec * Nm) := by
    refine le_trans (hCrev T₀) ?_
    rw [hsumcongr]
    refine mul_le_mul_of_nonneg_left
      (le_trans (hCspec T₀) (mul_le_mul_of_nonneg_left hspecmono hCspec_nn)) hCrev_nn
  have hit : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
        (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q T₀)‖ ≤
      Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) T₀‖ := hCit T₀
  have hemb := hCemb (iteratedCovGrad (I := I) g₀ 0 2 q T₀) x
  have hnorm : ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ≤
      (Cemb * Cit * Crev * Cspec) * Nm := by
    calc ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖
        ≤ Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
            (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q T₀)‖ := hemb
      _ ≤ Cemb * (Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            (2 * K + q) T₀‖) := mul_le_mul_of_nonneg_left hit hCemb_pos.le
      _ ≤ Cemb * (Cit * (Crev * (Cspec * Nm))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrev hCit_nn) hCemb_pos.le
      _ = (Cemb * Cit * Crev * Cspec) * Nm := by ring
  have hns : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x) =
      ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ^ 2 := by
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        (iteratedCovGrad (I := I) g₀ 0 2 q T₀),
      Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)]
  rw [hns]
  have hsq_le : ‖(iteratedCovGrad (I := I) g₀ 0 2 q T₀).toSection x‖ ^ 2 ≤
      ((Cemb * Cit * Crev * Cspec) * Nm) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  refine le_trans hsq_le ?_
  rw [hNm_def, mul_pow]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem deTurckPrincipalCometricCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨Kslot, hKslot_nn, hKslot⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), Kslot j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hKslot_nn j), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hC g₁ i x)
  have hjetL2 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      C i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
    refine le_trans key (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
    exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm
  refine le_trans hjetL2 ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
  intro j hj
  have hj_le : j ≤ a :=
    le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
  exact hKslot g₁ P hδ_le hδ htie hPball j hj_le

end DifferentialGeometry.Integral.Connection

end
