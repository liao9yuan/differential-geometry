import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem smoothCcToTensorHs_zero_norm_eq (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ =
      ‖SmoothCcTensor.toL2 X‖ := by
  classical
  have hnn_lhs : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ := norm_nonneg _
  have hnn_rhs : 0 ≤ ‖SmoothCcTensor.toL2 X‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ ^ 2 =
      ‖SmoothCcTensor.toL2 X‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ 0 X).coeff i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 X) i) ^ 2 by
      funext i
      rw [tensorSobolevWeight_zero, one_mul, smoothCcToTensorHs_coeff]]
    exact tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 X)
  nlinarith [hsq, hnn_lhs, hnn_rhs, sq_nonneg
    (‖smoothCcToTensorHs (I := I) (M := M) g₀ 0 X‖ - ‖SmoothCcTensor.toL2 X‖)]

theorem smoothCcToTensorHs_norm_order_congr (g₀ : SmoothRiemannianMetric I M)
    {σ σ' : ℝ} (h : σ = σ') (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' T‖ := by
  subst h; rfl

theorem smoothCcToTensorHs_inner_order_congr (g₀ : SmoothRiemannianMetric I M)
    {σ σ' : ℝ} (h : σ = σ') (S T : SmoothCcTensor g₀ 0 2) :
    (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ σ S)
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T) : ℝ) =
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ σ' S)
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ' T) : ℝ) := by
  subst h; rfl

private lemma weight_natCast (g₀ : SmoothRiemannianMetric I M)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) (n : ℕ) :
    tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]

private lemma smoothCcToTensorHs_rawConnLap_coeff (g₀ : SmoothRiemannianMetric I M)
    (σ : ℝ) (T₀ : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T₀).coeff i := by
  classical
  have hdiag := tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) T₀ i 1
  have hiter1 : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 1 T₀ =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero]
  have hsub : SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 T₀) =
      SmoothCcTensor.toL2 T₀ -
        SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀) := by
    unfold oneMinusConnLapSmooth
    exact map_sub _ _ _
  rw [hiter1, hsub] at hdiag
  rw [tensorL2Coeff_eq_inner, inner_sub_right, ← tensorL2Coeff_eq_inner,
    ← tensorL2Coeff_eq_inner] at hdiag
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [pow_one] at hdiag
  linear_combination -hdiag

private lemma smoothCcToTensorHs_two_le_connLap_add (g₀ : SmoothRiemannianMetric I M)
    (T₀ : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
  classical
  have hsum2 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).weighted_summable
  have hsum0 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).weighted_summable
  have hsum1 : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).weighted_summable
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ^ 2 +
        2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    have hterm : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2 +
          2 * (tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2) := by
      intro i
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have hcoeff2 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i := rfl
      rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ (0 : ℝ) T₀ i,
        weight_natCast, weight_natCast, tensorSobolevWeight_zero, hcoeff2]
      have hcoeff0 : (smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) T₀).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i := rfl
      rw [hcoeff0]
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i
      set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i
      have hsq_ci : 0 ≤ ci ^ 2 := sq_nonneg _
      nlinarith [hsq_ci, hlam_nn]
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀).coeff i) ^ 2)
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2 +
            2 * (tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2)) :=
          Summable.tsum_le_tsum hterm hsum2 (hsum0.add (hsum1.mul_left 2))
      _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)).coeff i) ^ 2) +
            2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀).coeff i) ^ 2 := by
          rw [Summable.tsum_add hsum0 (hsum1.mul_left 2), tsum_mul_left]
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
    norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  nlinarith [hsq, hs2, mul_nonneg (mul_nonneg hsqrt2_nn hb_nn) hc_nn]

lemma delta_nonneg_of_ball_gFibreOpBound [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {δ : ℝ}
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    0 ≤ δ := by
  have hzero_ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
    have h0 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) =
          (0 : TensorL2 0 2 g₀) from map_zero _,
        tensorL2Coeff_eq_inner, inner_zero_right]
    rw [h0, norm_zero]
    exact hR₀
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
    haveI : Nontrivial (TangentSpace I x₀) := by
      have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
        have hrk : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
        rw [hrk]; exact Nat.pos_of_ne_zero (NeZero.ne _)
      exact Module.nontrivial_of_finrank_pos hfr
    exact exists_ne 0
  have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
  have hbound := hδ_fibre (0 : SmoothCcTensor g₀ 0 2) hzero_ball x₀ v v
  have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
  have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x₀ v v| :=
    abs_nonneg _
  by_contra hδc
  have hδc' : δ < 0 := lt_of_not_ge hδc
  have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
    have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
      mul_neg_of_neg_of_pos hδc' hsqrt_pos
    exact mul_neg_of_neg_of_pos h1 hsqrt_pos
  linarith [le_trans habs_nn hbound]

private theorem arm_realize_Hs_norm_zero_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by
  classical
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hδ_nn : 0 ≤ δ := delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn h1δ.le
  have hCE_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    deTurckArmFibreConst_nonneg _
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ 1
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      (Real.sqrt 2 + Real.sqrt Cgap), by positivity, fun T₀ hball => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
  set armT := deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀ with harm_def
  have hHs0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) armT‖ = ‖armT‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
  have h615 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (armT.toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((iteratedCovGrad (I := I) g₀ 0 2 2 T₀).toSection x) := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricArm_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ T₀ y)
      (fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w)
      hδ_lt1 hδ_nn (hδ_fibre T₀ hball) T₀ x
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 T₀).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)).const_mul _
  have hsq1 : ‖armT‖ ^ 2 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 2 armT _ hFint h615
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have harm_le : ‖armT‖ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ := by
    have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ := by positivity
    refine le_of_sq_le_sq ?_ hrhs_nn
    have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖) ^ 2 =
        deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) ^ 2 *
          ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ^ 2 := by ring
    rw [hexp, sq_deTurckArmFibreConst]
    exact hsq1
  have hgap1 := hgap T₀
  rw [SmoothCcTensor.norm_toL2] at hgap1
  have hgap' : ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ +
        Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
    have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ :=
      norm_nonneg _
    have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
      norm_nonneg _
    have hsqrt_nn : 0 ≤ Real.sqrt Cgap := Real.sqrt_nonneg _
    refine le_of_sq_le_sq ?_ (by positivity)
    have hsC : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
    nlinarith [hgap1, mul_nonneg (mul_nonneg hsqrt_nn hb_nn) hc_nn]
  have htwo1 : ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ := rfl
  have hcast2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  have htwo := smoothCcToTensorHs_two_le_connLap_add (I := I) (M := M) g₀ T₀
  have hcast1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  have hCEκ_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
    mul_nonneg hCE_nn hκ_nn
  have hjets : ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by
    rw [← hcast1]
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 2 T₀‖
        = ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) T₀‖ := htwo1
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T₀‖ +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ :=
          hgap'
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) T₀‖ +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
          rw [hcast2]
      _ ≤ (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖) +
            Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by
          linarith [htwo]
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            (Real.sqrt 2 + Real.sqrt Cgap) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ := by ring
  have hchain : ‖armT‖ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖) :=
    le_trans harm_le (mul_le_mul_of_nonneg_left hjets hCEκ_nn)
  rw [hHs0]
  calc ‖armT‖
      ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          (‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            (Real.sqrt 2 + Real.sqrt Cgap) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖) := hchain
    _ = deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
        deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            (Real.sqrt 2 + Real.sqrt Cgap) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 1) T₀‖ := by ring

private lemma smoothCcToTensorHs_connLap_shift_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ +
        Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := by
  classical
  have hsumA : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable
  have hsumB : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable
  have hsumC : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).weighted_summable
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 +
        2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    have hterm : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
          2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2) := by
      intro i
      have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
        weight_natCast (I := I) (M := M) g₀ i (k + 2),
        weight_natCast (I := I) (M := M) g₀ i k,
        weight_natCast (I := I) (M := M) g₀ i (k + 1)]
      set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
      set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i with hci_def
      have hc2 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i = ci := rfl
      have hc0 : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
      rw [hc2, hc0]
      have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
      have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
      have e1 : (1 + lam) ^ (k + 1) = (1 + lam) ^ k * (1 + lam) := by rw [pow_succ]
      rw [e2, e1]
      nlinarith [hbase_nn, sq_nonneg ci, hlam_nn,
        mul_nonneg hbase_nn (sq_nonneg ci),
        mul_nonneg (mul_nonneg hbase_nn (sq_nonneg ci)) hlam_nn]
    calc (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 2 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i) ^ 2)
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2 +
            2 * (tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2)) :=
          Summable.tsum_le_tsum hterm hsumA (hsumB.add (hsumC.mul_left 2))
      _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i ((k : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).coeff i) ^ 2) +
            2 * ∑' i, tensorSobolevWeight (I := I) (M := M) i ((k + 1 : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u).coeff i) ^ 2 := by
          rw [Summable.tsum_add hsumB (hsumC.mul_left 2), tsum_mul_left]
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine le_of_sq_le_sq ?_ (by positivity)
  nlinarith [hsq, hs2, mul_nonneg (mul_nonneg hsqrt2_nn hb_nn) hc_nn]

private lemma smoothCcToTensorHs_rawConnLap_order_le (g₀ : SmoothRiemannianMetric I M)
    (k : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := by
  classical
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ := norm_nonneg _
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)).weighted_summable)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).weighted_summable)
    have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    rw [smoothCcToTensorHs_rawConnLap_coeff (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u i,
      weight_natCast (I := I) (M := M) g₀ i k, weight_natCast (I := I) (M := M) g₀ i (k + 2)]
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    set ci := (smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) u).coeff i with hci_def
    have hc : (smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) u).coeff i = ci := rfl
    rw [hc]
    have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ k := by positivity
    have e2 : (1 + lam) ^ (k + 2) = (1 + lam) ^ k * (1 + lam) ^ 2 := by rw [pow_add]
    rw [e2]
    nlinarith [hbase_nn, sq_nonneg ci, hlam_nn, mul_nonneg hbase_nn (sq_nonneg ci)]
  exact le_of_sq_le_sq hsq hnn

private lemma smoothCcToTensorHs_norm_mono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w := tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w := tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

private lemma iteratedCovGrad_le_connLap_add (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Cj * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower (I := I) (M := M) g₀ (k + 1)
  refine ⟨Real.sqrt 2 + Real.sqrt Cgap, by positivity, fun S => ?_⟩
  have hgapS := hgap S
  have hJeq : SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 1 + 1) S) =
      SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S) := rfl
  rw [hJeq, SmoothCcTensor.norm_toL2] at hgapS
  have hcast_succ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hb_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hc_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := norm_nonneg _
  have hjet_two : ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
        Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
    have hsqrt_nn : 0 ≤ Real.sqrt Cgap := Real.sqrt_nonneg _
    have hsC : Real.sqrt Cgap ^ 2 = Cgap := Real.sq_sqrt hCgap_nn
    rw [← hcast_succ]
    refine le_of_sq_le_sq ?_ (by positivity)
    nlinarith [hgapS, hsC, mul_nonneg (mul_nonneg hsqrt_nn
      (norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ (((k + 1 : ℕ) : ℝ) + 1) S)))
      hc_nn, hcast_succ, hb_nn, hc_nn]
  have hshift := smoothCcToTensorHs_connLap_shift_le (I := I) (M := M) g₀ k S
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 (k + 2) S‖
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 2 : ℕ) : ℝ) S‖ +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ :=
        hjet_two
    _ ≤ (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          Real.sqrt 2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖) +
          Real.sqrt Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by
        linarith [hshift]
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          (Real.sqrt 2 + Real.sqrt Cgap) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k + 1 : ℕ) : ℝ) S‖ := by ring

private lemma arm_l2_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := by
  classical
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  have h615 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricArm_le (I := I) (M := M) g₀ g₁ h htie
      hδ_lt hδ_nn hδ S x
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 4
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)).const_mul _
  have hsq1 : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 2 (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) _ hFint h615
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S)
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ :=
    mul_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn) (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
      ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖) ^ 2 =
      deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) ^ 2 *
        ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ^ 2 := by ring
  rw [hexp, sq_deTurckArmFibreConst]
  exact hsq1

private lemma arm_covGrad_slotExtend_l2_le (g₀ g₁ : SmoothRiemannianMetric I M)
    {κ : ℝ} (hκ_nn : 0 ≤ κ)
    (hC : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖appCc (I := I) (M := M) g₀ 5 3
        (slotExtend (I := I) (M := M) g₀ 4 2 (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * κ *
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := by
  classical
  set C := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hC_def
  set W := iteratedCovGrad (I := I) g₀ 0 2 3 S with hW_def
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) W).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 5 x (W.toSection x) := by
    intro x
    refine le_trans (riemannianFiberNormSq_appCc_slotExtend_le (I := I) (M := M) g₀ 4 2 C W x) ?_
    exact mul_le_mul_of_nonneg_right (hC x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 5 x _)
  have hFint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 5 x (W.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 5 W).const_mul _
  have hsq : ‖appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) W‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * κ ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g₀ 0 3
      (appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) W) _ hFint hpt
    rw [MeasureTheory.integral_const_mul] at h1
    have hbridge := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 5 W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * κ * ‖W‖ :=
    mul_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn) (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs_nn
  have hexp : (deTurckArmFibreConst (Module.finrank ℝ E) * κ * ‖W‖) ^ 2 =
      deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * κ ^ 2 * ‖W‖ ^ 2 := by ring
  rw [hexp, sq_deTurckArmFibreConst]
  exact hsq

private theorem arm_commutator_Hs_tame [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ CEcomm : ℕ → ℝ, (∀ j, 0 ≤ CEcomm j) ∧
      ∀ (j : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (S : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)) S) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball))
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 S))‖ ≤
          CEcomm j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ :=
  sorry

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem arm_covGrad_coeffLower_l2_tame [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (S : SmoothCcTensor g₀ 0 2),
        ‖appCc (I := I) (M := M) g₀ 4 3
            (covGrad (I := I) (M := M) g₀ 4 2
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball))))
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
          Cgrad * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
  classical
  letI inst03 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst23 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  obtain ⟨Cpo, hCpo_nn, hCpo⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨Cenv, hCenv_nn, hCenv⟩ :=
    norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one (I := I) (M := M) g₀
  have hm_super : 2 * (2 * (Module.finrank ℝ E / 2 + 1) + 1) ≤ a + 2 := by omega
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_iteratedCovGrad_fiberNormSq_le_smoothCcToTensorHs_sq (I := I) (M := M) g₀ 1 (a + 2) hm_super
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hδ_nn : 0 ≤ δ := delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hδ_half : δ < 1 / 2 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1 / 2)
  set R : ℝ := Cq * R₀ with hR_def
  have hR_nn : 0 ≤ R := mul_nonneg hCq_nn hR₀
  set Bsq : ℝ := Cpo 1 * ((Module.finrank ℝ E : ℝ) ^ 2 + (Cenv * (1 + R)) ^ 2) with hBsq_def
  have hBsq_nn : 0 ≤ Bsq := mul_nonneg (hCpo_nn 1) (by positivity)
  set B : ℝ := Real.sqrt Bsq with hB_def
  have hB_nn : 0 ≤ B := Real.sqrt_nonneg _
  have hBsqeq : B ^ 2 = Bsq := Real.sq_sqrt hBsq_nn
  refine ⟨B * (1 + Cj0), mul_nonneg hB_nn (by linarith [hCj0_nn]), fun T₀ hball S => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) with hg₁_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w :=
    fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) y v w
  have hδC : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hHsle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ ≤ R₀ := by
    rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by push_cast; ring) T₀]
    exact hball
  have hjet_x : ∀ x : M, ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R := by
    intro x
    have hc2 := hCq T₀ x
    have hrfns_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x) ≤ R ^ 2 := by
      refine le_trans hc2 ?_
      rw [hR_def, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hHsle 2) (sq_nonneg Cq)
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (iteratedCovGrad (I := I) g₀ 0 2 1 T₀)]
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x))
        ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hrfns_le
      _ = R := Real.sqrt_sq hR_nn
  have hΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 3 x
      ((covGrad (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤ B ^ 2 := by
    intro x
    have hperord := hCpo g₁ 1 x
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hperord
    have hj0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 :=
      riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T₀ hδ_half hδ_nn htie hδC x
    have hj1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        (Cenv * (1 + R)) ^ 2 := by
      have henv := hCenv g₁ T₀ hδ_half hδ_nn htie hδC x hR_nn (hjet_x x)
      rw [pow_one, norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
        (iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁))] at henv
      have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 3 x
        ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)
      have key : riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
          (Cenv * (1 + R)) ^ 2 := by
        nlinarith [henv, Real.sq_sqrt hnn, Real.sqrt_nonneg
          (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
            ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)),
          mul_nonneg hCenv_nn (by linarith [hR_nn] : (0 : ℝ) ≤ 1 + R)]
      exact key
    refine le_trans hperord ?_
    rw [hBsqeq, hBsq_def]
    exact mul_le_mul_of_nonneg_left (add_le_add hj0 hj1) (hCpo_nn 1)
  refine le_trans (appCc_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀ 4 3
    (covGrad (I := I) (M := M) g₀ 4 2 (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) B hB_nn hΦ) ?_
  have hjet := hCj0 S
  have hdrop := smoothCcToTensorHs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
  have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
  have hΔ0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    rw [← hdrop_congr]; exact hdrop
  have h2jet : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
      (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    nlinarith [hjet, hΔ0, hmono, hCj0_nn,
      norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S),
      mul_le_mul_of_nonneg_left hmono hCj0_nn]
  calc B * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖
      ≤ B * ((1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖) :=
        mul_le_mul_of_nonneg_left h2jet hB_nn
    _ = B * (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by ring

private lemma appCc_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (W₁ - W₂) =
      appCc (I := I) (M := M) g r s Φ W₁ - appCc (I := I) (M := M) g r s Φ W₂ := by
  have h : appCc (I := I) (M := M) g r s Φ (W₁ - W₂) +
      appCc (I := I) (M := M) g r s Φ W₂ = appCc (I := I) (M := M) g r s Φ W₁ := by
    rw [← appCc_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

private lemma deTurckPrincipalCometricArm_sub (g₀ g₁ : SmoothRiemannianMetric I M)
    (u v : SmoothCcTensor g₀ 0 2) :
    deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ (u - v) =
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u -
        deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ v := by
  rw [deTurckPrincipalCometricArm, deTurckPrincipalCometricArm, deTurckPrincipalCometricArm,
    iteratedCovGrad_sub, appCc_sub_right]

private lemma smoothCcToTensorHs_sub (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (u v : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (u - v) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ u - smoothCcToTensorHs (I := I) (M := M) g₀ σ v := by
  refine tensorHs.ext (funext fun i => ?_)
  simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff, smoothCcToTensorHs_coeff,
    map_add, map_neg, tensorL2Coeff_eq_inner, inner_add_right, inner_neg_right]

private lemma rawConnLap_oneMinusConnLap_comm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, rawTensorConnLapSmooth_sub]

set_option maxHeartbeats 1600000 in
theorem deTurckPrincipalCometricArm_realize_Hs_norm_succ_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hδ_nn : 0 ≤ δ :=
    delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  have hCE_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) := deTurckArmFibreConst_nonneg _
  set CEκ : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) with hCEκ_def
  have hCEκ_nn : 0 ≤ CEκ := by rw [hCEκ_def]; positivity
  obtain ⟨CEcomm, hCEcomm_nn, hCEcomm⟩ :=
    arm_commutator_Hs_tame (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cgrad, hCgrad_nn, hCgrad⟩ :=
    arm_covGrad_coeffLower_l2_tame (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  obtain ⟨Cj1, hCj1_nn, hCj1⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 1
  set Mbase : ℝ := CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) + CEκ * Cj0 + 1 with hMbase_def
  have hMbase_nn : 0 ≤ Mbase := by rw [hMbase_def]; positivity
  set ClowerFn : ℕ → ℝ := fun j => Mbase + ∑ i ∈ Finset.range j, CEcomm i with hClowerFn_def
  have hClowerFn_nn : ∀ j, 0 ≤ ClowerFn j := fun j => by
    rw [hClowerFn_def]
    exact add_nonneg hMbase_nn (Finset.sum_nonneg fun i _ => hCEcomm_nn i)
  refine ⟨fun m => ClowerFn (m + 1), fun m => hClowerFn_nn (m + 1), fun m T₀ hball => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) with hg₁_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := fun y v w =>
    tensorSectionRealizeMetric_inner (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) y v w
  have hδC : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hcoeff : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T₀) htie hδ_lt1 hδ_nn hδC x
  have hG : ∀ (j : ℕ) (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
        CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          ClowerFn j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 1 : ℕ) : ℝ) S‖ := by
    have hG0 : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            ClowerFn 0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := by
      intro S
      have hHs0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ =
          ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ := by
        rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, smoothCcToTensorHs_zero_norm_eq,
          SmoothCcTensor.norm_toL2]
      have harm := arm_l2_le (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T₀) htie
        hδ_lt1 hδ_nn hδC S
      have hjet := hCj0 S
      have hP0_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := norm_nonneg _
      have hQ1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      rw [hHs0]
      have hClf0 : ClowerFn 0 = Mbase := by
        rw [hClowerFn_def]; simp
      rw [hClf0]
      have hstep : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
          CEκ * (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖) :=
        le_trans harm (by
          have := mul_le_mul_of_nonneg_left hjet hCEκ_nn
          rwa [hCEκ_def] at this ⊢)
      have hMbase_ge : CEκ * Cj0 ≤ Mbase := by rw [hMbase_def]; nlinarith [hCEκ_nn, hCj0_nn]
      nlinarith [hstep, hMbase_ge, hP0_nn, hQ1_nn, hCEκ_nn, hCj0_nn,
        mul_nonneg hQ1_nn hCEκ_nn]
    have hG1 : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            ClowerFn 1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ := by
      intro S
      set C := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hCdef
      set Q := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ with hQ_def
      set P := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ with hP_def
      have hQ_nn : 0 ≤ Q := norm_nonneg _
      have hP_nn : 0 ≤ P := norm_nonneg _
      have ha2 := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad (I := I) (M := M) g₀ 0
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)
      simp only [oneMinusConnLapSmoothIter_zero] at ha2
      rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
          (show ((2 * 0 + 1 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) by norm_num)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S),
        SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at ha2
      have hA2jet := hCj0 S
      have hdrop := smoothCcToTensorHs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
      have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ = Q :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
      have hmono01 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤ Q :=
        smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
      have hΔ0_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤ Q := by rw [← hdrop_congr]; exact hdrop
      have hA2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤ (1 + Cj0) * Q := by
        have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
              Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := hA2jet
        nlinarith [h1, hΔ0_le, hmono01, hCj0_nn, hQ_nn,
          mul_le_mul_of_nonneg_left hmono01 hCj0_nn]
      have ha_bound : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
          CEκ * (1 + Cj0) * Q := by
        have harm := arm_l2_le (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T₀) htie
          hδ_lt1 hδ_nn hδC S
        calc ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖
            ≤ CEκ * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := harm
          _ ≤ CEκ * ((1 + Cj0) * Q) := mul_le_mul_of_nonneg_left hA2_le hCEκ_nn
          _ = CEκ * (1 + Cj0) * Q := by ring
      have hcov3 : covGrad (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          iteratedCovGrad (I := I) g₀ 0 2 3 S :=
        (iteratedCovGrad_succ g₀ 0 2 2 S).symm
      have hcov : covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) =
          appCc (I := I) (M := M) g₀ 4 3 (covGrad (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) +
            appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 3 S) := by
        rw [deTurckPrincipalCometricArm, ← hCdef, covGrad_appCc_eq, hcov3]
      have hgrad := hCgrad T₀ hball S
      have hgrad_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ = Q :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
      rw [hgrad_congr] at hgrad
      have hprinc := arm_covGrad_slotExtend_l2_le (I := I) (M := M) g₀ g₁ hκ_nn hcoeff S
      have hA3jet := hCj1 S
      have hA3_le : ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ ≤ P + Cj1 * Q := hA3jet
      have hb_bound : ‖covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * P + (Cgrad + CEκ * Cj1) * Q := by
        rw [hcov]
        refine le_trans (norm_add_le _ _) ?_
        have hprinc' : ‖appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖ ≤ CEκ * P + CEκ * Cj1 * Q := by
          calc ‖appCc (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
                (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖
              ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := hprinc
            _ = CEκ * ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := by rw [hCEκ_def]
            _ ≤ CEκ * (P + Cj1 * Q) := mul_le_mul_of_nonneg_left hA3_le hCEκ_nn
            _ = CEκ * P + CEκ * Cj1 * Q := by ring
        have hdist : Cgrad * Q + (CEκ * P + CEκ * Cj1 * Q) =
            CEκ * P + (Cgrad + CEκ * Cj1) * Q := by ring
        linarith [hgrad, hprinc', hdist]
      have hClf1_ge : CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) ≤ ClowerFn 1 := by
        have h1 : Mbase ≤ ClowerFn 1 := by
          simp only [hClowerFn_def, Finset.sum_range_one]
          linarith [hCEcomm_nn 0]
        have h2 : CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) ≤ Mbase := by
          rw [hMbase_def]; linarith [mul_nonneg hCEκ_nn hCj0_nn]
        linarith [h1, h2]
      set α := CEκ * (1 + Cj0) with hα_def
      set β := Cgrad + CEκ * Cj1 with hβ_def
      have hα_nn : 0 ≤ α := mul_nonneg hCEκ_nn (by linarith [hCj0_nn])
      have hβ_nn : 0 ≤ β := add_nonneg hCgrad_nn (mul_nonneg hCEκ_nn hCj1_nn)
      have ha_sq : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ^ 2 ≤ (α * Q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ha_bound 2
      have hb_sq : ‖covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ^ 2 ≤
          (CEκ * P + β * Q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb_bound 2
      have hfinal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤ CEκ * P + (α + β) * Q := by
        refine le_of_sq_le_sq ?_
          (add_nonneg (mul_nonneg hCEκ_nn hP_nn) (mul_nonneg (add_nonneg hα_nn hβ_nn) hQ_nn))
        rw [ha2]
        nlinarith [ha_sq, hb_sq,
          mul_nonneg (mul_nonneg (mul_nonneg hCEκ_nn hα_nn) hP_nn) hQ_nn,
          mul_nonneg (mul_nonneg hα_nn hβ_nn) (mul_nonneg hQ_nn hQ_nn)]
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖
          ≤ CEκ * P + (α + β) * Q := hfinal
        _ ≤ CEκ * P + ClowerFn 1 * Q := by
            have hmul := mul_le_mul_of_nonneg_right hClf1_ge hQ_nn
            linarith [hmul]
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      match j, IH with
      | 0, _ => exact hG0
      | 1, _ => exact hG1
      | (i + 2), IH =>
        have ih := IH i (by omega)
        intro S
        have hA3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)
        have hLarm : oneMinusConnLapSmooth (I := I) g₀ 0 2
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) -
              (rawTensorConnLapSmooth (I := I) g₀ 0 2
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) -
                deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) := by
          rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, deTurckPrincipalCometricArm_sub]
          abel
        rw [hA3, hLarm, smoothCcToTensorHs_sub]
        refine le_trans (norm_sub_le _ _) ?_
        have hih := ih (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        have hcommΔ := rawConnLap_oneMinusConnLap_comm (I := I) (M := M) g₀ S
        have hA3Δ := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)
        have hprinc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := by
          rw [hcommΔ, ← hA3Δ]
        have hA3S := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ (i + 1) S
        have hlower : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ)
              (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by
          rw [← hA3S]
        rw [hprinc, hlower] at hih
        have hE := hCEcomm i T₀ hball S
        have hcast_goal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 + 1 : ℕ) : ℝ) S‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
          smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
        rw [hcast_goal]
        have hQ3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
          norm_nonneg _
        have hCl_rec : ClowerFn i + CEcomm i ≤ ClowerFn (i + 2) := by
          have hsub : ∑ k ∈ Finset.range i, CEcomm k + CEcomm i ≤
              ∑ k ∈ Finset.range (i + 2), CEcomm k := by
            calc ∑ k ∈ Finset.range i, CEcomm k + CEcomm i
                = ∑ k ∈ Finset.range (i + 1), CEcomm k := (Finset.sum_range_succ CEcomm i).symm
              _ ≤ ∑ k ∈ Finset.range (i + 2), CEcomm k :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.range_mono (by omega)) (fun k _ _ => hCEcomm_nn k)
          simp only [hClowerFn_def]
          linarith [hsub]
        refine le_trans (add_le_add hih hE) ?_
        have hmul := mul_le_mul_of_nonneg_right hCl_rec hQ3_nn
        have hdist : ClowerFn i *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ +
            CEcomm i * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ =
            (ClowerFn i + CEcomm i) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by ring
        linarith [hmul, hdist]
  have hchild := hG (m + 1) T₀
  have hcast1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcast2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcast3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  rw [hcast1, hcast2, hcast3] at hchild
  exact hchild

theorem deTurckPrincipalCometricArm_realize_Hs_norm_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cl0, hCl0_nn, hbase⟩ :=
    arm_realize_Hs_norm_zero_le (I := I) (M := M) g₀ a hR₀ hδ_le hδ_fibre
  obtain ⟨Cls, hCls_nn, hstep⟩ :=
    deTurckPrincipalCometricArm_realize_Hs_norm_succ_le (I := I) (M := M) g₀ a
      ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun m => match m with
    | 0 => Cl0
    | (k + 1) => Cls k, fun m => ?_, fun m T₀ hball => ?_⟩
  · match m with
    | 0 => exact hCl0_nn
    | (k + 1) => exact hCls_nn k
  · match m with
    | 0 =>
      have h0 : ((0 : ℕ) : ℝ) = (0 : ℝ) := by norm_num
      have hb := hbase T₀ hball
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ h0
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) T₀)
      have hnormR := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ h0
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
      have hnormT := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (0 : ℝ) + 1 by rw [h0]) T₀
      rw [hnormL, hnormR, hnormT]
      exact hb
    | (k + 1) =>
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hs := hstep k T₀ hball
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hcast
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) T₀)
      have hnormR := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hcast
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
      have hnormT := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by rw [hcast]; ring) T₀
      rw [hnormL, hnormR, hnormT]
      exact hs

theorem deTurckPrincipalCometricArm_Hs_inner_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (φ : SmoothCcTensor g₀ 0 2),
        (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
            (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)) : ℝ) ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := by
  obtain ⟨Clower, hCl_nn, hnorm⟩ :=
    deTurckPrincipalCometricArm_realize_Hs_norm_le (I := I) (M := M) g₀ a
      ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hCl_nn, fun m T₀ hball φ => ?_⟩
  have hCS := real_inner_le_norm
    (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
    (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀))
  have hb := hnorm m T₀ hball
  have hφ_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := norm_nonneg _
  calc (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀)) : ℝ)
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ := hCS
    _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ *
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖) :=
        mul_le_mul_of_nonneg_left hb hφ_nn
    _ = deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ +
          Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := by ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
