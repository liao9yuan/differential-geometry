import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
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
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
  sorry

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
