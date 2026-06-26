import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private theorem tensorL2Inner_eq_tsum_l2Coeff_cross
    (g₀ : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * t) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S))]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m t]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  rw [mul_pow, ← pow_mul, mul_comm t 2, (even_two_mul t).neg_pow L]

private theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set U : SmoothCcTensor g₀ 0 2 := rawTensorConnLapIter (I := I) g₀ 0 2 i S with hU_def
  have hnorm_sq : ‖covGrad (I := I) (M := M) g₀ 0 2 U‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun := by
    rw [SmoothCcTensor.norm_def (covGrad (I := I) (M := M) g₀ 0 2 U)]
    exact tensorL2Norm_sq_toFun (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 U)
  rw [hnorm_sq,
    tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g₀ 2 U]
  have hraw_eq : rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
      rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S := by
    rw [hU_def, rawTensorConnLapIter_succ]
  rw [hraw_eq, tensorL2Inner_eq_tsum_l2Coeff_cross (I := I) (M := M) g₀
    (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S) U, hU_def]
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m (i + 1),
    tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow, (odd_two_mul_add_one i).neg_pow L]
  ring

private theorem smoothCcToTensorHs_rawTensorConnLapSmooth_le_self
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set lam : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) i with hlam_def
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i
    with hc_def
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := norm_nonneg _
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
      (I := I) (M := M) i
  have hLHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)) i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ h_compact T i]
    rw [show (- lam i * c i) ^ 2 = (lam i) ^ 2 * (c i) ^ 2 by ring]
    ring
  have hRHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (σ + 2) * (c i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2]
    have hw2 : tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) = (1 + lam i) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw2]
  have hsummable_RHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2) := by
    have hw := (ccSpectralEmbed (I := I) (M := M) g₀ (σ + 2) T).weighted_summable
    refine hw.congr (fun i => ?_)
    rw [ccSpectralEmbed_coeff,
      show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
    exact hRHS_term i
  have hsummable_LHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_RHS
    · have := tensorSobolevWeight_pos (I := I) (M := M) i σ
      have := hlam_nn i
      positivity
    · have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
        have := hlam_nn i; nlinarith
      have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def]
      exact hLHS_term i]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def,
        show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
      exact hRHS_term i]
    refine Summable.tsum_le_tsum (fun i => ?_) hsummable_LHS hsummable_RHS
    have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
      have := hlam_nn i; nlinarith
    have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  exact le_of_sq_le_sq hsq hnn

private theorem spectralModeMass_succ_le_smoothCcToTensorHs_succ_normSq
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) (u : SmoothCcTensor g₀ 0 2) :
    ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 u) m) ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u‖ ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcomp
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u =
      ccSpectralEmbed (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u :=
    tensorHs.ext (funext (fun i => rfl))
  rw [hembed_eq, ccSpectralEmbed_norm_sq_eq_tsum]
  have hweight_eq : ∀ m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) := by
    intro m
    unfold tensorSobolevWeight
    rw [show ((n : ℕ) : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hRHS_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        tensorSobolevWeight (I := I) (M := M) m (((n : ℕ) : ℝ) + 1) *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 u) m) ^ 2) :=
    (ccSpectralEmbed (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u).weighted_summable
  have hLHS_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 u) m) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hRHS_summable
    · intro m
      have := tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      rw [hweight_eq m]
      have hL_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL_nn hle (n + 1)) (sq_nonneg _)
  refine Summable.tsum_le_tsum (fun m => ?_) hLHS_summable hRHS_summable
  rw [hweight_eq m]
  have hL_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
    tensor_lambda_nonneg (I := I) (M := M) m
  have hle : TensorEigenIdx.lambda (I := I) (M := M) m ≤
      1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL_nn hle (n + 1)) (sq_nonneg _)

private theorem covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd_local
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ ^ 2 := by
    rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ i S,
      ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg c)
    · have hsummable := (ccSpectralEmbed (I := I) (M := M) g₀
        ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
      refine Summable.of_nonneg_of_le ?_ ?_ hsummable
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        positivity
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
            1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
        have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast]
        rw [hweight_eq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem norm_iteratedCovGrad_comp_local
    (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i) (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

private theorem norm_iteratedCovGrad_order_eq_local
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 2 k
  refine ⟨((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)), by positivity, fun S => ?_⟩
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have heq : tensorL2Norm (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ :=
      (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀ (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).trans
        (SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).symm
    rw [heq]
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g₀ i S
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ ≤ Nspec := by
      rw [hNspec_def, ← hembed_eq]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
      have : (2 * i : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        ((k + 1 : ℕ) : ℝ) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cg * (((k + 1 : ℕ) : ℝ) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgj := hCg j hj2k S
    have heqj : tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
    rw [heqj] at hgj
    exact le_trans hgj (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1), Cg * (((k + 1 : ℕ) : ℝ) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (((k + 1 : ℕ) : ℝ) * Nspec)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)) * Nspec := by push_cast; ring

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd_local
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 3 k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
  have hcommfam : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => exists_rawConnLapIter_covGrad_commutator_l2Norm_le (I := I) (M := M) g₀ 2 i
  set Ccomm : ℕ → ℝ := fun i => Classical.choose (hcommfam i) with hCcomm_def
  have hCcomm_nn : ∀ i, 0 ≤ Ccomm i := fun i => (Classical.choose_spec (hcommfam i)).1
  have hCcomm : ∀ i, ∀ S : SmoothCcTensor g₀ 0 2,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        Ccomm i * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => (Classical.choose_spec (hcommfam i)).2
  set Ccommsum : ℝ := ∑ i ∈ Finset.range (k + 1), Ccomm i with hCcommsum_def
  have hCcommsum_nn : 0 ≤ Ccommsum :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  refine ⟨Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven), by positivity,
    fun S => ?_⟩
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def, ← hembed_eq]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this
  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCeven_nn
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)
  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    refine mul_le_mul_of_nonneg_left ?_ hClow_nn
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)
  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 3 i
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (1 + Ccomm i * Ceven) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S) =
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤ Nspec := by
      refine le_trans
        (covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd_local (I := I) (M := M) g₀ i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i S
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          Ccomm i * Ceven * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
          ≤ Ccomm i * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := hcomm
        _ ≤ Ccomm i * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ Ccomm i * (Ceven * Nspec) :=
            mul_le_mul_of_nonneg_left heven_le (hCcomm_nn i)
        _ = Ccomm i * Ceven * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
        ≤ Nspec + Ccomm i * Ceven * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + Ccomm i * Ceven) * Nspec := by ring
  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ ≤
      Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have h := norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ 2 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 2 S =
          iteratedCovGrad (I := I) g₀ 0 2 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 2 * k) S‖ :=
        norm_iteratedCovGrad_order_eq_local (I := I) (M := M) g₀ 2 (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard := hCgard (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 2 S)
    have hgard' : ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        Cgard * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have heq1 : tensorL2Norm (I := I) (M := M) g₀ 0 (3 + 2 * k)
            (iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
              (covGrad (I := I) (M := M) g₀ 0 2 S)).toFun =
          ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ :=
        DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
          (iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S))
      rw [← heq1]
      refine le_trans hgard ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCgard_nn
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S))
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖
          ≤ ∑ i ∈ Finset.range (k + 1), (1 + Ccomm i * Ceven) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1), (Nspec + (Ccomm i) * (Ceven * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            rw [hCcommsum_def]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖
        ≤ Cgard * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := hgard'
      _ ≤ Cgard * ((((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by ring
  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖
      ≤ Clow * Nspec + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven)) * Nspec := by ring

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general_local
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_even_local (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd_local (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

private theorem iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 2),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (k + 2) u)‖ ^ 2 ≤
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 k
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 u))‖ ^ 2
        + C * (∑ a ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a u‖) ^ 2 :=
  sorry

private theorem spectralModeMass_base0
    (g₀ : SmoothRiemannianMetric I M) (u : SmoothCcTensor g₀ 0 2) :
    ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (0 + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 u) m) ^ 2 := by
  have hcov : iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u =
      covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 0 u) := by
    rw [rawTensorConnLapIter_zero]
    rfl
  rw [show ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u‖ ^ 2 by
      rw [SmoothCcTensor.norm_toL2], hcov]
  rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ 0 u]

private theorem spectralModeMass_base1
    (g₀ : SmoothRiemannianMetric I M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g₀ 0 2),
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) u)‖ ^ 2 ≤
        (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2)
        + C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
    iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower (I := I) (M := M) g₀ 0
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general_local (I := I) (M := M) g₀ 1
  refine ⟨Cstep * Csob ^ 2, by positivity, fun u => ?_⟩
  have hS := hCstep u
  have hbase0 :
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 0
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u))‖ ^ 2 =
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2 := by
    rw [iteratedCovGrad_zero,
      show rawTensorConnLapSmooth (I := I) g₀ 0 2 u =
        rawTensorConnLapIter (I := I) g₀ 0 2 1 u by rw [rawTensorConnLapIter_succ,
          rawTensorConnLapIter_zero],
      rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ 1 u]
  have hSobu := hCsob u
  set SUM := ∑ a ∈ Finset.range (0 + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 a u‖ with hSUM
  have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  set HN := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) u‖ with hHN
  have hHN_nn : (0 : ℝ) ≤ HN := norm_nonneg _
  have hSobidx : SUM ≤ Csob * HN := by
    have hh : ∑ a ∈ Finset.range (1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a u‖ ≤
        Csob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) u‖ := hSobu
    rw [hSUM, hHN, show (0 + 2) = (1 + 1) by ring]
    exact hh
  have hstep_sq : Cstep * SUM ^ 2 ≤ (Cstep * Csob ^ 2) * HN ^ 2 := by
    have h1 : SUM ^ 2 ≤ (Csob * HN) ^ 2 := pow_le_pow_left₀ hSUM_nn hSobidx 2
    calc Cstep * SUM ^ 2 ≤ Cstep * (Csob * HN) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hCstep_nn
      _ = (Cstep * Csob ^ 2) * HN ^ 2 := by ring
  calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) u)‖ ^ 2
      ≤ ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 0
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u))‖ ^ 2 + Cstep * SUM ^ 2 := hS
    _ = (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2) + Cstep * SUM ^ 2 := by rw [hbase0]
    _ ≤ (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (1 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2) + (Cstep * Csob ^ 2) * HN ^ 2 := by
        linarith [hstep_sq]

private theorem exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u)‖ ^ 2 ≤
          (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 u) m) ^ 2) +
            C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n, IH with
    | 0, _ =>
      refine ⟨0, le_refl _, fun u => ?_⟩
      rw [spectralModeMass_base0 (I := I) (M := M) g₀ u]
      simp
    | 1, _ => exact spectralModeMass_base1 (I := I) (M := M) g₀
    | (Nat.succ (Nat.succ N)), IH =>
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        iteratedCovGrad_l2NormSq_succ_le_rawConnLap_base_add_lower (I := I) (M := M) g₀ (N + 1)
      obtain ⟨Cih, hCih_nn, hCih⟩ := IH N (by omega)
      obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
        exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general_local (I := I) (M := M) g₀ (N + 2)
      refine ⟨Cstep * Csob ^ 2 + Cih, by positivity, fun u => ?_⟩
      have hS := hCstep u
      have hIH := hCih (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)
      have hHsh := smoothCcToTensorHs_rawTensorConnLapSmooth_le_self
        (I := I) (M := M) g₀ ((N : ℕ) : ℝ) u
      have hSobu := hCsob u
      have hLHSidx : (N + 1 + 2) = (N + 2 + 1) := by ring
      rw [hLHSidx] at hS
      have hTopShift :
          (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 1) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)) m) ^ 2) =
            ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 2 + 1) *
                (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 u) m) ^ 2 := by
        refine tsum_congr (fun m => ?_)
        rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) u m]
        set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL
        set c := tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 u) m with hc
        rw [show (- L * c) ^ 2 = L ^ 2 * c ^ 2 by ring,
          show N + 2 + 1 = (N + 1) + 2 by ring, pow_add]
        ring
      rw [hTopShift] at hIH
      have hHidx : ((N : ℕ) : ℝ) + 2 = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hHidx] at hHsh
      set A := ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (N + 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u))‖ ^ 2 with hA
      set TOPg := ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (N + 2 + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2 with hTOPg
      set SUM := (∑ a ∈ Finset.range ((N + 1) + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 a u‖) with hSUM
      set HN := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((N : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 u)‖ with hHN
      set HNu := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((N + 2 : ℕ) : ℝ) u‖ with hHNu
      have hSUM_nn : (0 : ℝ) ≤ SUM := Finset.sum_nonneg (fun a _ => norm_nonneg _)
      have hHN_nn : (0 : ℝ) ≤ HN := norm_nonneg _
      have hHNu_nn : (0 : ℝ) ≤ HNu := norm_nonneg _
      have hSob_le : SUM ≤ Csob * HNu := by
        have hSobu' : ∑ a ∈ Finset.range ((N + 2) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a u‖ ≤
              Csob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((N + 2 : ℕ) : ℝ) u‖ := hSobu
        rw [hSUM, hHNu, show ((N + 1) + 2) = ((N + 2) + 1) by ring]
        exact hSobu'
      have hIH_H : Cih * HN ^ 2 ≤ Cih * HNu ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hCih_nn
        exact pow_le_pow_left₀ hHN_nn hHsh 2
      have hStep_sq : Cstep * SUM ^ 2 ≤ (Cstep * Csob ^ 2) * HNu ^ 2 := by
        have h1 : SUM ^ 2 ≤ (Csob * HNu) ^ 2 := pow_le_pow_left₀ hSUM_nn hSob_le 2
        calc Cstep * SUM ^ 2 ≤ Cstep * (Csob * HNu) ^ 2 :=
              mul_le_mul_of_nonneg_left h1 hCstep_nn
          _ = (Cstep * Csob ^ 2) * HNu ^ 2 := by ring
      have hgoal : ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (N + 2 + 1) u)‖ ^ 2 ≤
          TOPg + (Cstep * Csob ^ 2 + Cih) * HNu ^ 2 := by
        calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (N + 2 + 1) u)‖ ^ 2
            ≤ A + Cstep * SUM ^ 2 := hS
          _ ≤ (TOPg + Cih * HN ^ 2) + Cstep * SUM ^ 2 := by linarith [hIH]
          _ ≤ TOPg + (Cstep * Csob ^ 2 + Cih) * HNu ^ 2 := by nlinarith [hIH_H, hStep_sq]
      exact hgoal

theorem exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u)‖ ^ 2 ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u‖ ^ 2 +
            Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_spectralModeMass_succ_add_lower (I := I) (M := M) g₀ n
  refine ⟨C, hC_nn, fun u => ?_⟩
  have hmass := spectralModeMass_succ_le_smoothCcToTensorHs_succ_normSq
    (I := I) (M := M) g₀ n u
  have hbound := hC u
  calc ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u)‖ ^ 2
      ≤ (∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (n + 1) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 u) m) ^ 2) +
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 := hbound
    _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u‖ ^ 2 +
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 := by
        have hMn_nn : 0 ≤ C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 :=
          mul_nonneg hC_nn (sq_nonneg _)
        linarith [hmass]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
