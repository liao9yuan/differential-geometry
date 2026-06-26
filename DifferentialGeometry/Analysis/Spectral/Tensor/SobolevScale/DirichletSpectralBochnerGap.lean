import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

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
            C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u‖ ^ 2 :=
  sorry

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
