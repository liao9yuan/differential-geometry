import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth) in

theorem ccSpectralEmbed_eigenvectorSmooth_norm_sq
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ := by
  classical
  rw [ccSpectralEmbed_norm_sq_eq_tsum]
  have hcoeff : ∀ j : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (eigenvectorSmooth (I := I) (M := M) g 0 2 i)) j =
      (if j = i then (1 : ℝ) else 0) := by
    intro j
    have hk := tensorL2Coeff_ofCompact_eigenSmooth (I := I) (M := M) g j i
    rw [← hk]
    congr 1
  simp_rw [hcoeff]
  rw [tsum_congr (fun j => by
    rw [show (if j = i then (1 : ℝ) else 0) ^ 2 = (if j = i then (1 : ℝ) else 0) by
      split <;> simp, mul_ite, mul_one, mul_zero])]
  rw [tsum_ite_eq i]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth) in

theorem eigenvectorSmooth_toHs_norm_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
  classical
  obtain ⟨C, hC_nn, hbridge⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g (2 * k)
  refine ⟨C, hC_nn, fun i => ?_⟩
  set ei := eigenvectorSmooth (I := I) (M := M) g 0 2 i with hei_def
  rw [tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (2 * k) ei]
  refine le_trans (hbridge ei) ?_
  have hspec : ‖ccSpectralEmbed (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) ei‖ =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
    have hsq := ccSpectralEmbed_eigenvectorSmooth_norm_sq (I := I) (M := M) g
      ((2 * (2 * k) : ℕ) : ℝ) i
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    have hw : tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) =
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k)) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show ((2 * (2 * k) : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) * 2 by push_cast; ring,
        Real.rpow_mul hbase_nn, Real.rpow_natCast, Real.rpow_two]
    rw [hw] at hsq
    have hnn_pow : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
      pow_nonneg hbase_nn _
    nlinarith [norm_nonneg (ccSpectralEmbed (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) ei),
      hsq, hnn_pow]
  rw [hspec]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
