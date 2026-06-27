import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
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

theorem deTurckPrincipalCometricArm_Hs_inner_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (φ T₀ : SmoothCcTensor g₀ 0 2),
          (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ σ φ)
              (smoothCcToTensorHs (I := I) (M := M) g₀ σ
                (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)) : ℝ) ≤
            (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖
                * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ φ‖ +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖
                * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ φ‖ :=
  sorry

theorem deTurckPrincipalCometricArm_Hs_norm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (T₀ : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ ≤
            (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖ := by
  obtain ⟨Clower, hCl, hpair⟩ :=
    deTurckPrincipalCometricArm_Hs_inner_le (I := I) (M := M) g₀ σ
  refine ⟨Clower, hCl, fun g₁ h htie δ hδ_lt hδ_nn hδ T₀ => ?_⟩
  have hpair' := hpair g₁ h htie hδ_lt hδ_nn hδ
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀) T₀
  rw [real_inner_self_eq_norm_sq] at hpair'
  have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  rcases eq_or_lt_of_le (norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ σ
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀))) with hA0 | hApos
  · rw [← hA0]
    exact add_nonneg (mul_nonneg hκ_nn (norm_nonneg _)) (mul_nonneg hCl (norm_nonneg _))
  · have hmul : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖
          * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖
        ≤ ((δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖)
          * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ := by
      nlinarith [hpair']
    exact le_of_mul_le_mul_right hmul hApos

theorem deTurckPrincipalCometricArm_spectralWeighted_coeffSq_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (T₀ : SmoothCcTensor g₀ 0 2),
          ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i σ *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)).coeff i) ^ 2 ≤
            ((δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
                Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖) ^ 2 := by
  obtain ⟨Clower, hCl, hnorm⟩ :=
    deTurckPrincipalCometricArm_Hs_norm_le (I := I) (M := M) g₀ σ
  refine ⟨Clower, hCl, fun g₁ h htie δ hδ_lt hδ_nn hδ T₀ => ?_⟩
  rw [← tensorHs.norm_sq_eq_tsum]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hnorm g₁ h htie hδ_lt hδ_nn hδ T₀) 2

theorem deTurckPrincipalCometricArm_spectralGarding_of_weightedCoeffSq
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (T₀ : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ ≤
            (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖ := by
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    deTurckPrincipalCometricArm_spectralWeighted_coeffSq_le (I := I) (M := M) g₀ σ
  refine ⟨Clower, hClower_nn, fun g₁ h htie δ hδ_lt hδ_nn hδ T₀ => ?_⟩
  have hRHS_nn : 0 ≤
      (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖ := by
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have h1 : 0 ≤ (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ :=
      mul_nonneg hκ_nn (norm_nonneg _)
    have h2 : 0 ≤ Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖ :=
      mul_nonneg hClower_nn (norm_nonneg _)
    linarith
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ ^ 2 ≤
      ((δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖) ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    exact hbound g₁ h htie hδ_lt hδ_nn hδ T₀
  exact le_of_sq_le_sq hsq hRHS_nn

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
