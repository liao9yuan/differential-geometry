import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet

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

theorem deTurckPrincipalCometricArm_spectralGarding_kernel
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
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 1) T₀‖ :=
  sorry

theorem exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
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
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, le_refl 0, fun g₁ h htie δ hδ_lt hδ_nn hδ T₀ => ?_⟩
    have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · exact deTurckPrincipalCometricArm_spectralGarding_kernel (I := I) (M := M) g₀ σ

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
