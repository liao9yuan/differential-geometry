import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis

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

private theorem tensorL2Inner_eq_tsum_l2Coeff_cross_arm
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
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

private theorem spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) (A : SmoothCcTensor g₀ 0 2) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) A).coeff i) =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        A.toFun := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm (I := I) (M := M) g₀
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) A]
  refine tsum_congr (fun i => ?_)
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ h_compact u₀ i n]
  have hweight : tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring

private theorem oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          tensorL2Inner (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun ≤
            (δ / (1 - δ)) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  sorry

theorem deTurckPrincipalCometricArm_spectralPairing_tsum_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) ≤
            2 * (δ / (1 - δ)) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨2 * Clower, by positivity, fun u₀ => ?_⟩
  have hpair :=
    spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner (I := I) (M := M) g₀ n u₀
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)
  rw [hpair]
  have hb := hbound u₀
  have hgoal :
      2 * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          2 * Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 =
        2 * ((δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) := by
    ring
  rw [hgoal]
  linarith [hb]

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * (δ / (1 - δ)) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    deTurckPrincipalCometricArm_spectralPairing_tsum_le (I := I) (M := M) g₀ n
      g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨Clower, hClower_nn, fun u₀ => ?_⟩
  have hinner :
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) =
        ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) :=
    tensorHs.inner_def (I := I) (M := M)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
  rw [hinner]
  exact hbound u₀

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
