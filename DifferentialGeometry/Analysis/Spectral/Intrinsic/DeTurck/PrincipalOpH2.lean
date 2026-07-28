import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCoeffH2
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.AppD2Hs

/-!
# Low-regularity DeTurck principal operator

This file packages the DeTurck principal-cometric arm as a completed operator
from spectral `H4` to spectral `H2`.  On a three-dimensional small `H2`
metric ball, its operator norm is linear in the metric deviation.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The completed DeTurck principal-cometric action from spectral `H4` to
spectral `H2`. -/
noncomputable def principalOpH2
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) :=
  appD2Hs (I := I) (M := M) g₀ 2 2
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)

/-- On a three-dimensional spectral `H2` metric ball, the completed DeTurck
principal operator has norm linear in the metric deviation. -/
theorem principalOpH2_norm
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        ‖principalOpH2 (I := I) (M := M) g₀ g₁‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
  obtain ⟨ρ, Ccoeff, hρ, hCcoeff, hcoeff⟩ :=
    principal_coeff_h2 (I := I) (M := M) hDim g₀
  obtain ⟨Capp, hCapp, happ⟩ :=
    appD2Hs_norm (I := I) (M := M) hDim g₀ 2 2
  refine ⟨ρ, Capp * Ccoeff, hρ, mul_nonneg hCapp hCcoeff, ?_⟩
  intro T g₁ hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  let A : ℝ := Ccoeff * N
  have hN : 0 ≤ N := norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg hCcoeff hN
  obtain ⟨_, hjet⟩ := hcoeff T g₁ (by simpa only [N] using hT) htie
  have hbound := happ
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    A hA (by simpa only [A, N] using hjet)
  simpa only [principalOpH2, A, N, mul_assoc] using hbound

/-- On smooth spectral inputs, the completed principal operator is exactly
the geometric DeTurck principal-cometric arm. -/
theorem principalOpH2_core
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor g₀ 0 2) :
    principalOpH2 (I := I) (M := M) g₀ g₁
        (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ U) := by
  simpa only [principalOpH2, deTurckPrincipalCometricArm] using
    appD2Hs_core (I := I) (M := M) hDim g₀ 2 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
