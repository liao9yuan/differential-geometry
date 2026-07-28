import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

/-!
# Fixed background forcing at Sobolev order two

This file packages the Ricci-DeTurck remainder at zero metric deviation as an
`H^2` spectral tensor.  It is the affine forcing term for the order-two
nonautonomous bootstrap.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
/-- The symmetrized extraction of the zero smooth tensor section vanishes. -/
theorem ccTensorBilinSymm_zero_apply (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring

omit [BoundarylessManifold I M] in
/-- The zero smooth tensor is uniformly fibre-small with constant zero. -/
theorem gFibreOpBound_ccTensorBilinSymm_zero
    (g : SmoothRiemannianMetric I M) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  rw [ccTensorBilinSymm_zero_apply]
  simp only [abs_zero, zero_mul, le_refl]

/-- The fixed Ricci-DeTurck affine forcing at Sobolev order two. -/
def baseForceH2 (g₀ g_bg : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
    (deTurckSmoothRemainder (I := I) g₀ g_bg
      (0 : SmoothCcTensor g₀ 0 2) (by norm_num)
      (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀))

/-- `baseForceH2` is the spectral embedding of the genuine smooth remainder at
zero metric deviation. -/
theorem baseForceH2_core (g₀ g_bg : SmoothRiemannianMetric I M) :
    baseForceH2 (I := I) (M := M) g₀ g_bg =
      ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (0 : SmoothCcTensor g₀ 0 2) (by norm_num)
          (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀)) := by
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
