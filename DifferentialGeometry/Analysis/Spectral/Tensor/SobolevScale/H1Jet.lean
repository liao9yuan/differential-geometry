import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder

/-!
# Exact spectral H1 jet identity

This module identifies the rank-two spectral `H¹` norm with the intrinsic
zeroth- and first-order covariant `L²` jet.  The result removes unnecessary
metric-dependent comparison constants from low-regularity product estimates.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem cc_toHs_eq_smooth
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ T =
      smoothCcToTensorHs (I := I) (M := M) g σ T := by
  refine tensorHs.ext ?_
  funext i
  simp only [ccTensorToHs_coeff, smoothCcToTensorHs_coeff]

/-- For a smooth covariant rank-two tensor, the spectral `H¹` norm squared is
exactly the sum of the intrinsic zeroth- and first-order `L²` norms squared. -/
theorem cc_h1_jet_sq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) T‖ ^ 2 =
      ‖T‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 2 T‖ ^ 2 := by
  rw [cc_toHs_eq_smooth (I := I) (M := M) g (1 : ℝ) T]
  have h := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (I := I) (M := M) g 0 T
  simp only [oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] at h
  have horder : (((2 * 0 + 1 : ℕ) : ℝ)) = (1 : ℝ) := by norm_num
  rw [horder] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
