import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MaxReg
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckNonlinearity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegFixedPoint
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem intrinsic_quasilinear_strong_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
