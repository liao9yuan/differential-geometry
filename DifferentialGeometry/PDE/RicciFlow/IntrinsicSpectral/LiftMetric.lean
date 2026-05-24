import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.QuasilinearStrong
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroup
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem lift_to_smoothriemannianmetric_family
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem positive_definiteness_preserved_through_smoothing_and_time
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
