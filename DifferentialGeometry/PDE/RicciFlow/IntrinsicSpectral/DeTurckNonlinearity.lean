import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
