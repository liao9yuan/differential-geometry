import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.Eigenbasis
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroup
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem connection_laplacian_maxreg_predicate_free
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
