import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolvent
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem connLaplacian_has_predicate_free_eigenbasis
    (g : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
