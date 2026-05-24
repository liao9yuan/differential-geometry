import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.L2BanachIso
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.Rellich
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Resolvent

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem intrinsic_compact_self_adjoint_resolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
