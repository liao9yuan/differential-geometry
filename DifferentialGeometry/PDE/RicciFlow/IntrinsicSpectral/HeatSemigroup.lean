import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.Eigenbasis
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

noncomputable def tensorHeatSemigroup_boundedC0
    (g : SmoothRiemannianMetric I M) :
    True := sorry

theorem parabolic_smoothing_ensures_Cinf_on_positive_t
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
