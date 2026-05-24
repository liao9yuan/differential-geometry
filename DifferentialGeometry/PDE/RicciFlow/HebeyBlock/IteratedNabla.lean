import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem iterated_nabla_vs_iterated_partial_equivalence_H1
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
