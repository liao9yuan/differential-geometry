import DifferentialGeometry.PDE.RicciFlow.Pullback.RiemannConjugation
import DifferentialGeometry.Integral.Connection.Ricci
import Mathlib.LinearAlgebra.Trace

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem ricci_trace_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
