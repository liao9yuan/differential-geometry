import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covariant_derivative_of_pullback_vf_naturality
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
