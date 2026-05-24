import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import Mathlib.Geometry.Manifold.VectorField.LieBracket

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem mlie_bracket_pullback_naturality
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (X Y : ∀ x : M, TangentSpace I x)
    (x : M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
