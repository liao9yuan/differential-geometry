import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff

noncomputable def Diffeomorph.pushforward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (W : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
