import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem time_dependent_vf_chart_local_picard
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (α : M) :
    ∃ T : ℝ, 0 < T := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
