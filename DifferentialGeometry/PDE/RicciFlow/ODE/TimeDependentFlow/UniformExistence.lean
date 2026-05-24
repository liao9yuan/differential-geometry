import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PointwiseLocal
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem time_dependent_vf_uniform_existence_time_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
