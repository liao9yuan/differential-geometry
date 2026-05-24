import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem time_dependent_vf_flow_hasMFDerivAt_packaging
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
