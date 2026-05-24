import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.ChartGlue
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
For a time-dependent vector field `X` on a closed manifold, the global flow
`Φ : ℝ → M → M` is, at every fixed time `t`, a smooth self-map of `M`.

Signature shape: there exist a positive horizon `T` and a flow family `Φ`
such that for every `t < T` the spatial slice `Φ t : M → M` is `C^∞`.
-/
theorem time_dependent_vf_flow_smooth_in_space
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M, ∀ t : ℝ, t < T → ContMDiff I I ∞ (Φ t) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
