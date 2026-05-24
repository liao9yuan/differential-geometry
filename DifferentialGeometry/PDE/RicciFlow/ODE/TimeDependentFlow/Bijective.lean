import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ReversedFlow
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ComposeIsId
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
For a time-dependent vector field `X` on a closed manifold, the spatial slice
`Φ t : M → M` of the global flow is bijective on `[0, T)`, with a smooth
inverse (obtained from the time-reversed flow).

Signature shape: there exist a positive horizon `T`, a flow family `Φ`, and
an inverse family `Ψ` such that for every `t < T` the map `Φ t` is bijective,
`Ψ t` is smooth, and `Ψ t ∘ Φ t = id`.
-/
theorem time_dependent_vf_flow_bijective_and_inverse_smooth
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M, ∀ t : ℝ, t < T →
        Function.Bijective (Φ t) ∧ ContMDiff I I ∞ (Ψ t) ∧
          Function.LeftInverse (Ψ t) (Φ t) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
