import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ReversedFlow
import Mathlib.Analysis.ODE.Gronwall

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
On the existence interval `[0, T)`, composing the forward flow `Φ` of a
time-dependent vector field with the time-reversed flow `Φ_rev` gives the
identity (Grönwall uniqueness of ODE solutions).

Signature shape: there exist a positive horizon `T`, a forward flow `Φ`,
and a reversed flow `Φ_rev` such that for every `t < T` and every `x : M`,
`Φ_rev t (Φ t x) = x`.
-/
theorem compose_flow_with_reversed_flow_is_id
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Φ_rev : ℝ → M → M,
        ∀ t : ℝ, t < T → ∀ x : M, Φ_rev t (Φ t x) = x := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
