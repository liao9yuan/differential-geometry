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

/--
Uniform existence-time on a closed manifold: there is a single positive time
horizon `T` and an open cover `{U_α}` of `M` such that at every base point
`α : M` the chart-local Picard flow `φ_α` exists on `U_α` for time `[0, T)`,
with `φ_α 0 = id` on `U_α` and the right-handed flow equation
`∂_t (φ_α s x) = X t (φ_α t x)`. Obtained from the pointwise local flow by
covering compact `M` with finitely many neighborhoods and taking the minimum
of the corresponding horizons.
-/
theorem time_dependent_vf_uniform_existence_time_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : M → Set M, (∀ α : M, IsOpen (U α) ∧ α ∈ U α) ∧
      ∃ φ : M → ℝ → M → M,
        (∀ α : M, ∀ x ∈ U α, φ α 0 x = x) ∧
        ∀ α : M, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U α,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ α s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ α t x))) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
