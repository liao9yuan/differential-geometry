import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
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

/--
Pointwise local flow for a time-dependent vector field on a closed manifold:
for any base point `x₀ : M`, there exists a positive time horizon `T`, an
open neighborhood `U ⊆ M` of `x₀`, and a local flow `φ : ℝ → M → M` with
`φ 0 = id` on `U` and the right-handed manifold-derivative flow equation
`∂_t (φ s x) = X t (φ t x)` on `Set.Ici 0` for every `t ∈ [0, T)` and every
`x ∈ U`. Specialisation of `time_dependent_vf_chart_local_picard` to a single
base point (the neighborhood is the chart-source intersection produced by
the chart-local Picard step).
-/
theorem time_dependent_vf_pointwise_local_flow
    (X : ℝ → ∀ x : M, TangentSpace I x) (x₀ : M) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x))) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
