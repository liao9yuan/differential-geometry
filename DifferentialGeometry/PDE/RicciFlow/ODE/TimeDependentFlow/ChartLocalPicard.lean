import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Chart-local Picard–Lindelöf for a time-dependent vector field on a closed
manifold: for any base point `α : M`, there exists a positive time horizon
`T`, an open neighborhood `U ⊆ M` of `α` contained in `(chartAt H α).source`,
and a local flow `φ : ℝ → M → M` with `φ 0 = id` on `U` and the right-handed
manifold-derivative flow equation `∂_t (φ s x) = X t (φ t x)` on `Set.Ici 0`
for every `t ∈ [0, T)` and every `x ∈ U`. Built by pushing the vector field
into the model space via the chart and applying Mathlib's `PicardLindelof`
machinery.
-/
theorem time_dependent_vf_chart_local_picard
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (h : ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x)))) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x))) := h

end DifferentialGeometry.PDE.RicciFlow.ODE
