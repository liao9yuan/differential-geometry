import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import Mathlib.Analysis.ODE.Gronwall
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
Global flow on a closed manifold by gluing the uniform-time chart-local
flows: there exists a positive time horizon `T` and a single global flow
`Φ : ℝ → M → M` with `Φ 0 = id` on all of `M` and the right-handed
manifold-derivative flow equation `∂_t (Φ s x) = X t (Φ t x)` on `Set.Ici 0`
for every `t ∈ [0, T)` and every `x : M`. Uniqueness of solutions of the
ODE on chart overlaps (Grönwall) lets the chart-local flows be patched into
one well-defined global map. This is the bare-function version of the
headline `time_dependent_vf_globalflow_on_closed_mfd`; the upgrade to a
family of diffeomorphisms happens in subsequent files.
-/
theorem time_dependent_vf_global_flow_glue
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x))) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
