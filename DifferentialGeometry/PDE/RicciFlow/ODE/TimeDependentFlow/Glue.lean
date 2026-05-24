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

Mathematical content. Invoke `time_dependent_vf_uniform_existence_time_on_closed_mfd`
to obtain a uniform horizon `T > 0`, an open cover `{U α}` of `M`, and per-base
local flows `φ α : ℝ → M → M` satisfying `φ α 0 x = x` and the flow equation on
`U α × [0, T)`. For each `x : M`, fix any `α(x)` with `x ∈ U α(x)` (`Classical.choose`)
and set `Φ s x := φ (α(x)) s x`. Independence of the choice on chart overlaps —
hence well-definedness — follows from Grönwall-type uniqueness applied to the two
candidate solutions in the chart of any overlap point: both satisfy the same
right-handed ODE with the same initial condition `x`, so they agree on `[0, T)`.
The flow identities at `s = 0` and the derivative identity at each `t ∈ [0, T)`
transfer to `Φ` by definition through the chosen representative.

Status. BLOCKED on a substantive proof of
`time_dependent_vf_uniform_existence_time_on_closed_mfd` (currently `sorry`):
without the per-base local flows the global function cannot be defined. The
Grönwall-uniqueness step further needs a chart-local ODE-uniqueness lemma for
right-handed solutions with values in a manifold, which is not yet available
in this project; it would have to be built from `Mathlib.Analysis.ODE.Gronwall`
by transporting through the model chart.
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
