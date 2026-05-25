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
`Φ t : M → M` of the global flow `Φ` produced by
`time_dependent_vf_global_flow_glue` is bijective on `[0, T)`, with a smooth
inverse `Ψ t` (obtained from the time-reversed flow).

The flow `Φ`, its horizon `T`, and the initial-condition / flow-equation
hypotheses are supplied as arguments so that the bijectivity / inverse
conclusion is stated about the same flow used downstream in
`time_dependent_vf_globalflow_on_closed_mfd`.

Mathematical content. Apply `time_reversed_flow_exists` to obtain a horizon
`T'` and a time-reversed companion flow `Ψ` for `X`. Combine with
`compose_flow_with_reversed_flow_is_id` to get `Ψ t (Φ t x) = x` on a common
sub-interval, yielding `Function.LeftInverse (Ψ t) (Φ t)`. Symmetrically
exchange the roles of `Φ` and `Ψ` (the time-reversed flow of the time-reversed
flow is `Φ` itself by Grönwall) to obtain `Function.RightInverse`, hence
`Function.Bijective (Φ t)`. Smoothness of `Ψ t` follows from
`time_dependent_vf_global_flow_smooth_in_space` applied to the reversed
vector field `-X`.

Status. BLOCKED. The conclusion requires producing a *global*
`Ψ : ℝ → M → M` with global smoothness and a global `LeftInverse (Ψ t) (Φ t)`
on all of `M`. The currently available chart-α-local Picard machinery
(`time_dependent_vf_chart_local_picard_with_lipschitz` in
`ChartLocalPicard.lean`, now substantive) produces chart-coordinate flows
`flow : E → ℝ → E` defined only on a closed ball around `(chartAt H α) α` in
the model space, integrating *forward from* `t = 0`. Two prerequisites are
missing before this leaf can be discharged honestly:

* A *global* forward flow `Φ : ℝ → M → M` patched from chart-α-local Picard
  via Grönwall uniqueness on chart overlaps. The companion file
  `Glue.lean` (`time_dependent_vf_global_flow_glue`) is the proper home for
  this construction and is itself currently `sorry`-bodied.

* For time-*dependent* `X`, the chart-α-local Picard applied to `-X`
  integrates `-X` from `t = 0` and does **not** give a chart-local right /
  left inverse of the forward flow at time `t`. The honest inverse is the
  solution at time `0` of the ODE `∂_s = X(s, ·)` with terminal condition
  `(t, y)`. Concretely, this requires either (a) a chart-α-local Picard
  variant with an arbitrary base time `t₀ ∈ [0, T]` (Mathlib's
  `IsPicardLindelof` interface naturally supports this; the existing
  `ChartLocalPicard.lean` specialises it to `t₀ = 0`), or (b) a two-time-
  parameter chart-local flow `φ(s, t, y)` satisfying `∂_s = X(s, φ)` and
  `φ(t, t, y) = y`. The "flow of `-X` from `0`" trick only directly inverts
  the forward flow in the *autonomous* case.

Once a global `Φ` is patched and either a base-time-shifted Picard or a
two-time-parameter flow is built, the chart-local LeftInverse identity
follows from a single application of Mathlib's `ODE_solution_unique`
(Grönwall) on the chart overlaps, and globalises by uniqueness of patching
data. Attempting any of this here without those prerequisites in place
would either be hypothesis-packaging (assume `∃ Ψ, …` as input, return it)
or rely on a Picard variant that does not yet exist.
-/
theorem time_dependent_vf_flow_bijective_and_inverse_smooth
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (_hT : 0 < T) (Φ : ℝ → M → M)
    (_hInit : ∀ x : M, Φ 0 x = x)
    (_hFlow : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici 0) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) :
    ∃ Ψ : ℝ → M → M, ∀ t : ℝ, t < T →
      Function.Bijective (Φ t) ∧ ContMDiff I I ∞ (Ψ t) ∧
        Function.LeftInverse (Ψ t) (Φ t) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
