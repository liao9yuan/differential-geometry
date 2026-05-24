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

Status. BLOCKED. The upstream leaves
`time_reversed_flow_exists` and `compose_flow_with_reversed_flow_is_id`
(in `Bijective/ReversedFlow.lean` and `Bijective/ComposeIsId.lean`) are
currently `sorry`-bodied with their own BLOCKED status, awaiting the
Picard / Cauchy–Lipschitz chain at the base of the time-dependent flow
hierarchy. With no concrete `Ψ` available from those leaves, the
composition argument outlined above cannot be executed: any attempt at a
proof here would re-introduce hypothesis-packaging (assume `∃ Ψ, …` as a
parameter, return it), which is prohibited. Once the upstream chain
supplies concrete flow data, this lemma becomes a straightforward
composition + Grönwall application.
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
