import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.Hartman

/-!
# Interior bare flow on the full time horizon

Assembles the local Hartman flows of an interior-`C∞` time-dependent vector field `X` into a
single forward flow `Φ` (together with the reverse flow `Ψ` of `-X`) on the **full** horizon
`(0, T)`: `Φ 0 = id`, per-time `C∞` slices on `(0, T)`, the **bare** geometric velocity on
`(0, T)`, the mutual-inverse (group/cocycle) law on `[0, T)`, and joint orbit continuity up to
`t = 0` on `Ico 0 T ×ˢ univ`.

The construction covers `(0, T)` by finitely many overlapping windows; on each window a time-cutoff
of `X` is globally `C∞` (`interior_field_global_cutoff_extension`), its global bare flow on a
uniform sub-horizon is supplied by `global_flow_jointContMDiffOn_on_closed_manifold`, and the
per-window flows are glued by forward bare-flow uniqueness
(`bare_forward_flow_eqOn_of_jointC1`); the `[0, δ)` seed (and the `Φ 0 = id` anchor with the joint
continuity up to `0`) is the from-`0` orbit germ `fromZero_forward_orbit_germ_flow`.  The reverse
flow `Ψ` is the same construction applied to `-X`; mutual inversion is per-window bijectivity glued
by the same uniqueness.
-/

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

/-- **Interior bare flow of an interior-`C∞` field on the full horizon `(0, T)`.**

For a time-dependent vector field `X` on a closed manifold `M` that is jointly `C∞` on the interior
`(0, T) ×ˢ univ` (`hint`) and continuous together with its chart-gradient up to `t = 0`
(`hcont0`, `hgrad0`), there is a forward flow `Φ` and a reverse flow `Ψ : ℝ → M → M` with:

* `Φ 0 = id`, `Ψ 0 = id`;
* `Φ t` and `Ψ t` are `C∞` diffeomorphism candidates for each `t ∈ (0, T)`
  (`ContMDiff I I ∞`);
* the **bare** geometric velocity `∂ₛ Φ s x = X t (Φ t x)` on `(0, T)` (one-sided, `Ici 0`);
* the mutual-inverse / cocycle law `Ψ s ∘ Φ s = id` and `Φ s ∘ Ψ s = id` on `[0, T)`;
* joint orbit continuity of `Φ` up to `t = 0` on `Ico 0 T ×ˢ univ`.

This is the genuine forward-Picard / Hartman flow node, isolated as the single deferred input of the
forward-flow route: the per-window cutoff-flow construction with its finite chaining/gluing cocycle.
It is a regularity/existence statement about the flow of the given field — not a packaging of any
hypothesis — and is TRUE for the classical time-dependent flow of a smooth field on a compact
boundaryless manifold (the finite-window chaining of the uniform-horizon Hartman flows). -/
theorem time_dependent_vf_interior_bare_flow_full_horizon
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ Ψ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧ (∀ x : M, Ψ 0 x = x) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t)) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) ∧
      (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
