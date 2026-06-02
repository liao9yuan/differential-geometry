import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The interior flow on `(0, T)` and its agreement with the `t = 0` anchor

On the open interval `(0, T)` the time-dependent DeTurck field is `C∞`, so the intrinsic
closed-manifold flow engine produces, on each window `[a, b] ⊂ (0, T)`, a jointly-`C∞`
bare-velocity local flow.  This file:

* `interior_cutoff_window_flow` — runs the cutoff + intrinsic-engine pipeline on one window;
* `interior_bare_flow_on_Ioo` — glues the per-window flows into a single flow `Φint` on all of
  `(0, T)`, carrying the bare velocity and per-time smoothness, by interior bare-uniqueness;
* `interior_flow_slice_diffeo_on_Ioo` — each time-slice `Φint t` is a diffeomorphism, via the
  reverse flow of `-X_DT`;
* `anchor_eq_interior_on_Ioo` — `Φint` agrees with the `t = 0` anchor `Φ0` on all of `(0, T)`,
  by a continuity-only forward Euclidean Grönwall seed at the `t = 0` edge plus interior
  bare-uniqueness for the bulk.

Every velocity conclusion is the intrinsic bare `X_DT t (point)`; the chart ODEs used in the
edge seed are stated through the corrected `chartTrivRepr`, never the raw chart value.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- On a window `[a, b] ⊂ (0, T)` around `t₀`, build a cutoff field agreeing with `X_DT` near
`[a, b]` and run the intrinsic engine to get a local bare-velocity flow `Φw`, jointly `C∞`,
anchored at `t₀`, whose velocity is `X_DT` on the agreement window. -/
theorem interior_cutoff_window_flow
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) {T : ℝ}
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (hab : 0 < a) (hab' : a < b) (hbT : b < T) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo a b) :
    ∃ (Te δ : ℝ) (_ : 0 < Te) (_ : 0 < δ) (Φw : M → ℝ → M),
      (∀ p, Φw p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φw q.2 q.1) (Set.Ioo (t₀ - Te) (t₀ + Te) ×ˢ (Set.univ : Set M)) ∧
      (∀ p, ∀ t ∈ Set.Ioo (t₀ - Te) (t₀ + Te), Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (a - δ) (b + δ) → HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φw p s) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φw p t)))) ∧
      Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (a - δ) (b + δ) := sorry

/-- Glue the per-window local flows into a single flow `Φint` on the whole open interval
`(0, T)` carrying the bare velocity `X_DT` and per-time smoothness, by interior
bare-uniqueness chaining over an exhausting family of windows. -/
theorem interior_bare_flow_on_Ioo
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φint : ℝ → M → M,
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ioo (0 : ℝ) T) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x)))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ContMDiff I I ∞ (Φint t)) := sorry

/-- Each time-slice `Φint t` (for `t ∈ (0, T)`) is a diffeomorphism, by building the reverse
flow of `-X_DT` and exhibiting the two as mutually inverse smooth maps. -/
theorem interior_flow_slice_diffeo_on_Ioo
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Φint : ℝ → M → M)
    (hΦint_slice : ∀ t ∈ Set.Ioo (0 : ℝ) T, ContMDiff I I ∞ (Φint t))
    (hΦint_bare : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ioo (0 : ℝ) T) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x)))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φint t x := sorry

/-- The interior flow `Φint` and the `t = 0` anchor `Φ0` agree on all of `(0, T)`: the
continuity-only forward Euclidean Grönwall seed forces `Φint`'s right-limit at `0` to be
`x = Φ0`'s value, then interior bare-uniqueness extends the agreement. -/
theorem anchor_eq_interior_on_Ioo
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2)) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (Φ0 Φint : ℝ → M → M) (σ : ℝ) (hσ : 0 < σ) (hσT : σ ≤ T)
    (hΦ0_0 : ∀ x : M, Φ0 0 x = x)
    (hΦ0_picard : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ σ), Φ0 s x ∈ (chartAt H α).source ∧
        extChartAt I α (Φ0 s x) = extChartAt I α x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X_DT r) (extChartAt I α (Φ0 r x)))
    (hΦ0_bare : ∀ t ∈ Set.Ioo (0 : ℝ) σ, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ioo (0 : ℝ) σ) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ0 t x))))
    (hΦint_bare : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ioo (0 : ℝ) T) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x))))
    (hΦint_cont0 : ∀ x : M, ContinuousWithinAt (fun s : ℝ => Φint s x) (Set.Ioi (0 : ℝ)) 0 → Filter.Tendsto (fun s : ℝ => Φint s x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, Φint t x = Φ0 t x := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
