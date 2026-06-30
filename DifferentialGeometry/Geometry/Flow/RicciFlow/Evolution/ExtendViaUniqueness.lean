import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Extending a Ricci flow past a finite endpoint by an interior restart + uniqueness

Alternative to the restart-*at-ω* + C∞-glue route of `CinftyLimitGlue` / `ricci_flow_extends_construction`.
Instead of restarting from the BBS limit `g(ω)` *at* time ω (which forces the DeTurck
C∞-**up-to-the-initial-time** Gate-R, the jet-matching, and Gate-L), we restart from an **interior**
time `t* < ω` where `g_fam` is genuinely C∞. If the restart `rr` exists for time `TT` with
`ω < t* + TT`, then ω is an *interior* time of `rr(·−t*)`, so C∞-at-ω is free (interior regularity);
forward uniqueness patches `rr(·−t*) = g_fam` on the overlap `[t*, ω)`, dissolving the seam.

This isolates the route to two standard PDE facts (both currently absent from the project, stated here
as labelled obligations):

* `ricci_flow_interior_restart` — a uniform/stable short-time existence: the restart from some interior
  `t*` reaches past ω. (Cleanest via `g(t*) → g(ω)` C∞ (BBS) + lower-semicontinuity of the existence
  time, or a quantitative-in-curvature short-time existence.)
* `ricci_flow_forward_unique` — forward uniqueness of the Ricci flow (standard, via DeTurck).

See `ExtendViaUniqueness.md`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Obligation (A): interior restart reaching past ω.** From the bounded-curvature solution on
`[α, ω)` (whose C∞ limit at ω is recorded by `limit`), short-time existence restarted from `g_fam t*`
at some interior `t* < ω` exists for a time `TT` with `ω < t* + TT`. The non-trivial content is that
the existence time does not collapse as `t* → ω` (a uniform/stable short-time existence — cleanest
from `g(t*) → g(ω)` C∞ + lower-semicontinuity of the existence time). The restart `rr` carries the
ordinary short-time regularity (interior C∞, C⁰ up to 0, the Ricci-flow PDE). Currently a labelled
PDE obligation (not in the project). -/
theorem ricci_flow_interior_restart
    (g_fam : ℝ → SmoothRiemannianMetric I M) {α omega : ℝ} (hαω : α < omega)
    (limit : CinftyLimitData (I := I) g_fam α omega hαω) :
    ∃ t_star : ℝ, t_star ∈ Set.Ico α omega ∧ ∃ TT : ℝ, omega < t_star + TT ∧
      ∃ rr : ℝ → SmoothRiemannianMetric I M, rr 0 = g_fam t_star ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
            (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContinuousOn
            (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) TT, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Set.Ici 0) t) := by
  sorry

/-- **Obligation (B): forward uniqueness of the Ricci flow.** Two solutions on `[a, b)` with equal
initial metric at `a`, each interior-C∞ + C⁰-up-to-`a` and solving `∂ₜg = −2 Ric`, agree on `[a, b)`.
Standard (via the DeTurck trick / parabolic uniqueness); currently a labelled obligation (not in the
project). -/
theorem ricci_flow_forward_unique
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Set.Ici a) t)
    (h2pde : ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Set.Ici a) t)
    (h0 : g₁ a = g₂ a) :
    ∀ t ∈ Set.Ico a b, g₁ t = g₂ t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow

end
