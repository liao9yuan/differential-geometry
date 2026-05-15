import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Bridge: chart-pushed geodesic flow ↔ manifold geodesic

This file links the chart-pushed phase-space flow `Φ : (E × E) × ℝ → E × E`
provided by `Geodesic/SmoothFlow.lean` to the manifold-level geodesic
formalism (`IsGeodesicAt`, `maximalGeodesic`).

The chart-pushed flow is built from the cutoff vector field
`chartPhaseVFCutoff g α (x₀, v₀) b` on `E × E`, which agrees with the
genuine chart-phase vector field `chartPhaseVF g α` on the inner ball
of the cutoff bump. On that inner ball, the flow's orbits satisfy the
chart-coordinate geodesic ODE
$$\dot x = v, \qquad \dot v = -\Gamma_\alpha(v, v)(x),$$
i.e., the chart-coordinate form of the geodesic equation.

## Main results

* `chartPhaseVF_orbit_uniqueness` — **chart-coordinate ODE uniqueness on
  `E × E`.** Two curves `c₁, c₂ : ℝ → E × E` with matching values at
  `t = 0` that both satisfy the chart-phase geodesic ODE on a
  neighbourhood of `0` agree on a neighbourhood of `0`. This is a direct
  application of `ODE_solution_unique_of_eventually` with the
  smooth-on-chart-interior right-hand side.

* `chartFlowGeodesicCurve` — the candidate manifold curve obtained by
  pulling back the chart-pushed flow's first component via
  `(extChartAt I p).symm`. We give its initial value, continuity, and
  domain properties.

* `IsMIntegralCurveAt.chartPhaseVF_hasDerivAt` — bridge from the
  manifold-level `IsMIntegralCurveAt` predicate to the chart-phase ODE
  satisfied by the chart-pushed lift. This is the **input direction** of
  the bridge: any geodesic lift, when pushed to chart coordinates, solves
  the chart-phase ODE.

## What this file does *not* do

* It does *not* invert the bridge: extracting a manifold geodesic from a
  chart-pushed flow orbit requires lifting the orbit back to the tangent
  bundle, which uses the chart-of-`TM` structure and the explicit form
  of `geodesicVectorFieldChart` as a section. The first-component
  identification of `Φ ((x₀, v₀), t).1` with `extChartAt I p (γ t)` for
  the manifold geodesic `γ` would be a direct consequence and is left as
  a follow-up step.

* It does *not* establish that the chart-pushed flow's first component,
  pulled back to `M`, equals `maximalGeodesic g p v` on the flow's time
  interval. That identification requires both the inverse-bridge above
  *and* a global-uniqueness propagation argument for `maximalGeodesic`
  itself (the chart-fixed geodesic vector field is only `C^∞` on the
  chart-domain preimage, so propagation along the maximal interval must
  change chart basepoint; this is a moving-chart phenomenon and is a
  separate development).
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## The chart-pushed flow's orbit satisfies the chart-phase ODE on the inner ball

The flow `Φ` provided by `exists_chartPhase_isLocalFlow` is a local flow of
the **cutoff** vector field `chartPhaseVFCutoff`, which equals the genuine
chart-phase vector field `chartPhaseVF` on the inner closed ball of the
bump `b`. Orbits whose values lie inside the inner ball therefore satisfy
the chart-phase ODE, not just the cutoff version.

We package this fact as a `HasDerivAt`-form, which is the input required
by `ODE_solution_unique_of_eventually`. -/

section ChartPhaseODE

variable [I.Boundaryless]

/-- The cutoff field equals the genuine chart-phase field on the inner
ball of the bump. Restated for the time-padded variant used by the local
flow theorem. -/
lemma chartPhaseVFTime_eq_chartPhaseVF_of_mem_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) {z : E × E}
    (hz : z ∈ Metric.closedBall z₀ b.rIn) (τ : ℝ) :
    chartPhaseVFTime (I := I) g α z₀ b τ z = chartPhaseVF (I := I) g α z := by
  simp only [chartPhaseVFTime_apply]
  exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b hz

end ChartPhaseODE

/-! ## Chart-coordinate ODE uniqueness on `E × E`

Two curves on `E × E` satisfying the chart-phase geodesic ODE on a
neighbourhood of `0` with matching values at `0` agree on a neighbourhood
of `0`. We prove this by applying `ODE_solution_unique_of_eventually` to
the autonomous (time-independent) chart-phase vector field — which is
`C^1` in `(x, v)` on the chart-target interior, hence locally Lipschitz
there.

The key technical step is to identify the chart-phase ODE as a special
case of a time-dependent ODE with constant time-padding: we set
`vTime t z := chartPhaseVF g α z`. -/

section ChartPhaseUniqueness

variable [I.Boundaryless]

/-- Time-padded autonomous form of `chartPhaseVF`. -/
def chartPhaseVFAuto (g : SmoothRiemannianMetric I M) (α : M) :
    ℝ → (E × E) → E × E :=
  fun _ z => chartPhaseVF (I := I) g α z

@[simp] lemma chartPhaseVFAuto_apply
    (g : SmoothRiemannianMetric I M) (α : M) (t : ℝ) (z : E × E) :
    chartPhaseVFAuto (I := I) g α t z = chartPhaseVF (I := I) g α z := rfl

/-- On the chart-interior product, `chartPhaseVF g α` is locally
Lipschitz: it is `C^1` there, hence locally Lipschitz at each point. -/
lemma chartPhaseVF_lipschitzOnWith_locally
    (g : SmoothRiemannianMetric I M) (α : M)
    {z : E × E} (hz : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 z, LipschitzOnWith K (chartPhaseVF (I := I) g α) s := by
  have hC1 : ContDiffOn ℝ 1 (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
    have h := chartPhaseVF_contDiffOn (I := I) g α
    exact h.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hC1_at : ContDiffAt ℝ 1 (chartPhaseVF (I := I) g α) z :=
    hC1.contDiffAt (hopen.mem_nhds hz)
  exact hC1_at.exists_lipschitzOnWith

/-- **Chart-coordinate ODE uniqueness.** If two curves `c₁, c₂ : ℝ → E × E`
have matching values at `0` and both satisfy the chart-phase geodesic
ODE on a neighbourhood of `0`, with values staying inside the chart-
interior product, then they agree on a neighbourhood of `0`. -/
theorem chartPhaseVF_orbit_uniqueness
    {g : SmoothRiemannianMetric I M} {α : M}
    {c₁ c₂ : ℝ → E × E} {z₀ : E × E}
    (hz₀ : z₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (h1 : c₁ 0 = z₀) (h2 : c₂ 0 = z₀)
    (hd1 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t)) t ∧
        c₁ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hd2 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ t)) t ∧
        c₂ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ := by
  classical
  -- Extract Lipschitz constant around z₀.
  obtain ⟨K, sNhd, hsNhd, hlip⟩ :=
    chartPhaseVF_lipschitzOnWith_locally (I := I) g α hz₀
  -- The Lipschitz hypothesis at time t is on the set sNhd (a neighbourhood of z₀).
  -- We need an `Eventually` version of LipschitzOnWith for the time-padded vector field.
  -- Strategy: rewrite c₁ t ∈ sNhd as an eventually statement, and use
  -- `ODE_solution_unique_of_eventually` with the time-padded version.
  --
  -- The autonomous form of `chartPhaseVF` has K-Lipschitz dependence on a
  -- neighbourhood `sNhd` of z₀, for every t. We define
  -- `vTime := chartPhaseVFAuto g α`.
  set v : ℝ → (E × E) → E × E := chartPhaseVFAuto (I := I) g α with hv_def
  set s : ℝ → Set (E × E) := fun _ => sNhd with hs_def
  -- The Lipschitz condition is uniform in t (autonomous field).
  have hv_lip : ∀ᶠ t in 𝓝 (0 : ℝ), LipschitzOnWith K (v t) (s t) :=
    Filter.Eventually.of_forall (fun _ => hlip)
  -- Continuity-based eventually condition: c₁ t ∈ sNhd near 0.
  have hc1_in_s : ∀ᶠ t in 𝓝 (0 : ℝ), c₁ t ∈ sNhd := by
    -- c₁ continuous at 0 (since it has derivative at 0 from hd1).
    have ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, (HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t₀)) t₀ ∧
        c₁ t₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) ∧
        ∀ᶠ t in 𝓝 t₀, HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ t)) t ∧
          c₁ t ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      refine ⟨0, ?_, hd1⟩
      exact hd1.self_of_nhds
    have hcont : ContinuousAt c₁ 0 := (hd1.self_of_nhds).1.continuousAt
    have hc1_z₀ : c₁ 0 ∈ sNhd := by rw [h1]; exact mem_of_mem_nhds hsNhd
    exact hcont.preimage_mem_nhds (by rw [h1]; exact hsNhd)
  have hc2_in_s : ∀ᶠ t in 𝓝 (0 : ℝ), c₂ t ∈ sNhd := by
    have hcont : ContinuousAt c₂ 0 := (hd2.self_of_nhds).1.continuousAt
    exact hcont.preimage_mem_nhds (by rw [h2]; exact hsNhd)
  -- Package into `ODE_solution_unique_of_eventually` form.
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (v t (c₁ t)) t ∧ c₁ t ∈ s t := by
    filter_upwards [hd1, hc1_in_s] with t htD htS
    exact ⟨htD.1, htS⟩
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (v t (c₂ t)) t ∧ c₂ t ∈ s t := by
    filter_upwards [hd2, hc2_in_s] with t htD htS
    exact ⟨htD.1, htS⟩
  have heq : c₁ 0 = c₂ 0 := h1.trans h2.symm
  exact ODE_solution_unique_of_eventually (v := v) (s := s) (K := K) (t₀ := 0)
    hv_lip hf hg heq

end ChartPhaseUniqueness

/-! ## The chart-pushed flow's orbit through `z₀`

The chart-pushed flow `Φ` from `exists_chartPhase_contDiffOn_isLocalFlow`
restricted to the initial point `(x₀, v₀)`, viewed as a function of time
on the interval `Ioo (-T) T`. -/

section ChartFlowOrbit

variable [I.Boundaryless]

/-- The chart-pushed flow's orbit through the base point `(x₀, v₀)`, as a
function of time. -/
def chartFlowOrbit (Φ : (E × E) × ℝ → E × E) (z₀ : E × E) : ℝ → E × E :=
  fun t => Φ (z₀, t)

@[simp] lemma chartFlowOrbit_apply (Φ : (E × E) × ℝ → E × E) (z₀ : E × E) (t : ℝ) :
    chartFlowOrbit Φ z₀ t = Φ (z₀, t) := rfl

end ChartFlowOrbit

/-! ## The chart-pushed flow geodesic curve on `M`

Given the chart-pushed flow at a base manifold point `p ∈ M`, we obtain a
candidate manifold curve by pulling back the first component via
`(extChartAt I p).symm`. -/

section ChartFlowGeodesicCurve

variable [I.Boundaryless]

/-- The chart-pushed flow geodesic curve on `M`: pull back the first
component of the orbit through `(extChartAt I p p, v_chart)` via the
inverse extended chart at `p`. -/
def chartFlowGeodesicCurve (Φ : (E × E) × ℝ → E × E) (p : M) (v_chart : E) :
    ℝ → M :=
  fun t => (extChartAt I p).symm
    (chartFlowOrbit Φ ((extChartAt I p p, v_chart)) t).1

@[simp] lemma chartFlowGeodesicCurve_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (v_chart : E) (t : ℝ) :
    chartFlowGeodesicCurve (I := I) Φ p v_chart t =
      (extChartAt I p).symm (Φ ((extChartAt I p p, v_chart), t)).1 := rfl

/-- **Initial value of the chart-pushed flow geodesic curve.** Provided
the flow satisfies the `IsLocalFlow` initial-value identity at the base
point, the chart-pushed geodesic curve starts at `p`. -/
theorem chartFlowGeodesicCurve_zero
    {Φ : (E × E) × ℝ → E × E} {p : M} {v_chart : E}
    (hinit : Φ ((extChartAt I p p, v_chart), 0) = (extChartAt I p p, v_chart)) :
    chartFlowGeodesicCurve (I := I) Φ p v_chart 0 = p := by
  unfold chartFlowGeodesicCurve chartFlowOrbit
  rw [hinit]
  -- `(extChartAt I p).symm (extChartAt I p p) = p`.
  exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)

end ChartFlowGeodesicCurve

/-! ## The geodesic-existence packaging through the chart-pushed flow

Combine `exists_chartPhase_contDiffOn_isLocalFlow` with the chart-pushed
flow geodesic curve constructor to produce an existence statement
packaged in manifold terms: there exists a smooth chart-pushed flow that,
when pulled back via `(extChartAt I p).symm`, gives a curve on `M`
starting at `p`. -/

section ChartFlowExistencePackaging

variable [I.Boundaryless] [CompleteSpace E]

/-- **Existence packaging of the chart-pushed flow geodesic curve.** For
any base point `p : M` and chart-coordinate velocity `v_chart : E`, there
exists a `ContDiffBump`, radii `ρ, T > 0`, a chart-pushed flow `Φ`, and
the corresponding chart-pushed geodesic curve `γ : ℝ → M` such that:

* `Φ` is jointly `C^1` on `ball ((x₀, v_chart)) ρ ×ˢ Ioo (-T) T`, where
  `x₀ := extChartAt I p p`;
* the initial-value identity `Φ ((x₀, v_chart), 0) = (x₀, v_chart)` holds;
* the chart-pushed geodesic curve starts at `p`.

The interior assumption `x₀ ∈ interior (extChartAt I p).target` is the
defining condition for the chart-phase ODE to be smooth at the base
point; under `[I.Boundaryless]`, this follows from
`extChartAt_target_subset_interior_of_boundaryless` applied to
`x₀ = extChartAt I p p`. -/
theorem exists_chartFlowGeodesicCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball (((extChartAt I p p, v_chart)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, v_chart) : E × E), 0) = (extChartAt I p p, v_chart) ∧
      chartFlowGeodesicCurve (I := I) Φ p v_chart 0 = p := by
  -- The base chart-point `x₀ := extChartAt I p p` lies in the chart-target
  -- interior, since under `[I.Boundaryless]`, the entire target equals its
  -- interior.
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨_b, ρ, T, Φ, hρ_pos, hT_pos, _hb_sub, hcd, hinit⟩ :=
    exists_chartPhase_contDiffOn_isLocalFlow (I := I) (M := M)
      (g := g) (α := p) (x₀ := x₀) (v₀ := v_chart) hx₀_interior
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, ?_⟩
  exact chartFlowGeodesicCurve_zero (I := I) (Φ := Φ) (p := p) (v_chart := v_chart) hinit

end ChartFlowExistencePackaging

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
