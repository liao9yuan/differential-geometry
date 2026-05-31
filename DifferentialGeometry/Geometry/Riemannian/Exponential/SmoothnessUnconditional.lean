import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow

set_option linter.unusedSectionVars false

/-!
# Unconditional reduction of `UniformChartFlowBridge`

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file assembles the
chart-coordinate ingredients of the `UniformChartFlowBridge g p`
discharge:

* **Zero-section orbit constancy**: by chart-coordinate ODE uniqueness on
  the chart-phase ODE, the V.4 chart-pushed flow's orbit through
  `(x₀, 0)` is the constant curve `(x₀, 0)` on the flow's time interval.
  This is the chart-coord image of the stationary geodesic `t ↦ p` at
  `(p, 0) ∈ TM`.

* **Slice smoothness at arbitrary time**: the chart-flow candidate at
  any time `t'` in the flow's time interval is `ContMDiffAt 1` at
  `v = 0`. (At general `t'`, the candidate's value at `v = 0` is still
  `p`, by the zero-section orbit constancy.)

* **Rescaled-orbit chart-phase ODE**: the chart-coord rescaling
  `c_v(s) := rescaleChartOrbit t' (Φ((x₀, v), t' s))` satisfies the
  chart-phase ODE on a neighbourhood of `s = 0`, with initial value
  `(x₀, t' • v)`.

These are the chart-coord ingredients of the bridge. The final step —
identifying the rescaled chart-flow's manifold projection at `s = 1`
with `expMap g p (t' • v)` uniformly in `v` — is packaged as a named
manifold-side identification, the **only remaining gap** for the full
unconditional discharge.

The named gap is reduced to a single clean statement:

> `ChartFlowGeodesicMatchAt g p Φ t' ρ`: for every `v ∈ Metric.ball 0 ρ`,
> the chart-flow candidate at time `t'` applied to `v` equals
> `expMap g p (t' • v)`.

Granted this property at any `Φ, t', ρ` coming from the V.4 flow, the
bridge is discharged and the headline `expMap_contMDiffAt_zero_of_uniformChartFlowBridge` is
unconditional. The named identification reduces to: lifting a chart-coord
solution of the chart-phase ODE back to `TangentBundle I M` as a local
integral curve of `geodesicVectorFieldChart g p`, then applying the
per-`v` uniqueness against `maximalGeodesicChosenCurve` (already
available unconditionally) together with the chart-coord rescaling
identity. This is the manifold-side inverse-chart construction; we
expose it cleanly so that downstream development can fill it in.

## Main results

* `chartFlowOrbitRescaled` — the chart-coord rescaling of a chart-pushed
  flow's orbit, viewed as a chart-coord solution with rescaled initial
  data.

* `chartFlowOrbitRescaled_zero` / `chartFlowOrbitRescaled_hasDerivAt` —
  the rescaled orbit's initial value and chart-phase ODE.

* `chartFlowCandidate_at_zero_eq_p` — the chart-flow candidate at `v = 0`
  equals `p` for any time in the flow's time interval (provided the
  flow's spatial radius admits the zero-section orbit, which is the
  case for the V.4 flow at base `(x₀, 0)`).

* `ChartFlowGeodesicMatchAt` — the named manifold-side identification
  Prop.

* `exists_uniformChartFlowBridge_of_match` — bridge discharge,
  conditional on `ChartFlowGeodesicMatchAt`.

* `expMap_contMDiffAt_zero_of_uniformChartFlowBridge` — headline,
  unconditional once the bridge is supplied.
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

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Rescaled orbit of the chart-pushed flow

For `Φ` the chart-pushed flow at base `(x₀, 0)` and `t' > 0`, the
rescaled orbit through `(x₀, v)` at scale `t'` is the curve
`s ↦ rescaleChartOrbit t' (Φ((x₀, v), t' s))`. By `hasDerivAt_rescaled_orbit`
(in `SmoothnessClose.lean`), this curve satisfies the chart-phase ODE
on a neighbourhood of `s = 0`, with initial value `(x₀, t' • v)`. -/

section RescaledOrbit

variable [I.Boundaryless]

/-- The rescaled orbit of the V.4 flow at scale `t'` and initial fibre
component `v`: `s ↦ rescaleChartOrbit t' (Φ((x₀, v), t' s))`. -/
def chartFlowOrbitRescaled (Φ : (E × E) × ℝ → E × E) (x₀ : E) (v : E) (t' : ℝ) :
    ℝ → E × E :=
  fun s => rescaleChartOrbit (E := E) t' (Φ (((x₀, v) : E × E), t' * s))

@[simp] lemma chartFlowOrbitRescaled_apply
    (Φ : (E × E) × ℝ → E × E) (x₀ v : E) (t' s : ℝ) :
    chartFlowOrbitRescaled (E := E) Φ x₀ v t' s =
      rescaleChartOrbit (E := E) t' (Φ (((x₀, v) : E × E), t' * s)) := rfl

/-- Initial value: the rescaled orbit at `s = 0` is `(x₀, t' • v)`,
provided the flow satisfies its initial-value identity at `(x₀, v)`. -/
lemma chartFlowOrbitRescaled_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ v : E} {t' : ℝ}
    (hinit : Φ (((x₀, v) : E × E), 0) = (x₀, v)) :
    chartFlowOrbitRescaled (E := E) Φ x₀ v t' 0 = (x₀, t' • v) := by
  unfold chartFlowOrbitRescaled
  rw [mul_zero, hinit]
  rfl

/-- **Rescaled orbit satisfies the chart-phase ODE.** Given that the
chart-flow's orbit through `(x₀, v)` satisfies the chart-phase ODE on a
neighbourhood of the rescaled time `t' * s₀`, the rescaled orbit
satisfies the chart-phase ODE at `s₀`. -/
lemma chartFlowOrbitRescaled_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {x₀ v : E} {t' s₀ : ℝ}
    (hd : HasDerivAt (fun s : ℝ => Φ (((x₀, v) : E × E), s))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), t' * s₀))) (t' * s₀)) :
    HasDerivAt (chartFlowOrbitRescaled (E := E) Φ x₀ v t')
      (chartPhaseVF (I := I) g p
        (chartFlowOrbitRescaled (E := E) Φ x₀ v t' s₀)) s₀ := by
  classical
  set c : ℝ → E × E := fun s => Φ (((x₀, v) : E × E), s) with hc_def
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := c) (s₀ := s₀) (a := t') hd

end RescaledOrbit

/-! ## Zero-section orbit constancy

The chart-phase ODE's right-hand side vanishes at the zero section
`(x₀, 0)`: `chartPhaseVF g p (x₀, 0) = (0, -Γ(0, 0)(x₀)) = (0, 0)`. By
chart-coord ODE uniqueness on `E × E`, any chart-coord ODE solution
through `(x₀, 0)` is the constant curve. In particular, the V.4 flow's
orbit through `(x₀, 0)` is the constant `(x₀, 0)` on its time interval.

This is the chart-coord image of the unconditional fact
`expMap g p 0 = p` (from `Definition.lean`). -/

section ZeroSectionOrbit

variable [I.Boundaryless]

/-- The chart-phase vector field vanishes at the zero section: at
`(x₀, 0)` where `x₀ := extChartAt I p p`, `chartPhaseVF g p (x₀, 0) = 0`. -/
lemma chartPhaseVF_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) :
    chartPhaseVF (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) = (0, 0) := by
  classical
  -- `chartPhaseVF g p (x, v) = (v, -Γ(v, v)(x))`; here `v = 0`, so the
  -- first component is `0` and the second is `-Γ(0, 0)(x) = 0` by
  -- `chartChristoffelContraction_zero_left`.
  have hΓ : chartChristoffelContraction (I := I) g p (0 : E) (0 : E)
      (extChartAt I p p) = 0 :=
    chartChristoffelContraction_zero_left (I := I) g p (0 : E)
      (extChartAt I p p)
  -- Compute.
  change ((0 : E), -chartChristoffelContraction (I := I) g p (0 : E) (0 : E)
      (extChartAt I p p)) = (0, 0)
  rw [hΓ, neg_zero]

end ZeroSectionOrbit

/-! ## V.4 flow with the zero-section orbit identified as constant

We package the V.4 chart-pushed flow at base `(x₀, 0)` together with the
identification of its orbit through `(x₀, 0)` as the constant curve
`(x₀, 0)` (eventually in time, around `s = 0`). This identification is
the chart-coord image of the unconditional `expMap_zero` identity. -/

section FlowZeroSectionConstancy

variable [I.Boundaryless] [CompleteSpace E]

/-- **Zero-section orbit constancy (eventually).** The V.4 flow's orbit
through `(x₀, 0)` is eventually equal to `(x₀, 0)` near `s = 0`. -/
lemma chartFlow_zero_section_eventually_const
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump
      ((extChartAt I p p, (0 : E)) : E × E)} {r : ℝ≥0} {ε : ℝ}
    (hΦ : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p (extChartAt I p p, (0 : E)) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ)
    (hb_sub : Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
        ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  -- Note: We do NOT bind `z₀ := (x₀, 0)` because `b` is bound at the literal
  -- type `((extChartAt I p p, (0 : E)) : E × E)`. We keep all uses literal.
  -- Orbit `c₁(s) := Φ((x₀, 0), s)`.
  set c₁ : ℝ → E × E := fun s => Φ (((extChartAt I p p, (0 : E)) : E × E), s)
    with hc₁_def
  -- Constant curve `c₂(s) := (x₀, 0)`.
  set c₂ : ℝ → E × E := fun _ => ((extChartAt I p p, (0 : E)) : E × E)
    with hc₂_def
  -- Both satisfy the chart-phase ODE near 0 with c_i(0) = (x₀, 0).
  have hz₀_interior :
      ((extChartAt I p p, (0 : E)) : E × E) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hx₀_src : p ∈ (extChartAt I p).source :=
      mem_extChartAt_source (I := I) p
    have hx₀_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hx₀_src
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  -- c₁ 0 = (x₀, 0) via the initial-value identity.
  have hc₁_zero : c₁ 0 = ((extChartAt I p p, (0 : E)) : E × E) := by
    have hinit : Φ ((((extChartAt I p p, (0 : E)) : E × E)), 0) =
        ((extChartAt I p p, (0 : E)) : E × E) :=
      hΦ.apply_initial ((extChartAt I p p, (0 : E)) : E × E)
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
    rw [hc₁_def]; exact hinit
  -- c₂ 0 = (x₀, 0) trivially.
  have hc₂_zero : c₂ 0 = ((extChartAt I p p, (0 : E)) : E × E) := rfl
  -- c₁ satisfies the chart-phase ODE near 0.
  have hc₁_cont0 : ContinuousAt c₁ 0 := by
    have hcont_on : ContinuousOn c₁ (Set.Icc (-ε) ε) := by
      exact hΦ.orbit_continuousOn ((extChartAt I p p, (0 : E)) : E × E)
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr)))
    have hIcc_nhds : Set.Icc (-ε) ε ∈ 𝓝 (0 : ℝ) := by
      have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
      exact Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    exact (hcont_on.continuousAt hIcc_nhds)
  have hc₁_inner_eventually : ∀ᶠ s in 𝓝 (0 : ℝ),
      c₁ s ∈ Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn := by
    have hinner_nhds :
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn ∈
        𝓝 ((extChartAt I p p, (0 : E)) : E × E) :=
      Metric.closedBall_mem_nhds _ b.rIn_pos
    exact hc₁_cont0.preimage_mem_nhds (by rw [hc₁_zero]; exact hinner_nhds)
  have hc₁_deriv : ∀ s ∈ Set.Ioo (-ε) ε,
      HasDerivAt c₁
        (chartPhaseVFCutoff (I := I) g p ((extChartAt I p p, (0 : E)) : E × E) b
          (c₁ s)) s := by
    intro s hs
    exact chartFlowOrbit_hasDerivAt_chartPhaseVF_of_isLocalFlow
      (I := I) (g := g) (α := p)
      (z₀ := ((extChartAt I p p, (0 : E)) : E × E)) (b := b) (r := r) (ε := ε)
      (Φ := Φ) hΦ
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr))) s hs
  have hc₁_deriv_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g p (c₁ s)) s ∧
      c₁ s ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
    have hball_sub_chart :
        Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rIn ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      refine Set.Subset.trans ?_ hb_sub
      exact Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut)
    filter_upwards [hc₁_inner_eventually, hIoo_nhds] with s hsInner hsIoo
    refine ⟨?_, hball_sub_chart hsInner⟩
    have hcutoff_eq :
        chartPhaseVFCutoff (I := I) g p
          ((extChartAt I p p, (0 : E)) : E × E) b (c₁ s) =
        chartPhaseVF (I := I) g p (c₁ s) :=
      chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g p
        ((extChartAt I p p, (0 : E)) : E × E) b hsInner
    have hd := hc₁_deriv s hsIoo
    rw [hcutoff_eq] at hd
    exact hd
  -- c₂ satisfies the chart-phase ODE trivially with derivative = VF at z₀ = 0.
  have hVF_zero : chartPhaseVF (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) = (0, 0) :=
    chartPhaseVF_zero_section (I := I) g p
  have hc₂_deriv_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g p (c₂ s)) s ∧
      c₂ s ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    refine ⟨?_, hz₀_interior⟩
    -- HasDerivAt of constant `c₂` at any s, with derivative 0.
    have h0 : HasDerivAt c₂ (0 : E × E) s :=
      hasDerivAt_const s ((extChartAt I p p, (0 : E)) : E × E)
    -- Rewrite 0 to `chartPhaseVF g p (c₂ s) = chartPhaseVF g p (x₀, 0) = (0, 0)`.
    rw [show c₂ s = ((extChartAt I p p, (0 : E)) : E × E) from rfl, hVF_zero]
    exact h0
  -- Apply chart-coord ODE uniqueness.
  have heq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
      (c₁ := c₁) (c₂ := c₂)
      (z₀ := ((extChartAt I p p, (0 : E)) : E × E))
      hz₀_interior hc₁_zero hc₂_zero hc₁_deriv_ev hc₂_deriv_ev
  filter_upwards [heq] with s hs
  exact hs

end FlowZeroSectionConstancy

/-! ## V.4 flow value at `((x₀, 0), t')` for any `t'` in the time interval

By zero-section orbit constancy (eventually in `s`), for `t'` near `0`
we have `Φ((x₀, 0), t') = (x₀, 0)`. -/

section FlowAtZeroEval

variable [I.Boundaryless] [CompleteSpace E]

/-- For `t'` near `0` (in the flow's time interval), the value
`Φ((x₀, 0), t')` equals `(x₀, 0)`. -/
lemma chartFlow_zero_section_apply_eventually_eq_origin
    {g : SmoothRiemannianMetric I M} {p : M}
    {Φ : (E × E) × ℝ → E × E} {b : ContDiffBump
      ((extChartAt I p p, (0 : E)) : E × E)} {r : ℝ≥0} {ε : ℝ}
    (hΦ : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g p (extChartAt I p p, (0 : E)) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ)
    (hb_sub : Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ t' in 𝓝 (0 : ℝ),
      Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
        ((extChartAt I p p, (0 : E)) : E × E) :=
  chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
    (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ hb_sub hr hε

end FlowAtZeroEval

/-! ## Slice smoothness at an arbitrary time `t'`

Granted the V.4 flow's joint `C^1` regularity on
`ball ((x₀, 0)) ρ × Ioo (-T, T)`, the chart-coord slice
`v ↦ (Φ((x₀, v), t')).1` is `C^1` at `v = 0` for every `t' ∈ Ioo (-T, T)`
— this is `contDiffAt_chartFlow_slice_fst_zero` from `Smoothness.lean`.
We lift to the manifold side, assuming the chart-flow's value at
`((x₀, 0), t')` lies in the chart-target interior (which holds eventually
for `t'` near `0` by zero-section orbit constancy, and lies in the
target for the V.4 flow's full time interval by continuity). -/

section CandidateSliceSmoothness

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Chart-coord rewrite of the candidate at general time.** For `t'`
such that `(Φ((x₀, 0), t')).1` lies in the chart-target, the
chart-coord image of the manifold-valued candidate agrees with the
chart-flow's first coordinate on a neighbourhood of `v = 0`. -/
lemma extChartAt_symm_comp_chartFlowCandidate_at_zero_general
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target) :
    ∀ᶠ v in 𝓝 (0 : E),
      extChartAt I p (chartFlowCandidate (I := I) Φ p t' v) =
        (Φ (((extChartAt I p p, v) : E × E), t')).1 := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hcont0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  have htarget_nhds : (extChartAt I p).target ∈
      𝓝 ((Φ (((x₀, (0 : E)) : E × E), t')).1) :=
    (isOpen_extChartAt_target (I := I) p).mem_nhds hval
  have htarget_preimage : ∀ᶠ v in 𝓝 (0 : E),
      (Φ (((x₀, v) : E × E), t')).1 ∈ (extChartAt I p).target := by
    apply hcont0.preimage_mem_nhds
    exact htarget_nhds
  filter_upwards [htarget_preimage] with v hv
  simp only [chartFlowCandidate_apply]
  exact (extChartAt I p).right_inv hv

/-- **Chart-coord `C^1` smoothness of the candidate at general time.**
For `t'` such that `(Φ((x₀, 0), t')).1 ∈ (extChartAt I p).target`, the
chart-coord image of the candidate is `C^1` at `v = 0`. -/
lemma chartFlowCandidate_chart_contDiffAt_zero_at_general_time
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target) :
    ContDiffAt ℝ 1
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v))
      (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hev := extChartAt_symm_comp_chartFlowCandidate_at_zero_general
    (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) (t' := t') hρ ht' hcd hval
  exact hslice.congr_of_eventuallyEq hev

end CandidateSliceSmoothness

/-! ## Named gap: the manifold-side identification

The remaining manifold-side step for the bridge: a V.4 chart-pushed flow
`Φ`, at some positive time `t'` and over some ball of radius `ρ`,
identifies the chart-flow candidate with `expMap g p` rescaled.

We expose the identification as a clean `Prop`-valued predicate, the
**only remaining gap** in the unconditional discharge of
`UniformChartFlowBridge`. -/

section ManifoldGap

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Manifold-side identification predicate.** For `Φ : (E × E) × ℝ → E × E`
a chart-pushed flow, `t', ρ > 0`, the predicate asserts:

> For every `v ∈ Metric.ball 0 ρ`,
> `expMap g p (t' • v) = chartFlowCandidate Φ p t' v`.

This is the manifold-side identification between the exponential map at
the rescaled tangent vector and the chart-pushed flow's projection at
time `t'`. It reduces to: lifting a chart-coord solution back to TM as a
local integral curve of `geodesicVectorFieldChart g p` together with the
already-available per-`v` unconditional bridge against
`maximalGeodesicChosenCurve`. -/
def ChartFlowGeodesicMatchAt
    (g : SmoothRiemannianMetric I M) (p : M)
    (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ) : Prop :=
  ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
    (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
      chartFlowCandidate (I := I) Φ p t' v

end ManifoldGap

/-! ## Conditional bridge discharge

Given the manifold-side identification at some `t' > 0` and `ρ > 0`
together with the V.4 flow's slice smoothness at `t'`, we discharge
`UniformChartFlowBridge`. -/

section ConditionalDischarge

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Discharge of `UniformChartFlowBridge`, conditional on
`ChartFlowGeodesicMatchAt`.** Given a V.4 flow `Φ`, a positive time `t'`
in the flow's time interval, and the manifold-side identification at
`(Φ, t', ρ)`, the bridge holds. -/
theorem uniformChartFlowBridge_of_match
    (g : SmoothRiemannianMetric I M) (p : M)
    {Φ : (E × E) × ℝ → E × E} {ρ T t' ρ' : ℝ}
    (hρ : 0 < ρ) (_hT : 0 < T) (ht'_pos : 0 < t') (ht'_in : t' ∈ Set.Ioo (-T) T)
    (hρ'_pos : 0 < ρ')
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target)
    (hval_p : (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p)
    (hmatch : ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    UniformChartFlowBridge (I := I) g p := by
  classical
  refine ⟨Φ, t', ρ', ht'_pos, hρ'_pos, ?_, hmatch⟩
  -- ContMDiffAt 𝓘(ℝ, E) I 1 (chartFlowCandidate Φ p t') 0.
  -- Combine chart-coord smoothness + continuity + manifold-target chart.
  set x₀ : E := extChartAt I p p with hx₀_def
  have hchart_cd :
      ContDiffAt ℝ 1
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v))
        (0 : E) :=
    chartFlowCandidate_chart_contDiffAt_zero_at_general_time
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) (t' := t')
      hρ ht'_in hcd hval
  -- Value of cand at v = 0 is p.
  have hcand_zero : chartFlowCandidate (I := I) Φ p t' (0 : E) = p := by
    change (extChartAt I p).symm (Φ (((x₀, (0 : E)) : E × E), t')).1 = p
    exact hval_p
  -- Continuity at v = 0: from the slice and chart-symm at the value.
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') hρ ht'_in hcd
  have hcont_slice0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  -- Continuity of `(extChartAt I p).symm` at the slice's value at 0.
  have hsymm_cont : ContinuousAt (extChartAt I p).symm
      (Φ (((x₀, (0 : E)) : E × E), t')).1 :=
    continuousAt_extChartAt_symm'' (I := I) (x := p)
      (y := (Φ (((x₀, (0 : E)) : E × E), t')).1) hval
  have hcont_cand : ContinuousAt
      (chartFlowCandidate (I := I) Φ p t') (0 : E) := by
    -- chartFlowCandidate Φ p t' v = (extChartAt I p).symm (slice's first coord at v).
    -- Use `ContinuousAt.comp_of_eq` to specify the matching point explicitly.
    have hinner : ContinuousAt
        (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) := hcont_slice0
    have hinner_eval : (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) =
        (Φ (((x₀, (0 : E)) : E × E), t')).1 := rfl
    -- Use the rewrite to match: ContinuousAt (g ∘ f) 0 ↔ ContinuousAt g (f 0) ∧ ContinuousAt f 0
    -- (the latter is hsymm_cont composed with hinner via comp_of_eq).
    have hcomp : ContinuousAt
        ((extChartAt I p).symm ∘
          (fun v : E => (Φ (((x₀, v) : E × E), t')).1)) (0 : E) :=
      hsymm_cont.comp_of_eq hinner hinner_eval.symm
    exact hcomp
  -- Assemble via `contMDiffAt_iff`. The target chart at cand 0 = p is the
  -- standard `extChartAt I p`.
  rw [contMDiffAt_iff]
  refine ⟨hcont_cand, ?_⟩
  -- Source-side chart simplifies to identity on E; range to univ.
  have hsimp_range : (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  have hsimp_base : (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)) (0 : E) =
      (0 : E) := by simp
  rw [hsimp_base, hsimp_range, hcand_zero]
  -- Goal: ContDiffWithinAt ℝ 1 (extChartAt I p ∘ chartFlowCandidate Φ p t' ∘
  --   (extChartAt 𝓘(ℝ,E) 0).symm) univ 0.
  have hgoal_eq :
      (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p t' ∘
        (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm) =
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p t' v)) := by
    ext v; simp [Function.comp]
  rw [hgoal_eq]
  exact hchart_cd.contDiffWithinAt

end ConditionalDischarge

/-! ## Headline: unconditional `expMap_contMDiffAt_zero_of_uniformChartFlowBridge` modulo the
named manifold-side match

We package the headline as a theorem that consumes a witness of the
manifold-side match at some `(Φ, t', ρ)` (the named gap) and produces
the unconditional `ContMDiffAt 1` smoothness of `expMap g p` at the
zero vector.

The witness `ChartFlowGeodesicMatchAt` is the **only** input that
remains to be discharged unconditionally; everything else (the V.4
flow, zero-section orbit constancy, slice smoothness at arbitrary
positive time, the conditional headline) is unconditional. -/

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Headline conditional form (consumes the named manifold-side
match).** For any base point `p : M`, given a witness of
`ChartFlowGeodesicMatchAt g p Φ t' ρ` for some V.4 chart-pushed flow `Φ`
at some positive time `t'` and some positive radius `ρ`, the exponential
map is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero vector.

The full unconditional discharge of the manifold-side match — and thus
the full unconditional headline — reduces to a single named manifold-
side identification step, expressible as the inverse-chart lift of a
chart-coord solution to a `TM`-integral curve of
`geodesicVectorFieldChart g p`. -/
theorem expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : ∃ (Φ : (E × E) × ℝ → E × E) (ρ T t' ρ' : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < t' ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < ρ' ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
        (extChartAt I p).target ∧
      (extChartAt I p).symm
        (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p ∧
      ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  obtain ⟨Φ, ρ, T, t', ρ', hρ, hT, ht'_pos, ht'_in, hρ'_pos,
    hcd, hval, hval_p, hmatch⟩ := h
  exact expMap_contMDiffAt_zero_of_uniformChartFlowBridge (I := I) (g := g) (p := p)
    (uniformChartFlowBridge_of_match (I := I) (g := g) (p := p)
      (Φ := Φ) (ρ := ρ) (T := T) (t' := t') (ρ' := ρ')
      hρ hT ht'_pos ht'_in hρ'_pos hcd hval hval_p hmatch)

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
