import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness

set_option linter.unusedSectionVars false

/-!
# Bridge infrastructure: `IsGeodesic` to chart-coordinate geodesic equation

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file collects the
infrastructure that bridges the integral-curve form
(`IsGeodesic`, `IsGeodesicAt`) to the chart-coordinate
second-derivative form (`HasGeodesicEquationAt`).

## Strategy

The chart-pushed lift `chartPushLift f t₀ s := extChartAt I.tangent (f t₀) (f s)`
of an integral curve `f` of `geodesicVectorFieldChart g α` carries a
first-derivative formula `chartPushLift_eventually_hasDerivAt` valued in
`E × E`. Taking the first component yields a `HasDerivAt` statement on
the chart-local curve `chartLocalCurve γ t₀`, where `γ = projectCurve f`.

A key simplification occurs at the **base time** `s = t₀`: the
change-of-coordinates `tangentCoordChange I.tangent (f t₀) (f t₀) (f t₀)`
on the tangent bundle of the tangent bundle of `M` reduces to the identity
(via `tangentCoordChange_self`), so the chart-pushed VF coincides with the
chart-fixed VF at `f t₀`. We exploit this to extract the first-derivative
clause of `HasGeodesicEquationAt` in the chart-centred case
(`α = γ(t₀)`) unconditionally.

The general (chart basepoint `α` arbitrary) case is reduced to the
chart-centred case via a uniqueness argument: a chart-`γ(t₀)`-centred
integral curve with the same value at `t₀` exists by Picard–Lindelöf
(`Existence.lean`), and by chart-fixed integral-curve uniqueness
(`Uniqueness.lean`) it agrees with the original lift on a neighbourhood.
The full bridge composes these steps.

## What is delivered here

* `chartPushLift_fst_eq` / `chartPushLift_fst_eq_chartLocalCurve` — the
  base-component decomposition of the chart-pushed lift.
* `chartPushVF_self` — the chart-pushed VF reduces to the chart-fixed
  VF at the base time.
* `exists_chartCenteredLift_at` — a chart-centred integral curve exists
  at any base time, by time-shifted Picard–Lindelöf.
* `hasDerivAt_chartLocalCurve_of_chartCentered` — the first-derivative
  clause of `HasGeodesicEquationAt`, established unconditionally in the
  chart-centred case.
* `eventually_hasDerivAt_chartLocalCurve_of_chartCentered` — the
  eventually-clause of `HasGeodesicEquationAt`.
* `hasGeodesicEquationAt_of_chartCentered_of_phase_identity` — the
  conditional bridge: from the autonomous phase-space identity and a
  chart-`γ(t₀)`-centred lift, obtain `HasGeodesicEquationAt`.
* `chartPushVF_eventually_eq_chartPhaseVF_of_chartCentered` — the
  autonomous phase-space identity discharged unconditionally for a
  chart-`γ(t₀)`-centred lift, by composing
  `chartPushVF_eq_chartPhaseVF_at` with chart-source continuity at
  `t₀`.
* `hasGeodesicEquationAt_of_chartCentered` — the **unconditional**
  chart-centred bridge: from a chart-`γ(t₀)`-centred lift alone, obtain
  `HasGeodesicEquationAt`.
* `hasGeodesicEquationAt_of_exists_chartCentered_lift` — the existence
  packaging of the chart-centred bridge.
* `IsGeodesicAt.hasGeodesicEquationAt_chartCentered` — the
  `IsGeodesicAt` form of the chart-centred bridge, applicable when the
  witness chart basepoint coincides with `γ(t₀)`.

## What is deferred

The fully unconditional `IsGeodesicAt → HasGeodesicEquationAt` bridge
(without the chart-centring hypothesis on the witness) requires
reducing an arbitrary `IsGeodesicAt`-witness to a chart-`γ(t₀)`-centred
one. A new chart-centred lift can be produced by Picard–Lindelöf at
`⟨γ t₀, (f t₀).snd⟩` with chart basepoint `γ t₀`, but identifying its
projection with `γ` near `t₀` requires a projection-uniqueness
argument across distinct chart-fixed vector fields. That reduction is
not delivered in this file.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Decomposition of the chart-pushed lift -/

section ChartPushedDecomp

/-- The first component of the chart-pushed lift coincides with the
chart image of the projection of `f`, evaluated in the chart at the foot
point of `f t₀`. -/
lemma chartPushLift_fst_eq
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    (chartPushLift (I := I) f t₀ t).1 =
      extChartAt I (f t₀).proj ((f t).proj) := by
  classical
  unfold chartPushLift
  rw [FiberBundle.extChartAt (E := TangentSpace I) (F := E)
        (HB := H) (IB := I) (f t₀)]
  simp only [PartialEquiv.trans_apply, PartialEquiv.prod_coe]
  rfl

/-- Specialisation: when the projection of `f` equals a given curve `γ`,
the first component of the chart-pushed lift equals
`extChartAt I (γ t₀) (γ t)`. -/
lemma chartPushLift_fst_eq_chartLocalCurve
    {f : ℝ → TangentBundle I M} {γ : ℝ → M}
    (hproj : ∀ t, (f t).proj = γ t) (t₀ t : ℝ) :
    (chartPushLift (I := I) f t₀ t).1 =
      extChartAt I (γ t₀) (γ t) := by
  rw [chartPushLift_fst_eq (I := I) f t₀ t, hproj t₀, hproj t]

end ChartPushedDecomp

/-! ## Self-evaluation of the chart-pushed phase-space vector field -/

section ChartPushVFSelf

/-- At the base time `t = t₀`, the chart-pushed phase-space vector field
equals the chart-fixed geodesic vector field at `f t₀`. -/
lemma chartPushVF_self
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    chartPushVF (I := I) g α f t₀ t₀ =
      geodesicVectorFieldChart (I := I) g α (f t₀) := by
  classical
  unfold chartPushVF
  have hsrc : f t₀ ∈ (extChartAt I.tangent (f t₀)).source :=
    mem_extChartAt_source (I := I.tangent) (f t₀)
  exact tangentCoordChange_self (I := I.tangent) (x := f t₀) (z := f t₀)
    (v := geodesicVectorFieldChart (I := I) g α (f t₀)) hsrc

end ChartPushVFSelf

/-! ## Construction of a chart-centred lift at any base time -/

section ChartCenteredLift

variable [I.Boundaryless] [CompleteSpace E]

/-- For any tangent vector `v : TangentSpace I p` and base time `t₀ : ℝ`,
there exists a lift `f : ℝ → TangentBundle I M` with `f t₀ = ⟨p, v⟩` that
is a local integral curve of the chart-`p`-fixed geodesic vector field at
`t = t₀`. Time-shifted Picard–Lindelöf. -/
lemma exists_chartCenteredLift_at
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t₀ : ℝ) :
    ∃ f : ℝ → TangentBundle I M,
      f t₀ = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) t₀ := by
  obtain ⟨f₀, hf₀_init, hf₀⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  refine ⟨f₀ ∘ (· - t₀), ?_, ?_⟩
  · change f₀ (t₀ - t₀) = (⟨p, v⟩ : TangentBundle I M)
    rw [sub_self]; exact hf₀_init
  · have hshift := hf₀.comp_add (-t₀)
    have hfn : (fun s : ℝ => s + -t₀) = (fun s : ℝ => s - t₀) := by
      funext s; ring
    have ht : (0 : ℝ) - -t₀ = t₀ := by ring
    rw [hfn, ht] at hshift
    exact hshift

end ChartCenteredLift

/-! ## First-derivative clauses of `HasGeodesicEquationAt` -/

section FirstDerivative

variable [I.Boundaryless] [CompleteSpace E]

/-- **First-derivative clause.** If `f` is a chart-`γ(t₀)`-centred
integral curve of the geodesic VF at `t₀` with `(f t).proj = γ t` for
all `t`, then `chartLocalCurve γ t₀` admits a `HasDerivAt` at `t₀` with
derivative the first component of `geodesicVectorFieldChart g (γ t₀) (f t₀)`. -/
theorem hasDerivAt_chartLocalCurve_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasDerivAt (chartLocalCurve (I := I) γ t₀)
      ((geodesicVectorFieldChart (I := I) g (γ t₀) (f t₀) : E × E).1) t₀ := by
  classical
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := γ t₀) (t₀ := t₀) (f := f) hf
  have hpush_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g (γ t₀) f t₀ t₀) t₀ := hpush.self_of_nhds
  -- Take the first component: compose with `Prod.fst : E × E → E` (a CLM).
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
    hasFDerivAt_fst
  have hfst : HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
      ((chartPushVF (I := I) g (γ t₀) f t₀ t₀).1) t₀ :=
    hfst_clm.comp_hasDerivAt t₀ hpush_t₀
  rw [chartPushVF_self (I := I) g (γ t₀) f t₀] at hfst
  have hfst_eq : (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
      chartLocalCurve (I := I) γ t₀ := by
    funext t
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ t,
      chartLocalCurve_def]
  rw [hfst_eq] at hfst
  exact hfst

/-- **Eventually first-derivative clause.** On a neighbourhood of `t₀`,
the chart-local curve has a `HasDerivAt` at every nearby `s`, equal to
its `deriv` at `s`. -/
theorem eventually_hasDerivAt_chartLocalCurve_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    ∀ᶠ s in nhds t₀, HasDerivAt (chartLocalCurve (I := I) γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) s) s := by
  classical
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := γ t₀) (t₀ := t₀) (f := f) hf
  filter_upwards [hpush] with s hs
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
    hasFDerivAt_fst
  have hfst : HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
      ((chartPushVF (I := I) g (γ t₀) f t₀ s).1) s :=
    hfst_clm.comp_hasDerivAt s hs
  have hfst_eq : (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
      chartLocalCurve (I := I) γ t₀ := by
    funext t
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ t,
      chartLocalCurve_def]
  rw [hfst_eq] at hfst
  have hderiv : deriv (chartLocalCurve (I := I) γ t₀) s =
      (chartPushVF (I := I) g (γ t₀) f t₀ s).1 := hfst.deriv
  rw [hderiv]
  exact hfst

end FirstDerivative

/-! ## Conditional headline: from the autonomous phase identity

The full bridge `IsGeodesicAt → HasGeodesicEquationAt` follows once the
chart-pushed VF is identified with the autonomous chart-coordinate
phase-space VF on a neighbourhood of the base time, i.e.

```
chartPushVF g (γ t₀) f t₀ s = chartPhaseVF g (γ t₀) (chartPushLift f t₀ s)
```

eventually as `s → t₀`. This identity captures the "geodesic ODE in
chart coordinates" in autonomous form. Below we package the
chart-centred bridge as a theorem that *takes the identity as a
hypothesis*; the unconditional version requires proving the identity
itself, which lives in a separate follow-up.

The advantage of this packaging: every clause of `HasGeodesicEquationAt`
is derived here, so the follow-up reduces to proving the single
phase identity. -/

section ConditionalHeadline

variable [I.Boundaryless] [CompleteSpace E]

/-- **Conditional chart-centred bridge.** Given the autonomous
phase-space identity for the chart-pushed lift on a neighbourhood of
`t₀`, the chart-coordinate second-derivative form of the geodesic
equation holds at `t₀`.

The hypothesis `hphase` is the chart-coordinate ODE identity in
autonomous form: the chart-pushed phase-space VF coincides with the
autonomous chart phase-space VF, evaluated on the chart-pushed lift,
on a neighbourhood of the base time. -/
theorem hasGeodesicEquationAt_of_chartCentered_of_phase_identity
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀)
    (hphase : ∀ᶠ s in nhds t₀,
      chartPushVF (I := I) g (γ t₀) f t₀ s =
        chartPhaseVF (I := I) g (γ t₀) (chartPushLift (I := I) f t₀ s)) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  set β : M := γ t₀ with hβ_def
  -- Get the chart-pushed eventually-derivative formula.
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := β) (t₀ := t₀) (f := f) hf
  -- Combine with the phase identity: `Φ' s = chartPhaseVF g β (Φ s)` eventually.
  have hphase_push : ∀ᶠ s in nhds t₀, HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)) s := by
    filter_upwards [hpush, hphase] with s hs hs_eq
    rw [← hs_eq]; exact hs
  -- Define u(s) := (Φ s).1, w(s) := (Φ s).2. The phase identity gives:
  --   u'(s) = w(s)
  --   w'(s) = -Γ_β(w(s), w(s)) u(s)
  -- At s = t₀, set v := w(t₀), a := w'(t₀) = -Γ_β(v, v) u(t₀).
  set u : ℝ → E := fun s => (chartPushLift (I := I) f t₀ s).1 with hu_def
  set w : ℝ → E := fun s => (chartPushLift (I := I) f t₀ s).2 with hw_def
  -- Identify u with chartLocalCurve γ t₀.
  have hu_eq : u = chartLocalCurve (I := I) γ t₀ := by
    funext s
    change (chartPushLift (I := I) f t₀ s).1 = chartLocalCurve (I := I) γ t₀ s
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ s,
      chartLocalCurve_def]
  -- Velocity v := w t₀.
  set v : E := w t₀ with hv_def
  -- Acceleration a := -Γ_β(v, v) (u t₀).
  set a : E := - chartChristoffelContraction (I := I) g β v v (u t₀) with ha_def
  -- u t₀ = extChartAt I β β = extChartAt I (γ t₀) (γ t₀).
  have hu_t₀ : u t₀ = extChartAt I β (γ t₀) := by
    rw [hu_eq, chartLocalCurve_def]
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · -- First derivative: HasDerivAt (chartLocalCurve γ t₀) v t₀.
    -- From hphase_push at t₀: HasDerivAt Φ (chartPhaseVF g β (Φ t₀)) t₀.
    -- The first component: HasDerivAt u ((chartPhaseVF g β (Φ t₀)).1) t₀.
    -- (chartPhaseVF g β z).1 = z.2 by definition.
    have hphase_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)) t₀ :=
      hphase_push.self_of_nhds
    have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
        (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
      hasFDerivAt_fst
    have hu_deriv : HasDerivAt u
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)).1) t₀ :=
      hfst_clm.comp_hasDerivAt t₀ hphase_t₀
    -- The first component of `chartPhaseVF g β z` is `z.2`.
    have hPhVF : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ t₀)).1 = w t₀ := by
      change (chartPushLift (I := I) f t₀ t₀).2 = w t₀
      rfl
    rw [hPhVF, ← hv_def, hu_eq] at hu_deriv
    exact hu_deriv
  · -- Eventually: chartLocalCurve has HasDerivAt at every nearby s.
    filter_upwards [hphase_push] with s hs
    have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
        (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
      hasFDerivAt_fst
    have hu_deriv : HasDerivAt u
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)).1) s :=
      hfst_clm.comp_hasDerivAt s hs
    have hPhVF : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ s)).1 = w s := by
      change (chartPushLift (I := I) f t₀ s).2 = w s
      rfl
    rw [hPhVF] at hu_deriv
    rw [hu_eq] at hu_deriv
    -- hu_deriv : HasDerivAt (chartLocalCurve γ t₀) (w s) s.
    -- We want: HasDerivAt (chartLocalCurve γ t₀) (deriv (chartLocalCurve γ t₀) s) s.
    -- These agree because `w s = deriv (chartLocalCurve γ t₀) s`.
    have : deriv (chartLocalCurve (I := I) γ t₀) s = w s := hu_deriv.deriv
    rw [this]
    exact hu_deriv
  · -- Second derivative: HasDerivAt (s ↦ deriv (chartLocalCurve γ t₀) s) a t₀.
    -- We have eventually `deriv (chartLocalCurve γ t₀) s = w s`. So it suffices
    -- to show `HasDerivAt w a t₀`.
    -- Approach: `w s = (Φ s).2`. Apply `Prod.snd` (a CLM) to the chart-pushed
    -- HasDerivAt. The derivative of `w` at t₀ is the second component of the
    -- chart-pushed VF at t₀, which by the phase identity equals
    -- `(chartPhaseVF g β (Φ t₀)).2 = -Γ_β(v, v) u(t₀) = a`.
    have heventually_eq : (fun s => deriv (chartLocalCurve (I := I) γ t₀) s) =ᶠ[𝓝 t₀] w := by
      filter_upwards [hphase_push] with s hs
      have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
          (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
        hasFDerivAt_fst
      have hu_deriv : HasDerivAt u
          ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)).1) s :=
        hfst_clm.comp_hasDerivAt s hs
      have hPhVF : (chartPhaseVF (I := I) g β
          (chartPushLift (I := I) f t₀ s)).1 = w s := by
        change (chartPushLift (I := I) f t₀ s).2 = w s
        rfl
      rw [hPhVF] at hu_deriv
      rw [hu_eq] at hu_deriv
      exact hu_deriv.deriv
    -- Use congr_of_eventuallyEq to transfer HasDerivAt from w to `deriv …`.
    -- Compute HasDerivAt w a t₀.
    have hphase_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)) t₀ :=
      hphase_push.self_of_nhds
    have hsnd_clm : HasFDerivAt (Prod.snd : E × E → E)
        (ContinuousLinearMap.snd ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
      hasFDerivAt_snd
    have hw_deriv : HasDerivAt w
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)).2) t₀ :=
      hsnd_clm.comp_hasDerivAt t₀ hphase_t₀
    -- `(chartPhaseVF g β z).2 = -Γ_β(z.2, z.2) z.1` by definition.
    have hPhVF_snd : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ t₀)).2 = a := by
      change -chartChristoffelContraction (I := I) g β
          (chartPushLift (I := I) f t₀ t₀).2
          (chartPushLift (I := I) f t₀ t₀).2
          (chartPushLift (I := I) f t₀ t₀).1 = a
      rw [ha_def, hv_def, hw_def, hu_def]
    rw [hPhVF_snd] at hw_deriv
    -- Transfer via congr_of_eventuallyEq.
    exact hw_deriv.congr_of_eventuallyEq heventually_eq
  · -- Algebraic identity: `a + Γ_β(v, v) (extChartAt I β β) = 0`.
    -- a = -Γ_β(v, v) u(t₀) and u(t₀) = extChartAt I β (γ t₀) = extChartAt I β β.
    rw [hu_t₀] at ha_def
    rw [ha_def]
    -- The goal: -Γ_β(v, v)(extChartAt I β β) + Γ_β(v, v)(extChartAt I β β) = 0
    -- — but wait, the goal uses `γ t₀` not `β`. They're defeq via hβ_def.
    change -chartChristoffelContraction (I := I) g β v v (extChartAt I β β) +
      chartChristoffelContraction (I := I) g (γ t₀) v v
        (extChartAt I (γ t₀) (γ t₀)) = 0
    rw [← hβ_def]; abel

end ConditionalHeadline

/-! ## Unconditional chart-centred bridge

We now discharge the autonomous phase-space identity hypothesis of
`hasGeodesicEquationAt_of_chartCentered_of_phase_identity`. The key
ingredient is `chartPushVF_eq_chartPhaseVF_at`
(`Exponential/ChartPushVFEq.lean`), which gives the pointwise identity
`chartPushVF g α f t₀ s = chartPhaseVF g α (chartPushLift f t₀ s)`
whenever `(f t₀).proj = α` and `(f s).proj ∈ (chartAt H α).source`. The
chart-source condition holds on a neighbourhood of `t₀` because `f` is
continuous at `t₀` (as an integral curve) and `(f t₀).proj = γ t₀`
lies in the chart source at `γ t₀`. -/

section UnconditionalChartCentered

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable [I.Boundaryless] [CompleteSpace E]

/-- **Eventually-form of the autonomous phase identity** for a
chart-`γ(t₀)`-centred integral curve. When `(f t).proj = γ t` for all
`t` and `f` is a local integral curve of `geodesicVectorFieldChart g (γ t₀)`
at `t₀`, the chart-pushed phase-space VF and the autonomous chart phase
VF agree on a neighbourhood of `t₀`. -/
theorem chartPushVF_eventually_eq_chartPhaseVF_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    ∀ᶠ s in nhds t₀,
      chartPushVF (I := I) g (γ t₀) f t₀ s =
        chartPhaseVF (I := I) g (γ t₀) (chartPushLift (I := I) f t₀ s) := by
  classical
  -- The pointwise alignment hypothesis `(f t₀).proj = γ t₀`.
  have hft₀_proj : (f t₀).proj = γ t₀ := hproj t₀
  -- Eventually `(f s).proj ∈ (chartAt H (γ t₀)).source`.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hcomp : ContinuousAt (fun s => (f s).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  have hα_open : IsOpen (chartAt H (γ t₀)).source :=
    (chartAt H (γ t₀)).open_source
  have hα_mem : γ t₀ ∈ (chartAt H (γ t₀)).source :=
    mem_chart_source H (γ t₀)
  have hα_nhds : (chartAt H (γ t₀)).source ∈ nhds (γ t₀) :=
    hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun s => (f s).proj) ⁻¹' (chartAt H (γ t₀)).source ∈
      nhds t₀ := by
    apply hcomp.preimage_mem_nhds
    rw [hft₀_proj]
    exact hα_nhds
  filter_upwards [hsrc_nhds] with s hs
  -- `chartPushVF_eq_chartPhaseVF_at` discharges the equality pointwise.
  exact chartPushVF_eq_chartPhaseVF_at (I := I) g (γ t₀)
    (f := f) (t₀ := t₀) hft₀_proj s hs

/-- **Unconditional chart-centred bridge.** If `f` is a chart-`γ(t₀)`-
centred lift of `γ` (i.e. `(f t).proj = γ t` for all `t` and `f` is a
local integral curve of `geodesicVectorFieldChart g (γ t₀)` at `t₀`),
then `γ` satisfies the chart-coordinate second-derivative form of the
geodesic equation at `t₀`.

This composes the conditional headline
`hasGeodesicEquationAt_of_chartCentered_of_phase_identity` with the
unconditional autonomous phase-space identity
`chartPushVF_eq_chartPhaseVF_at`: the only remaining hypothesis is the
chart-centring `(f t).proj = γ t` jointly with the integral-curve
property at the chart-`γ(t₀)`-fixed VF. -/
theorem hasGeodesicEquationAt_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ :=
  hasGeodesicEquationAt_of_chartCentered_of_phase_identity
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf
    (chartPushVF_eventually_eq_chartPhaseVF_of_chartCentered
      (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf)

/-- **Existence form of the chart-centred bridge.** For any manifold
curve `γ` admitting a chart-`γ(t₀)`-centred lift at `t₀`, `γ` satisfies
the chart-coordinate second-derivative form of the geodesic equation at
`t₀`.

This is the existence-quantified packaging of
`hasGeodesicEquationAt_of_chartCentered`: the lift `f` is folded into an
existential. Use this when the chart-centred witness is supplied by an
upstream Picard–Lindelöf invocation at the basepoint `γ(t₀)`. -/
theorem hasGeodesicEquationAt_of_exists_chartCentered_lift
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (h : ∃ f : ℝ → TangentBundle I M,
      (∀ t, (f t).proj = γ t) ∧
      IsMIntegralCurveAt f
        (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f, hproj, hf⟩ := h
  exact hasGeodesicEquationAt_of_chartCentered
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf

/-- **`IsGeodesicAt` bridge, chart-centred case.** A local geodesic
`γ` at `t₀` whose `IsGeodesicAt`-witness has chart basepoint coinciding
with `γ(t₀)` (the chart-centred case) satisfies the chart-coordinate
geodesic equation at `t₀`.

The hypothesis `hα : α = γ t₀` selects the chart-centred witnesses: any
`IsGeodesicAt`-data `(α, f)` with `α = γ t₀` is fed directly into
`hasGeodesicEquationAt_of_chartCentered`. -/
theorem IsGeodesicAt.hasGeodesicEquationAt_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀)
    (hα : (hγ.choose) = γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  -- Unpack the existential structure of `IsGeodesicAt`.
  obtain ⟨hproj, _hα_src, hf⟩ := hγ.choose_spec.choose_spec
  -- `hγ.choose = α`, the witness basepoint. After `hα`, it equals `γ t₀`.
  -- Rewrite the chart-fixed VF in `hf` accordingly.
  set f : ℝ → TangentBundle I M := hγ.choose_spec.choose with hf_def
  -- `hf : IsMIntegralCurveAt f (geodesicVectorFieldChart g hγ.choose) t₀`,
  -- and `hα` lets us replace `hγ.choose` by `γ t₀`.
  rw [hα] at hf
  exact hasGeodesicEquationAt_of_chartCentered
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf

end UnconditionalChartCentered

/-! ## Cross-VF reduction: from arbitrary chart basepoint to `γ(t₀)`

We now handle the general case of `IsGeodesicAt → HasGeodesicEquationAt`,
in which the witness chart basepoint `α : M` need not coincide with
`γ(t₀)`. The strategy is to construct a **chart-`γ(t₀)`-centred** lift
`f₁` via Picard–Lindelöf at the tangent-bundle point `f t₀`, then bridge
this chart-centred witness into `HasGeodesicEquationAt`, and finally
transfer along the local equality `γ =ᶠ[𝓝 t₀] projectCurve f₁` derived
from manifold-level integral-curve uniqueness on `TM`.

The transfer hinges on a `HasGeodesicEquationAt.congr_of_eventuallyEq_at`
lemma: the predicate `HasGeodesicEquationAt g γ t₀` is a local property
of `γ` at `t₀` — it only references `γ` through `chartLocalCurve γ t₀`,
which equals `extChartAt I (γ t₀) ∘ γ`. -/

section CrossVFReduction

variable [I.Boundaryless] [CompleteSpace E]

/-- **Local invariance of `HasGeodesicEquationAt`.** If two curves
`γ, γ'` agree on a neighbourhood of `t₀` (in particular, `γ t₀ = γ' t₀`),
then `HasGeodesicEquationAt g γ' t₀` implies `HasGeodesicEquationAt g γ t₀`.

The predicate `HasGeodesicEquationAt` depends on `γ` only through
`chartLocalCurve γ t₀ s = extChartAt I (γ t₀) (γ s)`. Local equality of
`γ` and `γ'` near `t₀`, together with equality of the basepoint
`γ t₀ = γ' t₀`, makes `chartLocalCurve γ t₀ =ᶠ[𝓝 t₀] chartLocalCurve γ' t₀`,
allowing the derivative clauses to transfer via `HasDerivAt.congr_of_eventuallyEq`. -/
theorem HasGeodesicEquationAt.congr_of_eventuallyEq_at
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t₀ : ℝ}
    (hγt₀ : γ t₀ = γ' t₀)
    (heq : γ =ᶠ[𝓝 t₀] γ')
    (h : HasGeodesicEquationAt (I := I) g γ' t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  -- chartLocalCurve γ t₀ s = extChartAt I (γ t₀) (γ s). Replace γ by γ' via heq, and
  -- γ t₀ by γ' t₀ via hγt₀.
  have hcurve_eq : chartLocalCurve (I := I) γ t₀ =ᶠ[𝓝 t₀]
      chartLocalCurve (I := I) γ' t₀ := by
    filter_upwards [heq] with s hs
    change extChartAt I (γ t₀) (γ s) = extChartAt I (γ' t₀) (γ' s)
    rw [hγt₀, hs]
  obtain ⟨v, a, hv, hev, ha, halg⟩ := h
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · -- HasDerivAt (chartLocalCurve γ t₀) v t₀. Transfer via congr_of_eventuallyEq.
    -- hv : HasDerivAt (chartLocalCurve γ' t₀) v t₀.
    -- Need eventually-eq in the form γ t₀-side =ᶠ γ' t₀-side: that's hcurve_eq.
    exact hv.congr_of_eventuallyEq hcurve_eq
  · -- Eventually clause.
    have hev_eq_nhds : ∀ᶠ s in 𝓝 t₀,
        chartLocalCurve (I := I) γ t₀ =ᶠ[𝓝 s] chartLocalCurve (I := I) γ' t₀ :=
      hcurve_eq.eventually_nhds
    filter_upwards [hev, hev_eq_nhds] with s hs hs_nhds
    -- hs : HasDerivAt (chartLocalCurve γ' t₀) (deriv (chartLocalCurve γ' t₀) s) s.
    -- hs_nhds : chartLocalCurve γ t₀ =ᶠ[𝓝 s] chartLocalCurve γ' t₀.
    have hderiv_eq : deriv (chartLocalCurve (I := I) γ t₀) s =
        deriv (chartLocalCurve (I := I) γ' t₀) s :=
      Filter.EventuallyEq.deriv_eq hs_nhds
    rw [hderiv_eq]
    exact hs.congr_of_eventuallyEq hs_nhds
  · -- HasDerivAt (s ↦ deriv (chartLocalCurve γ t₀) s) a t₀.
    -- ha : HasDerivAt (s ↦ deriv (chartLocalCurve γ' t₀) s) a t₀.
    -- Need eventually-eq: (s ↦ deriv γ t₀ s) =ᶠ (s ↦ deriv γ' t₀ s).
    have hderiv_eventually : (fun s => deriv (chartLocalCurve (I := I) γ t₀) s) =ᶠ[𝓝 t₀]
        (fun s => deriv (chartLocalCurve (I := I) γ' t₀) s) := by
      filter_upwards [hcurve_eq.eventually_nhds] with s hs_nhds
      exact Filter.EventuallyEq.deriv_eq hs_nhds
    exact ha.congr_of_eventuallyEq hderiv_eventually
  · -- Algebraic identity. Both sides use γ t₀, which equals γ' t₀ by hγt₀.
    rw [hγt₀]
    exact halg

/-- **Construction of a chart-`γ(t₀)`-centred lift agreeing with the
original witness lift at `t₀`.** From a general `IsGeodesicAt`-witness
`(α, f)` of `γ` at `t₀`, construct a chart-`γ(t₀)`-centred integral
curve `f₁` with `f₁ t₀ = f t₀` (same point in `TangentBundle I M`).

Picard–Lindelöf is applied to the chart-`γ(t₀)`-fixed geodesic vector
field at `f t₀ = ⟨γ t₀, (f t₀).snd⟩`. The latter equality holds because
`(f t₀).proj = γ t₀` (witness projection identity) and `TotalSpace.eta`. -/
lemma exists_chartCenteredLift_at_lift_eq
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj_t₀ : (f t₀).proj = γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      f₁ t₀ = f t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ := by
  -- Use exists_chartCenteredLift_at at point γ t₀ with velocity
  -- ((f t₀).snd : TangentSpace I (f t₀).proj = E = TangentSpace I (γ t₀) by defeq).
  -- TangentSpace I p reduces to E definitionally.
  obtain ⟨f₁, hf₁_init, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  refine ⟨f₁, ?_, hf₁⟩
  -- hf₁_init : f₁ t₀ = ⟨γ t₀, (f t₀).snd⟩. Need: f₁ t₀ = f t₀.
  rw [hf₁_init, ← hproj_t₀]

/-- **`IsGeodesicAt → HasGeodesicEquationAt`, conditional on cross-VF
projection-uniqueness.** A local geodesic `γ` at `t₀` (witness `(α, f)`)
admits the chart-coordinate second-derivative form of the geodesic
equation at `t₀`, provided one can supply a chart-`γ(t₀)`-centred
integral curve `f₁` whose projection agrees with `γ` on a neighbourhood
of `t₀`.

The hypothesis `hf₁_init : f₁ t₀ = f t₀` and the chart-centred
integral-curve property `hf₁` are produced by Picard–Lindelöf via
`exists_chartCenteredLift_at_lift_eq`. The local agreement
`γ =ᶠ[𝓝 t₀] projectCurve f₁` is the cross-VF projection-uniqueness; it
expresses **chart-invariance of the geodesic flow on `TM`** in the form
suitable for the bridge.

This packaging exposes the cross-VF reduction as a single hypothesis,
which downstream consumers can discharge from a chart-invariance fact
on the geodesic spray (the chart-transition law for the `(0, 2)`-tensor
form of Christoffel symbols at the foot point). -/
theorem IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (_hγ : IsGeodesicAt (I := I) g γ t₀)
    {f₁ : ℝ → TangentBundle I M}
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀)
    (hf₁_proj_t₀ : (f₁ t₀).proj = γ t₀)
    (hcross : γ =ᶠ[𝓝 t₀] projectCurve (I := I) f₁) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  -- f₁'s projection is γ_alt := projectCurve f₁.
  set γ_alt : ℝ → M := projectCurve (I := I) f₁ with hγ_alt_def
  -- γ_alt t₀ = (f₁ t₀).proj = γ t₀.
  have hγ_alt_t₀ : γ_alt t₀ = γ t₀ := hf₁_proj_t₀
  have hproj_alt : ∀ t, (f₁ t).proj = γ_alt t := fun t => rfl
  -- hf₁ uses chart basepoint γ t₀; rewrite to γ_alt t₀ (defeq).
  have hf₁_alt : IsMIntegralCurveAt f₁
      (geodesicVectorFieldChart (I := I) g (γ_alt t₀)) t₀ := by
    rw [hγ_alt_t₀]; exact hf₁
  -- Apply the chart-centred bridge to γ_alt.
  have h_alt : HasGeodesicEquationAt (I := I) g γ_alt t₀ :=
    hasGeodesicEquationAt_of_chartCentered (I := I) (g := g) (γ := γ_alt)
      (t₀ := t₀) (f := f₁) hproj_alt hf₁_alt
  -- Transfer to γ via the eventually-equality.
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
    (γ := γ) (γ' := γ_alt) (t₀ := t₀) hγ_alt_t₀.symm hcross h_alt

end CrossVFReduction

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
