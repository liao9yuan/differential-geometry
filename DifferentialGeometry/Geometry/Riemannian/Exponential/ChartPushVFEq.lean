import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness

set_option linter.unusedSectionVars false

/-!
# Identification of `chartPushVF` with `chartPhaseVF`

The Mathlib lemma `IsMIntegralCurveAt.eventually_hasDerivAt` produces a
derivative formula for the chart-pushed lift in terms of
`tangentCoordChange I.tangent`. This file shows that, when applied to the
chart-fixed geodesic vector field `geodesicVectorFieldChart g α` and the
chart basepoint chosen as `α = (f 0).proj`, the resulting
`chartPushVF g α f 0 t` coincides with the value of the chart-coordinate
phase-space geodesic vector field `chartPhaseVF g α` at the chart-pushed
lift's current position `chartPushLift f 0 t`.

The proof uses two key ingredients:

* The Mathlib identity
  `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`, which
  rewrites the trivialisation of the tangent bundle `T(TM) → TM` at
  `⟨α, 0⟩` in terms of the change-of-coordinates of `tangentBundleCore`
  on the manifold `TM`.

* The chart-of-`TM` identification `extChartAt_tangent_eq_at_proj`, which
  shows that the chart of `TangentBundle I M` at any point only depends
  on the projection, so the chart at `f 0 = ⟨α, v⟩` coincides with the
  chart at `⟨α, 0⟩`.

## Main results

* `tangentCoordChange_tangent_geodesicVF` — the chart-`f 0`-coordinate of
  the geodesic vector field at `f t`, obtained via the tangent-bundle
  coordinate change on `TM`, equals
  `geodesicVectorFieldChartFiber g α (f t)`.

* `chartPushVF_eq_geodesicVectorFieldChartFiber` — equivalent restatement
  of the above in terms of `chartPushVF`.

* `geodesicVectorFieldChartFiber_eq_chartPhaseVF` — the chart-α-fixed
  fibre form of the geodesic vector field at `f t` equals the chart-phase
  vector field evaluated at the chart-pushed lift's current position.

* `chartPushVF_eq_chartPhaseVF` — the headline identification:
  `chartPushVF g α f 0 t = chartPhaseVF g α (chartPushLift f 0 t)` on the
  chart-α domain (with `α = (f 0).proj`).

* `chartPushLift_eventually_hasDerivAt_chartPhaseVF` — the chart-pushed
  lift's eventual `HasDerivAt`-formula upgraded to the `chartPhaseVF`
  form. This unconditionally discharges the chart-phase-ODE hypothesis
  in the bridge headline.

* `chartPushedFlow_eq_maximalGeodesicChosenCurve_eventually_unconditional`
  — unconditional closure of the bridge headline against
  `maximalGeodesicChosenCurve`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

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

/-! ## Achart-equality from projection equality

`achart` on `TM` only sees the projection, so two points with the same
projection give the same achart. -/

section AchartEquality

/-- The achart on `TM` (indexed by `ModelProd H E`) depends only on the
projection: two points with equal projections give the same achart. -/
lemma achart_modelProd_eq_of_proj_eq {q₁ q₂ : TangentBundle I M}
    (h : q₁.proj = q₂.proj) :
    achart (ModelProd H E) q₁ = achart (ModelProd H E) q₂ := by
  -- `achart H₀ x = ⟨chartAt H₀ x, _⟩`, and `chartAt (ModelProd H E) q` only
  -- depends on `q.1 = q.proj` (cf. `TangentBundle.chartAt`).
  refine Subtype.ext ?_
  change chartAt (ModelProd H E) q₁ = chartAt (ModelProd H E) q₂
  rw [TangentBundle.chartAt q₁, TangentBundle.chartAt q₂, h]

end AchartEquality

/-! ## Identifying `tangentCoordChange I.tangent` via the trivialisation

For a point `q : TM` with `q.proj` in `(chartAt H α).source`, the
trivialisation of `T(TM)` at `⟨α, 0⟩` evaluated linearly at `q` coincides
with the coordinate change `tangentCoordChange I.tangent q ⟨α, 0⟩ q`. -/

section TangentCoordChange

/-- The chart at `⟨α, 0⟩` on `TM` source contains `q : TM` iff
`q.proj ∈ (chartAt H α).source`. -/
lemma mem_chartAt_modelProd_zero_source_iff
    (α : M) (q : TangentBundle I M) :
    q ∈ (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source ↔
      q.proj ∈ (chartAt H α).source := by
  -- `TangentBundle.mem_chart_source_iff` reduces it to first-coord membership.
  exact TangentBundle.mem_chart_source_iff (I := I) (M := M) q
    (⟨α, (0 : E)⟩ : TangentBundle I M)

/-- For `q : TM` with `q.proj ∈ (chartAt H α).source`,
`(triv (E×E) (TangentSpace I.tangent) ⟨α, 0⟩).continuousLinearMapAt ℝ q`
coincides with the `tangentBundleCore I.tangent TM` coordinate change
from the achart at `q` to the achart at `⟨α, 0⟩`, evaluated at `q`. -/
lemma trivializationAt_tangent_continuousLinearMapAt_eq_core
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ q =
      (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
        (achart (ModelProd H E) q)
        (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q := by
  -- Instantiate `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`
  -- at the manifold `TM`, model-with-corners `I.tangent`, model space
  -- `E × E`, model topological space `ModelProd H E`. Base points: `b₀ = ⟨α, 0⟩`,
  -- `b = q`. Hypothesis: `q ∈ (chartAt (ModelProd H E) ⟨α, 0⟩).source`,
  -- equivalent to `q.proj ∈ (chartAt H α).source` via
  -- `TangentBundle.mem_chart_source_iff`.
  have hq_src : q ∈
      (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α q).mpr hq
  exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := q) hq_src

/-- For `q : TM` with `q.proj ∈ (chartAt H α).source`, the value of
`tangentCoordChange I.tangent q ⟨α, 0⟩ q : (E × E) →L[ℝ] (E × E)`
applied to any `V ∈ E × E` equals the trivialisation's
`continuousLinearMapAt` at `q` applied to `V`. -/
lemma tangentCoordChange_tangent_eq_triv
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) (V : E × E) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q V =
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ q V := by
  -- `tangentCoordChange I.tangent q₁ q₂ z` is by definition the
  -- `tangentBundleCore`-coordChange from the achart at `q₁` to the achart
  -- at `q₂` evaluated at `z`. Rewrite using
  -- `trivializationAt_tangent_continuousLinearMapAt_eq_core` (in the
  -- reverse direction).
  rw [trivializationAt_tangent_continuousLinearMapAt_eq_core (I := I) α q hq]
  rfl

/-- The chart change `tangentCoordChange I.tangent q ⟨α, 0⟩ q`, applied to
the symm-image of `(v_fiber : E × E)` under the trivialisation of `T(TM)`
at `⟨α, 0⟩` taken at `q`, returns `v_fiber`. This is the central
"chart-coord extraction" property: the trivialisation's `.symm`
inverts to `.continuousLinearMapAt` on the base set. -/
lemma tangentCoordChange_tangent_symm_apply
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) (v_fiber : E × E) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q
      ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symm q v_fiber) = v_fiber := by
  classical
  -- `q ∈ baseSet` iff `q.proj ∈ (chartAt H α).source` (via
  -- `TangentBundle.trivializationAt_baseSet`).
  have hq_base : q ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (mem_chartAt_modelProd_zero_source_iff (I := I) α q).mpr hq
  -- Rewrite the LHS via the trivialisation-CLM identification.
  rw [tangentCoordChange_tangent_eq_triv (I := I) α q hq]
  -- Now the goal is `triv.continuousLinearMapAt ℝ q (triv.symm q v_fiber) = v_fiber`.
  -- This is `Bundle.Trivialization.continuousLinearMapAt_symmL`, observing
  -- that `triv.symm b = triv.symmL ℝ b` as a function.
  -- Convert `triv.symm q v_fiber = triv.symmL ℝ q v_fiber` and apply the inverse lemma.
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hsymm : e.symm q v_fiber = e.symmL ℝ q v_fiber := by
    -- `Trivialization.symmL_apply` (in `Mathlib/Topology/VectorBundle/Basic.lean`)
    -- gives `e.symmL ℝ q v = e.symm q v` definitionally.
    rfl
  rw [hsymm]
  -- Apply `continuousLinearMapAt_symmL`.
  exact e.continuousLinearMapAt_symmL hq_base v_fiber

/-- Specialisation: applied to `geodesicVectorFieldChart g α q`, the
chart change returns `geodesicVectorFieldChartFiber g α q`. -/
lemma tangentCoordChange_tangent_geodesicVF
    (g : SmoothRiemannianMetric I M) (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q
      (geodesicVectorFieldChart (I := I) g α q) =
        geodesicVectorFieldChartFiber (I := I) g α q := by
  -- Unfold `geodesicVectorFieldChart` and apply `tangentCoordChange_tangent_symm_apply`.
  unfold geodesicVectorFieldChart
  exact tangentCoordChange_tangent_symm_apply (I := I) α q hq
    (geodesicVectorFieldChartFiber (I := I) g α q)

end TangentCoordChange

/-! ## Identifying `chartPushVF` with `chartPhaseVF`

We package the previous identity in the form used by the bridge: when
`f 0 = ⟨α, v⟩` (so `(f 0).proj = α`), the chart-pushed vector field
`chartPushVF g α f 0 t` equals
`chartPhaseVF g α (chartPushLift f 0 t)` for any `t` with
`(f t).proj ∈ (chartAt H α).source`. -/

section ChartPushVFEq

variable [I.Boundaryless]

/-- When `(f 0).proj = α`, the achart of `TM` at `f 0` equals the achart
at `⟨α, 0⟩`. -/
lemma achart_modelProd_f0_eq
    {f : ℝ → TangentBundle I M} {α : M}
    (hf0_proj : (f 0).proj = α) :
    achart (ModelProd H E) (f 0) =
      achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M) := by
  apply achart_modelProd_eq_of_proj_eq (I := I)
  -- Goal: `(f 0).proj = (⟨α, (0 : E)⟩ : TangentBundle I M).proj`, i.e. `(f 0).proj = α`.
  exact hf0_proj

/-- When `(f 0).proj = α`, `tangentCoordChange I.tangent q (f 0) q`
coincides with `tangentCoordChange I.tangent q ⟨α, 0⟩ q`. -/
lemma tangentCoordChange_tangent_f0_eq
    {f : ℝ → TangentBundle I M} {α : M}
    (hf0_proj : (f 0).proj = α) (q : TangentBundle I M) :
    tangentCoordChange I.tangent q (f 0) q =
      tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q := by
  -- `tangentCoordChange I.tangent q₁ q₂ z` is `coordChange (achart q₁) (achart q₂) z`.
  -- The right-hand achart at `f 0` and at `⟨α, 0⟩` agree, so the coord changes
  -- agree.
  change (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q) (achart (ModelProd H E) (f 0)) q =
    (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q)
      (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q
  rw [achart_modelProd_f0_eq (I := I) (f := f) (α := α) hf0_proj]

/-- **`chartPushVF` in terms of `geodesicVectorFieldChartFiber`.** When
`(f 0).proj = α` and `(f t).proj ∈ (chartAt H α).source`,
`chartPushVF g α f 0 t = geodesicVectorFieldChartFiber g α (f t)`. -/
theorem chartPushVF_eq_geodesicVectorFieldChartFiber
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f 0 t =
      geodesicVectorFieldChartFiber (I := I) g α (f t) := by
  -- Unfold `chartPushVF`.
  unfold chartPushVF
  -- Reduce `tangentCoordChange ... (f 0) ...` to `tangentCoordChange ... ⟨α, 0⟩ ...`.
  rw [tangentCoordChange_tangent_f0_eq (I := I) hf0_proj (f t)]
  -- Apply `tangentCoordChange_tangent_geodesicVF`.
  exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f t) ht

/-- The chart-α fibre form of the geodesic vector field at `f t` matches
the chart-phase vector field evaluated at the chart-pushed lift's
current position. -/
theorem geodesicVectorFieldChartFiber_eq_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α (f t) =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) := by
  classical
  -- Both pairs `(chartFiberCoord α (f t), -Γ_α(...)(extChartAt I α (f t).proj))`.
  have hpair : chartPushLift (I := I) f 0 t =
      (extChartAt I α (f t).proj, chartFiberCoord (I := I) α (f t)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := 0) (t := t) ?_
    · -- `(f 0).proj = α`, so the RHS rewrites.
      rw [h_eq]
      rw [hf0_proj]
    · -- `(f t).proj ∈ (chartAt H (f 0).proj).source`: substitute `(f 0).proj = α`.
      rw [hf0_proj]; exact ht
  rw [hpair]
  -- Now `chartPhaseVF g α (x, v) = (v, -Γ_α(v, v)(x))`.
  -- `geodesicVectorFieldChartFiber g α (f t) = (chartFiberCoord α (f t),
  --   -chartChristoffelContraction g α (chartFiberCoord α (f t)) (chartFiberCoord α (f t))
  --     (extChartAt I α (f t).proj))`.
  rfl

/-- **Headline identification.** When `(f 0).proj = α` and
`(f t).proj ∈ (chartAt H α).source`, the chart-pushed vector field
`chartPushVF g α f 0 t` agrees with the chart-phase vector field
evaluated at the chart-pushed lift's current position. -/
theorem chartPushVF_eq_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f 0 t =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) := by
  rw [chartPushVF_eq_geodesicVectorFieldChartFiber (I := I) g α
        hf0_proj t ht]
  exact geodesicVectorFieldChartFiber_eq_chartPhaseVF (I := I) g α
    hf0_proj t ht

/-! ### Generalisation to an arbitrary base time `t₀`

The chart-pushed/chart-phase identification packaged in
`chartPushVF_eq_chartPhaseVF` is autonomous in the sense that nothing
above singles out `t = 0`: the base time `0` appears only as the index
into the curve `f` chosen to align with the basepoint `α`. We mirror the
lemma chain with an arbitrary base time `t₀`, using `(f t₀).proj = α` as
the alignment hypothesis. The proofs are identical to the `t₀ = 0` case,
because every intermediate identity is itself base-time-free up to the
projection-equality hypothesis. -/

/-- When `(f t₀).proj = α`, the achart of `TM` at `f t₀` equals the
achart at `⟨α, 0⟩`. -/
lemma achart_modelProd_ft₀_eq
    {f : ℝ → TangentBundle I M} {α : M} {t₀ : ℝ}
    (hft₀_proj : (f t₀).proj = α) :
    achart (ModelProd H E) (f t₀) =
      achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M) := by
  apply achart_modelProd_eq_of_proj_eq (I := I)
  exact hft₀_proj

/-- When `(f t₀).proj = α`, `tangentCoordChange I.tangent q (f t₀) q`
coincides with `tangentCoordChange I.tangent q ⟨α, 0⟩ q`. -/
lemma tangentCoordChange_tangent_ft₀_eq
    {f : ℝ → TangentBundle I M} {α : M} {t₀ : ℝ}
    (hft₀_proj : (f t₀).proj = α) (q : TangentBundle I M) :
    tangentCoordChange I.tangent q (f t₀) q =
      tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q := by
  change (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q) (achart (ModelProd H E) (f t₀)) q =
    (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q)
      (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q
  rw [achart_modelProd_ft₀_eq (I := I) (f := f) (α := α) (t₀ := t₀) hft₀_proj]

/-- **`chartPushVF` in terms of `geodesicVectorFieldChartFiber`, general
base time.** When `(f t₀).proj = α` and `(f s).proj ∈ (chartAt H α).source`,
`chartPushVF g α f t₀ s = geodesicVectorFieldChartFiber g α (f s)`. -/
theorem chartPushVF_eq_geodesicVectorFieldChartFiber_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f t₀ s =
      geodesicVectorFieldChartFiber (I := I) g α (f s) := by
  unfold chartPushVF
  rw [tangentCoordChange_tangent_ft₀_eq (I := I) (t₀ := t₀) hft₀_proj (f s)]
  exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f s) hs

/-- The chart-α fibre form of the geodesic vector field at `f s` matches
the chart-phase vector field evaluated at the chart-pushed lift's
current position, at a general base time `t₀`. -/
theorem geodesicVectorFieldChartFiber_eq_chartPhaseVF_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α (f s) =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f t₀ s) := by
  classical
  have hpair : chartPushLift (I := I) f t₀ s =
      (extChartAt I α (f s).proj, chartFiberCoord (I := I) α (f s)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := t₀) (t := s) ?_
    · rw [h_eq]
      rw [hft₀_proj]
    · rw [hft₀_proj]; exact hs
  rw [hpair]
  rfl

/-- **Headline identification, general base time.** When
`(f t₀).proj = α` and `(f s).proj ∈ (chartAt H α).source`, the
chart-pushed vector field `chartPushVF g α f t₀ s` agrees with the
chart-phase vector field evaluated at the chart-pushed lift's current
position. This is the autonomous generalisation of
`chartPushVF_eq_chartPhaseVF` to an arbitrary base time. -/
theorem chartPushVF_eq_chartPhaseVF_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f t₀ s =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f t₀ s) := by
  rw [chartPushVF_eq_geodesicVectorFieldChartFiber_at (I := I) g α
        hft₀_proj s hs]
  exact geodesicVectorFieldChartFiber_eq_chartPhaseVF_at (I := I) g α
    hft₀_proj s hs

end ChartPushVFEq

/-! ## Eventual chart-phase form of the chart-pushed derivative

The Mathlib chart-pushed derivative formula gives the derivative in
`chartPushVF` form; the identification `chartPushVF_eq_chartPhaseVF`
upgrades it to the `chartPhaseVF` form, eventually around `0`. -/

section EventualChartPhase

variable [I.Boundaryless]

/-- **Chart-phase derivative of the chart-pushed lift.** When the lift
`f` has `(f 0).proj = α` and `f` is a local integral curve of the
chart-fixed geodesic vector field at `0`, on a neighbourhood of `0` the
chart-pushed lift admits the chart-phase `HasDerivAt`-formula
`HasDerivAt (chartPushLift f 0) (chartPhaseVF g α (chartPushLift f 0 t)) t`. -/
theorem chartPushLift_eventually_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M}
    (hf0_proj : (f 0).proj = α)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t)) t := by
  -- The Mathlib-derived formula `HasDerivAt ... (chartPushVF ...) t`.
  have hd := chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α)
    (t₀ := 0) (f := f) hf
  -- Eventually `(f t).proj ∈ (chartAt H α).source`.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f 0 := hf.continuousAt
  have hcomp0 : ContinuousAt (fun t => (f t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hf0_α : (f 0).proj = α := hf0_proj
  have hα_nhds : (chartAt H α).source ∈ 𝓝 α := hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hf0_α]
    exact hα_nhds
  filter_upwards [hd, hsrc_nhds] with t htD ht_src
  -- Use `chartPushVF_eq_chartPhaseVF`.
  have hreplace : chartPushVF (I := I) g α f 0 t =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) :=
    chartPushVF_eq_chartPhaseVF (I := I) g α hf0_proj t ht_src
  rw [hreplace] at htD
  exact htD

/-- **Chart-phase derivative + chart-target-interior condition.** Same
as above, additionally ensuring the chart-pushed lift's position is in
`interior (extChartAt I α).target ×ˢ univ` (a defining condition for the
chart-phase ODE's smoothness). Under `[I.Boundaryless]`, this is
automatic for `(f t).proj` near `α`. -/
theorem chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M}
    (hf0_proj : (f 0).proj = α)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t)) t ∧
      chartPushLift (I := I) f 0 t ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
  -- Eventually `(f t).proj ∈ (chartAt H α).source`.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f 0 := hf.continuousAt
  have hcomp0 : ContinuousAt (fun t => (f t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hf0_α : (f 0).proj = α := hf0_proj
  have hα_nhds : (chartAt H α).source ∈ 𝓝 α := hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hf0_α]
    exact hα_nhds
  -- The chart-phase derivative formula.
  have hd_phase :=
    chartPushLift_eventually_hasDerivAt_chartPhaseVF (I := I) (g := g) (α := α)
      (f := f) hf0_proj hf
  filter_upwards [hd_phase, hsrc_nhds] with t htD ht_src
  refine ⟨htD, ?_⟩
  -- Compute `chartPushLift f 0 t = (extChartAt I α (f t).proj, ...)` and
  -- use boundarylessness to get the first component in the chart-target interior.
  have hpair : chartPushLift (I := I) f 0 t =
      (extChartAt I α (f t).proj, chartFiberCoord (I := I) α (f t)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := 0) (t := t) ?_
    · rw [h_eq]; rw [hf0_α]
    · rw [hf0_α]; exact ht_src
  rw [hpair]
  refine ⟨?_, Set.mem_univ _⟩
  -- `extChartAt I α (f t).proj ∈ interior (extChartAt I α).target` via boundarylessness.
  have h_target : extChartAt I α (f t).proj ∈ (extChartAt I α).target := by
    have h_src : (f t).proj ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact ht_src
    exact (extChartAt I α).map_source h_src
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target

end EventualChartPhase

/-! ## Unconditional closure of the bridge headline

We discharge the chart-phase-ODE hypothesis in the bridge headline
unconditionally, yielding closed-form statements against
`maximalGeodesicChosenCurve`. -/

section UnconditionalBridge

variable [I.Boundaryless] [CompleteSpace E]

/-- **Unconditional bridge against a witness curve.** Given a manifold
curve `γ : ℝ → M` admitting a lift `f` with `f 0 = ⟨p, v_chart⟩` and `f`
a local integral curve of `geodesicVectorFieldChart g p` at `0`, there
exists a chart-pushed flow `Φ` such that on a neighbourhood of `0` the
chart-pushed flow's projection agrees with `γ`. -/
theorem chartPushedFlow_eq_witness_curve_eventually_unconditional
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf0 : f 0 = (⟨p, v_chart⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        γ t = chartFlowGeodesicCurve (I := I) Φ p v_chart t) := by
  -- Build the chart-phase ODE hypothesis from
  -- `chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior`,
  -- using `(f 0).proj = p`.
  have hf0_proj : (f 0).proj = p := by rw [hf0]
  have hd := chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    (I := I) (g := g) (α := p) (f := f) hf0_proj hf_int_at0
  -- Now invoke the conditional bridge.
  exact chartPushedFlow_eq_witness_curve_eventually
    (I := I) (g := g) (p := p) (v_chart := v_chart)
    (γ := γ) (f := f) hproj hf0 hf_int_at0 hd

/-- **Unconditional bridge against `maximalGeodesicChosenCurve`.** Given
a maximal-geodesic witness at some `t₁`, and a lift `f` that
(a) projects to the chosen-witness curve, (b) starts at `⟨p, v⟩`, and
(c) is a local integral curve of `geodesicVectorFieldChart g p` at `0`,
there exists a chart-pushed flow `Φ` such that on a neighbourhood of
`0` the chart-pushed flow's projection equals the chosen-witness curve.

This is the **unconditional closure** of the chart-pushed-flow ↔
maximal-geodesic bridge: the chart-phase-ODE hypothesis on the
chart-pushed lift is discharged via `chartPushVF_eq_chartPhaseVF`. -/
theorem chartPushedFlow_eq_maximalGeodesicChosenCurve_eventually_unconditional
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t₁ : ℝ} (ht₁ : t₁ ∈ maximalGeodesicInterval (I := I) g p v)
    {f : ℝ → TangentBundle I M}
    (hproj_chosen : ∀ t, (f t).proj =
      maximalGeodesicChosenCurve (I := I) g p v ht₁ t)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, (v : E)) : E × E), 0) =
        (extChartAt I p p, (v : E)) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        maximalGeodesicChosenCurve (I := I) g p v ht₁ t =
          chartFlowGeodesicCurve (I := I) Φ p (v : E) t) :=
  chartPushedFlow_eq_witness_curve_eventually_unconditional
    (I := I) (g := g) (p := p) (v_chart := (v : E))
    (γ := maximalGeodesicChosenCurve (I := I) g p v ht₁)
    (f := f) hproj_chosen hf0 hf_int_at0

end UnconditionalBridge

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
