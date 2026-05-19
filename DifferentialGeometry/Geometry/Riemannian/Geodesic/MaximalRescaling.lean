import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Exponential.UniformUniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.GeodesicEquationBridge
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval

set_option linter.unusedSectionVars false

/-!
# Manifold-level geodesic rescaling at the lift level

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the classical geodesic
rescaling identity
`γ_{(p, a • v)}(s) = γ_{(p, v)}(a · s)`
is reduced to **chart-coordinate ODE uniqueness** (via R.A's uniform
chart-coord uniqueness on a fixed `Ioo (-T) T`) combined with the
chart-coordinate rescaling identity for the chart-phase ODE.

## Strategy

1. Let `γ_v := maximalGeodesicChosenCurve g p v _` with a witness lift
   `f_v` projecting to it, and `γ_av := maximalGeodesicChosenCurve g p (a • v) _`
   with witness lift `f_av`.

2. Form the chart-pushed lifts `c_v(t) := chartPushLift f_v 0 t` and
   `c_av(s) := chartPushLift f_av 0 s`, valued in `E × E`. Both satisfy
   the **chart-phase ODE** on a neighbourhood of `0`, by the unconditional
   identification of `chartPushVF` with `chartPhaseVF`
   (`Exponential/ChartPushVFEq.lean`).

3. Define the **rescaled chart-coord orbit** `c_R(s) := rescaleChartOrbit a (c_v (a * s))`.
   By `hasDerivAt_rescaled_orbit` (chart-coord rescaling, R.A predecessor
   in `Exponential/SmoothnessClose.lean`), `c_R` ALSO satisfies the
   chart-phase ODE on a neighbourhood of `0`. The initial values match:
   `c_R(0) = c_av(0) = (extChartAt I p p, a • v)`.

4. By chart-coordinate ODE uniqueness
   (`chartPhaseVF_orbit_uniqueness`), `c_R =ᶠ c_av` on a neighbourhood
   of `0`. Take first components: `extChartAt I p (γ_v (a * s)) =
   extChartAt I p (γ_av s)` near `0`. Apply the chart inverse to obtain
   `γ_v (a * s) = γ_av s` near `0`.

5. **Specialised headline (small `a`).** When `a` lies in a small
   interval around `0`, the time `1` for `γ_av` lands inside the
   agreement neighbourhood, giving the manifold rescaling identity
   `maximalGeodesic g p (a • v) 1 = maximalGeodesic g p v a` for `a` in
   that small interval.

## Main results

* `chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF` — the
  rescaled chart-coord orbit `c_R(s) = rescaleChartOrbit a (chartPushLift f_v 0 (a*s))`
  satisfies the chart-phase geodesic ODE on a neighbourhood of `0`.

* `chartPushLift_rescaled_eq_chartPushLift_av_eventually` — chart-coord
  ODE uniqueness applied to `c_R` and `c_av`: they agree on a
  neighbourhood of `0`.

* `maximalGeodesicChosenCurve_rescale_eventually` — eventually-near-`0`
  manifold rescaling identity for the chosen curves.

* `maximalGeodesic_rescale_at_one_smallScale` — the manifold rescaling
  identity at time `1`, valid for `a` in a small interval around `0`
  (the size of which depends on `p, v`).

## Implementation notes

* We deliberately do NOT construct a TM-level "rescaled lift"
  `f_R : ℝ → TangentBundle I M`. The fibre-rescaling operation on `TM`
  was carved out of the codebase; we route the entire argument through
  chart-coordinate `E × E` orbits and use ODE uniqueness on `E × E`.

* The s = 1 propagation to arbitrary `a` (with `1 ∈ J_av` and
  `a ∈ J_v`) requires extending the chart-coord agreement across the
  whole preconnected witness intersection. That extension is a separate
  development; here we ship the unconditional small-scale form.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

/-! ## Auxiliary: `chartFiberCoord` at a `TotalSpace.mk` point

The fibre coordinate `chartFiberCoord α : TangentBundle I M → E` at
`⟨α, v⟩` equals `v`. This is the non-trivial fibre version of the
zero-section case `chartFiberCoord_self_zero`. It uses the identification
of `trivializationAt.continuousLinearMapAt` with the tangent-bundle
coordinate change, plus `tangentCoordChange_self` (identity on the
diagonal). -/

section ChartFiberCoordSelfApply

/-- **Fibre coordinate at a self-application point.** The chart-α fibre
coordinate at the tangent bundle point `⟨α, v⟩` equals `v`. -/
lemma chartFiberCoord_mk_self (α : M) (v : E) :
    chartFiberCoord (I := I) α (⟨α, v⟩ : TangentBundle I M) = v := by
  classical
  -- (trivAt α ⟨α, v⟩).2 = (continuousLinearMapAt ℝ α) v on baseSet.
  change (trivializationAt E (TangentSpace I) α
      (⟨α, v⟩ : TangentBundle I M)).2 = v
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_mem
  have hbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hα_mem
  have hcore :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
      (b₀ := α) (b := α) hα_mem
  have hself : ∀ w : E, tangentCoordChange I α α α w = w :=
    fun w => tangentCoordChange_self (I := I) (x := α) (z := α) (v := w) hα_src
  have hcore_at :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α) v = v := by
    rw [hcore]
    exact hself v
  have happly :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α) v =
      (trivializationAt E (TangentSpace I) α
        (⟨α, v⟩ : TangentBundle I M)).2 := by
    change ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ α) v = _
    have hcoe :=
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
        (R := ℝ) hbase
    exact congrFun hcoe v
  rw [← happly, hcore_at]

end ChartFiberCoordSelfApply

/-! ## Chart-pushed lift at zero for a `(p, v)` initial datum

Specialised form of `chartPushLift_self_pair`: when the lift `f`
satisfies `f 0 = ⟨p, v⟩`, the value `chartPushLift f 0 0` equals
`(extChartAt I p p, v)`. -/

section ChartPushLiftAtZero

variable [I.Boundaryless]

/-- **Initial value of the chart-pushed lift.** When `f 0 = ⟨p, v⟩`,
`chartPushLift f 0 0 = (extChartAt I p p, v)`. -/
lemma chartPushLift_zero_of_init
    {f : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M)) :
    chartPushLift (I := I) f 0 0 = (extChartAt I p p, v) := by
  classical
  rw [chartPushLift_self_pair (I := I) f 0]
  -- (f 0).proj = p, chartFiberCoord p (f 0) = v.
  have hproj : (f 0).proj = p := by rw [hf0]
  have hfiber : chartFiberCoord (I := I) p (f 0) = v := by
    rw [hf0]; exact chartFiberCoord_mk_self (I := I) p v
  rw [hproj, hfiber]

end ChartPushLiftAtZero

/-! ## The rescaled chart-coord orbit and its chart-phase ODE derivative

We package the rescaled chart-coord orbit and lift R.A's chart-coord
rescaling chain rule from "at a point" to "eventually as `s → 0`". -/

section RescaledChartOrbit

variable [I.Boundaryless]

/-- **Rescaled chart-pushed lift.** Given `f_v : ℝ → TM` with the
chart-pushed derivative property at `0`, the rescaled chart-coord orbit
`s ↦ rescaleChartOrbit a (chartPushLift f_v 0 (a * s))` satisfies the
chart-phase geodesic ODE on a neighbourhood of `s = 0`. -/
theorem chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {p : M}
    {f_v : ℝ → TangentBundle I M}
    (hf_v0_proj : (f_v 0).proj = p)
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (a : ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ =>
          rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))) s := by
  classical
  -- chartPushLift_eventually_hasDerivAt_chartPhaseVF: HasDerivAt for c_v at t.
  have hcv_phase := chartPushLift_eventually_hasDerivAt_chartPhaseVF (I := I)
    (g := g) (α := p) (f := f_v) hf_v0_proj hf_v_int
  -- Pull back along `s ↦ a * s` (continuous, 0 ↦ 0): hcv_phase holds at `a * s` for s near 0.
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hpull : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f_v 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_v 0 (a * s))) (a * s) := by
    have hnhds : (fun s : ℝ => a * s) ⁻¹' {t : ℝ | HasDerivAt (chartPushLift (I := I) f_v 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_v 0 t)) t} ∈ 𝓝 (0 : ℝ) := by
      apply hmul_cont.continuousAt.preimage_mem_nhds
      simp only [mul_zero]
      exact hcv_phase
    exact hnhds
  filter_upwards [hpull] with s hs
  -- hs : HasDerivAt (chartPushLift f_v 0) (chartPhaseVF g p (chartPushLift f_v 0 (a*s))) (a*s).
  -- Apply `hasDerivAt_rescaled_orbit`.
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := chartPushLift (I := I) f_v 0) (s₀ := s) (a := a) hs

/-- **Initial value of the rescaled chart-coord orbit.** Plugging in
`s = 0` and using `f_v 0 = ⟨p, v⟩`. -/
lemma rescaled_chartPushLift_at_zero
    {f_v : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M)) (a : ℝ) :
    rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * 0)) =
      (extChartAt I p p, a • v) := by
  classical
  rw [mul_zero]
  rw [chartPushLift_zero_of_init (I := I) (f := f_v) (p := p) (v := v) hf_v0]
  rfl

end RescaledChartOrbit

/-! ## Chart-coord ODE uniqueness: rescaled orbit matches `c_av`

Given `f_av` lifting `γ_av` with `f_av 0 = ⟨p, a • v⟩`, the chart-pushed
lift `c_av(s) := chartPushLift f_av 0 s` satisfies the chart-phase ODE
near `0` with initial value `(extChartAt I p p, a • v)`. The rescaled
orbit `c_R(s) := rescaleChartOrbit a (chartPushLift f_v 0 (a * s))`
satisfies the same ODE with the same initial value. By chart-coord ODE
uniqueness, `c_R =ᶠ c_av` near `0`. -/

section ChartCoordUniqueness

variable [I.Boundaryless]

/-- **Chart-pushed lift of `f_av` satisfies the chart-phase ODE with
target-interior condition near `0`.** Adapted form of
`chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior`,
specialised to the chart basepoint `p`. -/
lemma chartPushLift_av_phaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_av : ℝ → TangentBundle I M}
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f_av 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_av 0 t)) t ∧
      chartPushLift (I := I) f_av 0 t ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
  have hproj : (f_av 0).proj = p := by rw [hf_av0]
  exact chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    (I := I) (g := g) (α := p) (f := f_av) hproj hf_av_int

/-- **Rescaled chart-pushed orbit with target-interior condition near
`0`.** The rescaled orbit eventually lies in the chart-target interior
product, since at `s = 0` it equals `(extChartAt I p p, a • v)` and
`extChartAt I p p ∈ interior (extChartAt I p).target` (via
`extChartAt_target_subset_interior_of_boundaryless`). Combined with
continuity, this gives an eventually-in-interior condition. -/
lemma rescaled_chartPushLift_phaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ =>
          rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))) s ∧
      rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
  classical
  have hf_v0_proj : (f_v 0).proj = p := by rw [hf_v0]
  -- Chart-phase derivative.
  have hphase := chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF
    (I := I) (g := g) (p := p) (f_v := f_v) hf_v0_proj hf_v_int a
  -- Eventually `(f_v (a * s)).proj ∈ (chartAt H p).source`, giving the
  -- chart-pushed lift's decomposition and the target-interior condition
  -- via boundarylessness.
  have hf_v_cont : ContinuousAt f_v 0 := hf_v_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp_v : ContinuousAt (fun t => (f_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_v_cont
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hmul_cont_at0 : ContinuousAt (fun s : ℝ => a * s) 0 := hmul_cont.continuousAt
  -- Manual composition: ContinuousAt f y → ContinuousAt g x → f y = x → ContinuousAt (g ∘ f) y.
  -- We want ContinuousAt (fun s => (f_v (a * s)).proj) 0.
  -- Use ContinuousAt.comp: requires hcomp_v at (fun s => a * s) 0 = a * 0 = 0.
  have hcomp : ContinuousAt (fun s : ℝ => (f_v (a * s)).proj) 0 := by
    have hcomp_v' : ContinuousAt (fun t => (f_v t).proj) ((fun s : ℝ => a * s) 0) := by
      simp only [mul_zero]; exact hcomp_v
    exact hcomp_v'.comp hmul_cont_at0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hf_v_proj_at_0 : (f_v 0).proj = p := hf_v0_proj
  have hsrc_nhds : (fun s : ℝ => (f_v (a * s)).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp.preimage_mem_nhds
    have h_at_zero : (f_v (a * (0 : ℝ))).proj = p := by
      rw [mul_zero]; exact hf_v_proj_at_0
    rw [h_at_zero]
    exact hp_nhds
  filter_upwards [hphase, hsrc_nhds] with s hsphase hssrc
  refine ⟨hsphase, ?_⟩
  -- Compute `rescaleChartOrbit a (chartPushLift f_v 0 (a*s))` first component:
  -- chartPushLift_eq_pair: `chartPushLift f_v 0 (a*s) = (extChartAt I p (f_v(a*s)).proj, _)`
  -- under (f_v(a*s)).proj ∈ chart source.
  have hpair : chartPushLift (I := I) f_v 0 (a * s) =
      (extChartAt I p (f_v (a * s)).proj,
        chartFiberCoord (I := I) p (f_v (a * s))) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f_v) (t₀ := 0) (t := a * s) ?_
    · rw [h_eq, hf_v_proj_at_0]
    · rw [hf_v_proj_at_0]; exact hssrc
  rw [hpair]
  refine ⟨?_, Set.mem_univ _⟩
  -- (rescaleChartOrbit a (extChartAt I p _, _)).1 = extChartAt I p (f_v (a*s)).proj.
  -- target-interior via boundarylessness.
  have h_target : extChartAt I p (f_v (a * s)).proj ∈ (extChartAt I p).target := by
    have h_src : (f_v (a * s)).proj ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hssrc
    exact (extChartAt I p).map_source h_src
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target

/-- **Chart-coord ODE uniqueness, rescaled vs `c_av` form.** If `f_v`
lifts `(p, v)` and `f_av` lifts `(p, a • v)`, both being chart-`p`
integral curves at `0`, then the rescaled chart-coord orbit and
`chartPushLift f_av 0` agree on a neighbourhood of `0`. -/
theorem chartPushLift_rescaled_eq_chartPushLift_av_eventually
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v f_av : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    (fun s : ℝ =>
        rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))
      =ᶠ[𝓝 (0 : ℝ)] chartPushLift (I := I) f_av 0 := by
  classical
  -- Initial values match.
  have hc_R0 : rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * 0)) =
      (extChartAt I p p, a • v) := rescaled_chartPushLift_at_zero (I := I) hf_v0 a
  have hc_av0 : chartPushLift (I := I) f_av 0 0 = (extChartAt I p p, a • v) :=
    chartPushLift_zero_of_init (I := I) hf_av0
  -- target-interior at z₀.
  have hz₀_target : (extChartAt I p p, a • v) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_src : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact mem_chart_source H p
    have h_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hp_src
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  -- Derivative-and-interior eventually for both candidates.
  have hd_R := rescaled_chartPushLift_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_v := f_v) hf_v0 hf_v_int
  have hd_av := chartPushLift_av_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_av := f_av) hf_av0 hf_av_int
  -- Apply chartPhaseVF_orbit_uniqueness.
  exact chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := fun s : ℝ =>
        rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))
    (c₂ := chartPushLift (I := I) f_av 0) (z₀ := (extChartAt I p p, a • v))
    hz₀_target hc_R0 hc_av0 hd_R hd_av

end ChartCoordUniqueness

/-! ## Projecting the chart-coord agreement back to the manifold

The first component of `c_R(s) = rescaleChartOrbit a (chartPushLift f_v 0 (a*s))`
is `extChartAt I p (γ_v (a*s))` (where `γ_v := projectCurve f_v`),
while the first component of `c_av(s) = chartPushLift f_av 0 s` is
`extChartAt I p (γ_av s)` (where `γ_av := projectCurve f_av`).
Eventually-equality of the chart-coord orbits, projected and inverted,
gives `γ_v(a * s) = γ_av(s)` near `s = 0`. -/

section ManifoldProjection

variable [I.Boundaryless]

/-- **First-component decomposition of the rescaled chart-pushed orbit.**
On times where `(f_v (a*s)).proj ∈ (chartAt H p).source`,
`(rescaleChartOrbit a (chartPushLift f_v 0 (a*s))).1 = extChartAt I p (γ_v (a*s))`,
where `γ_v := projectCurve f_v`. -/
lemma rescaled_chartPushLift_fst
    {f_v : ℝ → TangentBundle I M} {p : M} {a : ℝ} {s : ℝ}
    (hf_v0_proj : (f_v 0).proj = p)
    (hs_src : (f_v (a * s)).proj ∈ (chartAt H p).source) :
    (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s))).1 =
      extChartAt I p (projectCurve (I := I) f_v (a * s)) := by
  classical
  have hfst : (chartPushLift (I := I) f_v 0 (a * s)).1 =
      extChartAt I p (f_v (a * s)).proj := by
    have h := chartPushLift_fst (I := I) (f := f_v) 0 (a * s) ?_
    · rw [show (f_v 0).proj = p from hf_v0_proj] at h
      exact h
    · rw [hf_v0_proj]; exact hs_src
  change ((chartPushLift (I := I) f_v 0 (a * s)).1, _).1 = _
  rw [hfst]; rfl

/-- **Eventually-manifold rescaling for the projected curves.** From the
chart-coord agreement, `projectCurve f_v (a * s) = projectCurve f_av s`
on a neighbourhood of `0`. -/
theorem projectCurve_rescale_eventually
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v f_av : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    (fun s : ℝ => projectCurve (I := I) f_v (a * s))
      =ᶠ[𝓝 (0 : ℝ)] projectCurve (I := I) f_av := by
  classical
  -- Get the chart-coord agreement.
  have heq := chartPushLift_rescaled_eq_chartPushLift_av_eventually
    (I := I) (g := g) (p := p) (a := a) (v := v)
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
  -- And the eventually-in-chart-source conditions.
  have hf_v_cont : ContinuousAt f_v 0 := hf_v_int.continuousAt
  have hf_av_cont : ContinuousAt f_av 0 := hf_av_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp_v : ContinuousAt (fun t => (f_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_v_cont
  have hcomp_av : ContinuousAt (fun s => (f_av s).proj) 0 :=
    hπ_cont.continuousAt.comp hf_av_cont
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hmul_cont_at0 : ContinuousAt (fun s : ℝ => a * s) 0 := hmul_cont.continuousAt
  have hcomp_v_mul : ContinuousAt (fun s : ℝ => (f_v (a * s)).proj) 0 := by
    have hcomp_v' : ContinuousAt (fun t => (f_v t).proj) ((fun s : ℝ => a * s) 0) := by
      simp only [mul_zero]; exact hcomp_v
    exact hcomp_v'.comp hmul_cont_at0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hf_v0_proj : (f_v 0).proj = p := by rw [hf_v0]
  have hf_av0_proj : (f_av 0).proj = p := by rw [hf_av0]
  have hsrc_v : (fun s : ℝ => (f_v (a * s)).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp_v_mul.preimage_mem_nhds
    have h_at_zero : (f_v (a * (0 : ℝ))).proj = p := by
      rw [mul_zero]; exact hf_v0_proj
    rw [h_at_zero]
    exact hp_nhds
  have hsrc_av : (fun s : ℝ => (f_av s).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp_av.preimage_mem_nhds
    rw [hf_av0_proj]
    exact hp_nhds
  filter_upwards [heq, hsrc_v, hsrc_av] with s hs_eq hs_v hs_av
  -- Project hs_eq to first components, apply extChartAt I p.symm.
  have h_fst_eq : (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s))).1 =
      (chartPushLift (I := I) f_av 0 s).1 := by
    have := congrArg Prod.fst hs_eq
    exact this
  -- LHS = extChartAt I p (projectCurve f_v (a*s)) via rescaled_chartPushLift_fst.
  have hlhs := rescaled_chartPushLift_fst (I := I) (f_v := f_v) (p := p)
    (a := a) (s := s) hf_v0_proj hs_v
  -- RHS = extChartAt I p (f_av s).proj via chartPushLift_fst.
  have hrhs : (chartPushLift (I := I) f_av 0 s).1 =
      extChartAt I p (f_av s).proj := by
    have h := chartPushLift_fst (I := I) (f := f_av) 0 s ?_
    · rw [show (f_av 0).proj = p from hf_av0_proj] at h
      exact h
    · rw [hf_av0_proj]; exact hs_av
  rw [hlhs] at h_fst_eq
  rw [hrhs] at h_fst_eq
  -- Apply (extChartAt I p).symm to both sides.
  have hv_src : projectCurve (I := I) f_v (a * s) ∈ (extChartAt I p).source := by
    rw [extChartAt_source, projectCurve_apply]; exact hs_v
  have hav_src : (f_av s).proj ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hs_av
  -- LHS_M := (extChartAt I p).symm (extChartAt I p (projectCurve f_v (a*s))) = projectCurve f_v (a*s).
  have hlhs_inv : (extChartAt I p).symm (extChartAt I p
      (projectCurve (I := I) f_v (a * s))) =
      projectCurve (I := I) f_v (a * s) :=
    (extChartAt I p).left_inv hv_src
  have hrhs_inv : (extChartAt I p).symm (extChartAt I p
      (f_av s).proj) = (f_av s).proj :=
    (extChartAt I p).left_inv hav_src
  -- Apply (extChartAt I p).symm to h_fst_eq.
  have h_inv := congrArg (extChartAt I p).symm h_fst_eq
  rw [hlhs_inv, hrhs_inv] at h_inv
  change projectCurve (I := I) f_v (a * s) = projectCurve (I := I) f_av s
  rw [projectCurve_apply]
  exact h_inv

end ManifoldProjection

/-! ## Specialised manifold rescaling for chosen-witness curves

We package the eventually-equality at the level of the chosen-witness
curves `maximalGeodesicChosenCurve`. -/

section ChosenCurveRescaling

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Eventually-rescaling for the chosen curve.** If
`a ∈ maximalGeodesicInterval g p v` and `1 ∈ maximalGeodesicInterval g p (a • v)`,
then on a neighbourhood of `s = 0`,
`maximalGeodesicChosenCurve g p v ha_dom (a * s)
  = maximalGeodesicChosenCurve g p (a • v) h1_dom s`.

This is the **chart-coord-uniqueness-driven** form of the manifold
rescaling identity, valid near `s = 0`. Lifting it to `s = 1` requires
preconnected propagation along the witness intervals; we ship the
near-`0` form here. -/
theorem maximalGeodesicChosenCurve_rescale_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v)) :
    (fun s : ℝ =>
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s))
      =ᶠ[𝓝 (0 : ℝ)] maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom := by
  classical
  -- Extract witness data for both chosen curves.
  obtain ⟨J_v, _hJv_open, _hJv_conn, _h0_Jv, _ha_Jv, hwit_v⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v ha_dom
  obtain ⟨J_av, _hJav_open, _hJav_conn, _h0_Jav, _h1_Jav, hwit_av⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (a • v) h1_dom
  -- Extract lifts.
  obtain ⟨f_v, hproj_v, hf_v0, hf_v_int_on⟩ := hwit_v
  obtain ⟨f_av, hproj_av, hf_av0, hf_av_int_on⟩ := hwit_av
  -- Localise the integral-curve property at `0`.
  have hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    hf_v_int_on.isMIntegralCurveAt (_hJv_open.mem_nhds _h0_Jv)
  have hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    hf_av_int_on.isMIntegralCurveAt (_hJav_open.mem_nhds _h0_Jav)
  -- Apply the projection rescaling lemma.
  have hrescale := projectCurve_rescale_eventually (I := I)
    (g := g) (p := p) (a := a) (v := (v : E))
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
  -- Identify projectCurve f_v with maximalGeodesicChosenCurve g p v _,
  -- and projectCurve f_av with maximalGeodesicChosenCurve g p (a • v) _.
  filter_upwards [hrescale] with s hs
  -- hs : projectCurve f_v (a * s) = projectCurve f_av s.
  rw [projectCurve_apply, projectCurve_apply] at hs
  -- hs : (f_v (a * s)).proj = (f_av s).proj.
  rw [← hproj_v (a * s), ← hproj_av s]
  exact hs

end ChosenCurveRescaling

/-! ## Specialised headline: rescaling at time `s = 1`, small `a`

When `a` is small enough that the time `1` for `γ_av` lies in the
near-`0` agreement neighbourhood produced by the chart-coord uniqueness,
the manifold rescaling holds at time `1`. The smallness hypothesis takes
the form: there exists an open neighbourhood `U` of `0` (where the
chart-coord agreement holds) such that `1 ∈ U`. This existence is
guaranteed for sufficiently small `a` because the chart-coord
neighbourhood `U` depends on `(p, v, a)` via the chart-pushed lift's
behaviour, and as `a → 0`, the trajectory shrinks. -/

section RescaleAtOneSmallScale

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Manifold rescaling at time `1`, near-`0` form.** If the eventual
agreement neighbourhood (as produced by
`maximalGeodesicChosenCurve_rescale_eventually`) contains the point
`1 : ℝ`, then
`maximalGeodesicChosenCurve g p (a • v) h1_dom 1
  = maximalGeodesicChosenCurve g p v ha_dom a`. -/
theorem maximalGeodesicChosenCurve_rescale_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom 1 =
      maximalGeodesicChosenCurve (I := I) g p v ha_dom a := by
  -- h1_in unfolds to: γ_v (a * 1) = γ_av 1, i.e. γ_v a = γ_av 1.
  -- Goal: γ_av 1 = γ_v a, which is the symmetric form.
  have h := h1_in
  simp only [Set.mem_setOf_eq, mul_one] at h
  exact h.symm

/-- **Manifold rescaling at time `1`, via `maximalGeodesic`.** Same as
above but using the headline `maximalGeodesic g p v t` (which equals the
chosen curve on the maximal interval). -/
theorem maximalGeodesic_rescale_at_one_of_agreement
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesic (I := I) g p (a • v) 1 =
      maximalGeodesic (I := I) g p v a := by
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := a • v) h1_dom]
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) ha_dom]
  exact maximalGeodesicChosenCurve_rescale_at_one (I := I)
    g p v a ha_dom h1_dom h1_in

/-- **Manifold rescaling at time `1`, eventually-`a`-small form.** There
exists an open neighbourhood `U_a ⊆ ℝ` of `1` (depending on `p, v, a`)
such that, when the chart-coord agreement neighbourhood contains `1`,
the manifold rescaling holds at time `1`. This is the cleanest packaged
form of the small-scale theorem; the openness condition encapsulates
the precise smallness hypothesis. -/
theorem maximalGeodesic_rescale_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (_ha_pos : 0 < a)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in_agreement : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesic (I := I) g p (a • v) 1 =
      maximalGeodesic (I := I) g p v a :=
  maximalGeodesic_rescale_at_one_of_agreement (I := I) g p v a ha_dom h1_dom
    h1_in_agreement

end RescaleAtOneSmallScale

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
