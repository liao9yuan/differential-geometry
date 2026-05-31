import DifferentialGeometry.Geometry.Riemannian.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChainedFlowContinuity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

/-!
# Continuity of the intrinsic exponential map in the initial velocity

For a complete Riemannian manifold the intrinsic exponential map
`expMapIntrinsic g hEnorm p v = intrinsicGeodesic g hEnorm p v 1`
(`Exponential/IntrinsicExp.lean`) follows the *complete* moving-foot geodesic
through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`, this
object is genuinely defined and geodesic across charts, so continuity in `v` is
*true* (the chart-fixed `expMap` continuity, by contrast, can only be stated on
small balls because `maximalGeodesic` reverts to its junk value once the
geodesic leaves the home chart).

This file develops the continuity of `v ↦ expMapIntrinsic g hEnorm p v`.  The
metric-geometry compactness endpoint (e.g. `bonnetMyers_compact`) consumes it as
"`M = expMapIntrinsic g p '' closedBall` is a continuous image of a compact
set".

## Mathematical structure

The geodesic `intrinsicGeodesic g hEnorm p v` depends continuously on the
initial velocity `v` because:

* the geodesic flow is continuous in initial conditions **per chart** — the
  per-chart Picard–Lindelöf phase-flow `Φ` of `SmoothFlow.exists_chartPhase_…`
  is jointly `C¹` (in particular continuous) in `(z, t)`, where `z = (x, w)` is
  the chart-coordinate position/velocity;
* the arc `[0, 1] ∋ t ↦ intrinsicGeodesic g hEnorm p v t` is a **compact** subset
  of `M` (continuous image of `[0, 1]`), so by the Lebesgue-number lemma the
  *time* interval `[0, 1]` is covered by finitely many subintervals each of whose
  arc-image lies in a single chart source;
* on each such subinterval the per-chart continuous-in-`(v, t)` flow applies,
  re-based at the foot point `intrinsicGeodesic g hEnorm p v₀ τ` via the proven
  cross-chart re-basing `Geodesic.bm_c_gc_cross_vf_projection_uniqueness`, and
  the *uniqueness* of the geodesic with prescribed initial data identifies
  `intrinsicGeodesic g hEnorm p v` with the chained flow uniformly in `v` over a
  small ball;
* chaining the finitely many per-chart flows yields the joint continuity of
  `(v, t) ↦ intrinsicGeodesic g hEnorm p v t` on `ball v₀ ρ ×ˢ [0, 1]`, whence
  continuity of `v ↦ … 1` by restriction to the `t = 1` slice.

## What this file establishes unconditionally

* `intrinsicGeodesic_compactArc` — the arc image `… '' Icc 0 1` is compact (from
  the proven `intrinsicGeodesic_continuous`).
* `intrinsicGeodesic_arc_finite_chart_cover` — the *time* interval `[0, 1]` is
  covered by finitely many open subintervals each carrying the arc into a single
  chart source (Lebesgue number lemma + finite subcover).
* `expMapIntrinsic_continuous_of_jointContinuity` — the headline-from-joint
  reduction: given the per-ball joint continuity of the chained flow, the
  intrinsic exponential map is continuous.  This mirrors the chart-fixed
  `bm_c_expMap_continuity_from_jointFlow` but for the genuine complete geodesic.

## Residual (single isolated analytic input)

The remaining input is the *uniform-in-`v`* joint continuity of
`(v, t) ↦ intrinsicGeodesic g hEnorm p v t` on a ball `ball v₀ ρ ×ˢ [0, 1]`
(`intrinsicGeodesic_jointContinuity`).  It is the only `sorry` below and the only
genuinely analytic piece; the headline `expMapIntrinsic_continuous` is then a
one-step corollary.  Its sub-lemma decomposition is recorded in the docstring of
`intrinsicGeodesic_jointContinuity`.
-/

noncomputable section

open Set Filter Topology Metric Bundle Manifold Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-! ## 1. Compactness of the intrinsic geodesic arc

The arc `[0, 1] ∋ t ↦ intrinsicGeodesic g hEnorm p v t` has compact image: it is
the continuous image of the compact unit interval, and the intrinsic geodesic is
*genuinely* continuous on all of `ℝ` (`intrinsicGeodesic_continuous`, proved as a
half-line glue of cross-chart extensions in `IntrinsicExp.lean`). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Compactness of the intrinsic geodesic arc.** The image of the unit time
interval `[0, 1]` under the intrinsic complete geodesic through `p` with launch
velocity `v` is a compact subset of `M`.

This is fully unconditional: `intrinsicGeodesic g hEnorm p v` is continuous on all
of `ℝ` (`intrinsicGeodesic_continuous`), and `[0, 1]` is compact, so the image is
compact (`IsCompact.image_of_continuousOn`). -/
theorem intrinsicGeodesic_compactArc
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    IsCompact (intrinsicGeodesic (I := I) g hEnorm p v '' Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.image_of_continuousOn
    (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

/-! ## 2. Finite chart cover of the time interval

The arc image is compact; the chart sources `(chartAt H q).source` form an open
cover of `M`, hence of the arc.  Pulling back along the *continuous* arc gives an
open cover of the compact time interval `[0, 1] ⊆ ℝ`; the Lebesgue-number lemma
on the metric space `ℝ` produces a uniform mesh `δ > 0` so that every time
subinterval of length `< δ` carries the arc into a single chart source. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finite chart cover of the time interval.** There is a mesh `δ > 0` such that
for every `t ∈ [0, 1]` there is a base point `q : M` with the whole
`δ`-time-neighbourhood `ball t δ` of `t` carrying the arc into the single chart
source `(chartAt H q).source`:
`∀ s ∈ ball t δ, intrinsicGeodesic g hEnorm p v s ∈ (chartAt H q).source`.

Construction: the chart sources `{(chartAt H q).source | q : M}` cover `M`, so
their preimages under the continuous arc cover `[0, 1] ⊆ ℝ`.  The Lebesgue-number
lemma `lebesgue_number_lemma_of_metric` on the compact metric set `[0, 1]` yields
the uniform mesh `δ`. -/
theorem intrinsicGeodesic_arc_lebesgue_mesh
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ q : M,
      ∀ s ∈ Metric.ball t δ,
        intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H q).source := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  -- The open cover of the time interval: preimages of chart sources.
  set c : M → Set ℝ := fun q => γ ⁻¹' (chartAt H q).source with hc_def
  have hc_open : ∀ q : M, IsOpen (c q) := by
    intro q
    exact (chartAt H q).open_source.preimage hγ_cont
  -- The chart sources cover the arc, so their preimages cover `[0, 1]`.
  have hc_cover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ q : M, c q := by
    intro t _ht
    refine Set.mem_iUnion.mpr ⟨γ t, ?_⟩
    -- `γ t ∈ (chartAt H (γ t)).source` is the canonical chart-source membership.
    simp only [hc_def, Set.mem_preimage]
    exact mem_chart_source H (γ t)
  -- Lebesgue-number lemma on the compact metric set `[0, 1] ⊆ ℝ`.
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.Icc (0 : ℝ) 1) (c := c)
      isCompact_Icc hc_open hc_cover
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht
  obtain ⟨q, hq⟩ := hδ t ht
  -- `Metric.ball t δ ⊆ c q = γ ⁻¹' (chartAt H q).source`.
  refine ⟨q, ?_⟩
  intro s hs
  have : s ∈ c q := hq hs
  simpa only [hc_def, Set.mem_preimage] using this

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finite chart cover of the time interval (finite-subcover form).** There is a
mesh `δ > 0`, a finite index set `s : Finset (Set.Icc (0 : ℝ) 1)` of times, and
for each indexed time a base point `q`, such that the open `δ`-balls of the chosen
times cover `[0, 1]` and each such ball carries the arc into one chart source.

This packages `intrinsicGeodesic_arc_lebesgue_mesh` with the compactness of
`[0, 1]` (`IsCompact.elim_finite_subcover`) into the explicit finite partition
data consumed by the chained-flow gluing. -/
theorem intrinsicGeodesic_arc_finite_chart_cover
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ∃ (δ : ℝ) (q : (Set.Icc (0 : ℝ) 1) → M) (s : Finset (Set.Icc (0 : ℝ) 1)),
      0 < δ ∧
      Set.Icc (0 : ℝ) 1 ⊆ ⋃ t ∈ s, Metric.ball (t : ℝ) δ ∧
      ∀ t : Set.Icc (0 : ℝ) 1, ∀ r ∈ Metric.ball (t : ℝ) δ,
        intrinsicGeodesic (I := I) g hEnorm p v r ∈ (chartAt H (q t)).source := by
  classical
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    intrinsicGeodesic_arc_lebesgue_mesh (I := I) g hEnorm p v
  -- Choose, for each time `t ∈ [0, 1]`, a chart base point `q t` whose source
  -- absorbs the whole `δ`-ball of `t` under the arc.
  have hq_choice : ∀ t : Set.Icc (0 : ℝ) 1, ∃ q : M,
      ∀ r ∈ Metric.ball (t : ℝ) δ,
        intrinsicGeodesic (I := I) g hEnorm p v r ∈ (chartAt H q).source := by
    intro t
    obtain ⟨q, hq⟩ := hδ (t : ℝ) t.2
    exact ⟨q, hq⟩
  choose q hq using hq_choice
  -- The `δ`-balls centred at points of `[0, 1]` cover `[0, 1]` (each `t` is in
  -- its own ball), and `[0, 1]` is compact, so a finite subfamily covers it.
  -- Phrase the cover indexed by the subtype `Set.Icc 0 1`.
  set U : (Set.Icc (0 : ℝ) 1) → Set ℝ := fun t => Metric.ball (t : ℝ) δ with hU_def
  have hU_open : ∀ t, IsOpen (U t) := fun t => Metric.isOpen_ball
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ t, U t := by
    intro r hr
    refine Set.mem_iUnion.mpr ⟨⟨r, hr⟩, ?_⟩
    simp only [hU_def]
    exact Metric.mem_ball_self hδ_pos
  obtain ⟨s, hs⟩ :=
    isCompact_Icc.elim_finite_subcover U hU_open hcover
  refine ⟨δ, q, s, hδ_pos, ?_, ?_⟩
  · -- `hs : Icc 0 1 ⊆ ⋃ t ∈ s, U t`; rewrite `U t = ball t δ`.
    intro r hr
    have := hs hr
    simpa only [hU_def] using this
  · intro t r hr
    exact hq t r hr

/-- **Chart-phase ODE uniqueness re-centred at a base time `t`.** The
neighbourhood-of-`0` chart-coordinate ODE uniqueness
`Geodesic.chartPhaseVF_orbit_uniqueness` re-based at an arbitrary base time `t`
by a time-shift `s ↦ s + t`.  Two chart-phase ODE solutions agreeing at `t` and
staying in the chart-target interior product near `t` agree on a neighbourhood
of `t`. -/
private theorem chartPhaseVF_orbit_uniqueness_at
    {g : SmoothRiemannianMetric I M} {α : M}
    {c₁ c₂ : ℝ → E × E} {z₀ : E × E} {t : ℝ}
    (hz₀ : z₀ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (h1 : c₁ t = z₀) (h2 : c₂ t = z₀)
    (hd1 : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s ∧
        c₁ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hd2 : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s ∧
        c₂ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    c₁ =ᶠ[𝓝 t] c₂ := by
  classical
  set d₁ : ℝ → E × E := fun s => c₁ (s + t) with hd₁_def
  set d₂ : ℝ → E × E := fun s => c₂ (s + t) with hd₂_def
  have hshift : Filter.Tendsto (fun s : ℝ => s + t) (𝓝 0) (𝓝 t) := by
    have h := (continuous_add_const t).tendsto (0 : ℝ)
    simpa using h
  have he1 : d₁ 0 = z₀ := by simp [hd₁_def, h1]
  have he2 : d₂ 0 = z₀ := by simp [hd₂_def, h2]
  have hdd1 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt d₁ (chartPhaseVF (I := I) g α (d₁ s)) s ∧
        d₁ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hshift.eventually hd1] with s hs
    obtain ⟨hder, hmem⟩ := hs
    refine ⟨?_, hmem⟩
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := by
      simpa using (hasDerivAt_id s).add_const t
    have hcomp := HasDerivAt.scomp s hder hadd
    simpa [hd₁_def, mul_one] using hcomp
  have hdd2 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt d₂ (chartPhaseVF (I := I) g α (d₂ s)) s ∧
        d₂ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hshift.eventually hd2] with s hs
    obtain ⟨hder, hmem⟩ := hs
    refine ⟨?_, hmem⟩
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := by
      simpa using (hasDerivAt_id s).add_const t
    have hcomp := HasDerivAt.scomp s hder hadd
    simpa [hd₂_def, mul_one] using hcomp
  have hdeq : d₁ =ᶠ[𝓝 (0 : ℝ)] d₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := α) hz₀ he1 he2 hdd1 hdd2
  have hshift2 : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have h := (continuous_add_const (-t)).tendsto t
    simpa [sub_eq_add_neg] using h
  filter_upwards [hshift2.eventually hdeq] with s hs
  simp only [hd₁_def, hd₂_def] at hs
  simpa using hs

/-! ## 2b. Converse lift: from the moving-foot geodesic equation to a
chart-centred integral curve

The intrinsic geodesic exposes its data only through the *moving-foot*
geodesic equation `HasGeodesicEquationAt g γ t` (`intrinsicGeodesic_isGeodesic`).
The per-chart re-based flow machinery, by contrast, consumes a chart-`γ(t)`-
centred *integral curve* on `TM` — the structure produced by
`Geodesic.bm_c_gc_cross_vf_projection_uniqueness` from an `IsGeodesicAt`
witness.

The genuine missing link is therefore the converse direction:
`HasGeodesicEquationAt g γ t → ` (a chart-`γ(t)`-centred integral curve whose
projection agrees with `γ` near `t`).  We build it here by Picard–Lindelöf at
the foot `γ t` with the chart velocity, plus chart-coordinate second-order ODE
uniqueness (reduced to the first-order chart-phase system on `E × E` and
discharged by the proven uniqueness `chartPhaseVF_orbit_uniqueness`). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Converse lift from the moving-foot geodesic equation.**  If `γ` is a
geodesic (`IsGeodesic g γ`, i.e. it satisfies the moving-foot geodesic equation
at every time) and is continuous, then at every time `t` there is a
chart-`γ(t)`-centred local integral curve `f₁` of the chart-fixed geodesic
vector field at `γ t` whose projection agrees with `γ` on a neighbourhood of
`t`.

This is the mirror of `Geodesic.bm_c_gc_cross_vf_projection_uniqueness` but
starting from the *moving-foot* geodesic equation (the structure the intrinsic
geodesic exposes through `intrinsicGeodesic_isGeodesic`) rather than from
`IsGeodesicAt`.  The proof:

* extracts the chart velocity `v := deriv (chartCurve (γ t) γ) t`;
* builds, via `exists_chartCenteredLift_at`, the chart-`γ(t)`-centred integral
  curve `f₁` with `f₁ t = ⟨γ t, v⟩`;
* reduces both the fixed-`γ(t)`-chart curve of `γ` and the chart-pushed lift of
  `f₁` to first-order solutions of the chart-phase ODE `chartPhaseVF g (γ t)` on
  a neighbourhood of `t` (the `γ`-side via the moving-foot → fixed-chart
  conversion `hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity` and its
  eventual first-derivative companion
  `hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt`, applied at every
  nearby time using `IsGeodesic`), matching at `t`, and applies the proven
  chart-phase ODE uniqueness `chartPhaseVF_orbit_uniqueness` to conclude the two
  agree, hence `γ` agrees with `projectCurve f₁` near `t` after applying the
  chart inverse. -/
theorem intrinsicGeodesic_hasGeodesicEquationAt_to_lift
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (hγ_cont : Continuous γ) (t : ℝ) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t).proj = γ t ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t)) t ∧
      γ =ᶠ[𝓝 t] (fun s => (f₁ s).proj) := by
  classical
  -- Fixed chart basepoint `y := γ t`, and chart velocity `v`.
  set y : M := γ t with hy_def
  set v : E := deriv
    (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ) t
    with hv_def
  -- Build the chart-`y`-centred integral curve `f₁` with `f₁ t = ⟨y, v⟩`.
  obtain ⟨f₁, hf₁_init, hf₁⟩ := exists_chartCenteredLift_at (I := I) g y v t
  have hf₁_proj_t : (f₁ t).proj = y := by rw [hf₁_init]
  refine ⟨f₁, by rw [hf₁_proj_t], by rw [hy_def] at hf₁ ⊢; exact hf₁, ?_⟩
  -- Abbreviation: the fixed-`y`-chart curve of `γ`.
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ with hw_def
  -- (A) The `γ`-side chart-phase solution `c₁ s := (w s, deriv w s)`.
  set c₁ : ℝ → E × E := fun s => (w s, deriv w s) with hc₁_def
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hγ_src_ev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H y).source := by
    apply hγ_cont.continuousAt.preimage_mem_nhds
    exact (chartAt H y).open_source.mem_nhds (by rw [hy_def]; exact hy_src)
  have hev_first : ∀ᶠ s in 𝓝 t, HasDerivAt w (deriv w s) s :=
    hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g y
      hγ_cont.continuousAt (by rw [hy_def]; exact hy_src) (hγ t)
  have hev_second : ∀ᶠ s in 𝓝 t,
      HasDerivAt (deriv w)
        (- chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) s := by
    filter_upwards [hγ_src_ev] with s hs
    exact hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
      hγ_cont.continuousAt hs (hγ s)
  have hc₁_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₁ (chartPhaseVF (I := I) g y (c₁ s)) s ∧
        c₁ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hev_first, hev_second, hγ_src_ev] with s hf hsd hsrc
    refine ⟨?_, ?_⟩
    · have hpair : HasDerivAt c₁
          ((deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s))) s :=
        hf.prodMk hsd
      have hrhs : chartPhaseVF (I := I) g y (c₁ s) =
          (deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) := by
        simp only [hc₁_def, chartPhaseVF_apply]
      rw [hrhs]; exact hpair
    · refine ⟨?_, Set.mem_univ _⟩
      have hp_ext_src : γ s ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
      have hp_target : extChartAt I y (γ s) ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      have : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
      rw [this]
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  -- (B) The `f₁`-side chart-phase solution `c₂ := chartPushLift f₁ t`.
  set c₂ : ℝ → E × E := chartPushLift (I := I) f₁ t with hc₂_def
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_contAt : ContinuousAt (fun s => (f₁ s).proj) t :=
    hπ_cont.continuousAt.comp hf₁.continuousAt
  have hf_src_ev : ∀ᶠ s in 𝓝 t, (f₁ s).proj ∈ (chartAt H y).source := by
    apply hproj_contAt.preimage_mem_nhds
    rw [hf₁_proj_t]; exact (chartAt H y).open_source.mem_nhds hy_src
  have hc₂_deriv : ∀ᶠ s in 𝓝 t, HasDerivAt (chartPushLift (I := I) f₁ t)
      (chartPushVF (I := I) g y f₁ t s) s := by
    have hf₁' : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g y) t := hf₁
    exact chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := y)
      (t₀ := t) (f := f₁) hf₁'
  have hc₂_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₂ (chartPhaseVF (I := I) g y (c₂ s)) s ∧
        c₂ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hc₂_deriv, hf_src_ev] with s hd hs
    refine ⟨?_, ?_⟩
    · have heq := chartPushVF_eq_chartPhaseVF_at (I := I) g y (f := f₁) (t₀ := t)
        hf₁_proj_t s hs
      rw [heq] at hd; exact hd
    · rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hs)]
      refine ⟨?_, Set.mem_univ _⟩
      rw [hf₁_proj_t]
      have hp_ext_src : (f₁ s).proj ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs
      have hp_target : extChartAt I y (f₁ s).proj ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  -- (C) Match at `t`: both `c₁ t` and `c₂ t` equal `(extChartAt I y y, v)`.
  have hc₁_t : c₁ t = (extChartAt I y y, v) := by
    have hwt : w t = extChartAt I y y := by simp [hw_def, hy_def]
    have hvt : deriv w t = v := by rw [hv_def, hw_def]
    simp only [hc₁_def, hwt, hvt]
  have hc₂_t : c₂ t = (extChartAt I y y, v) := by
    rw [hc₂_def, chartPushLift_self_pair (I := I) f₁ t, hf₁_proj_t]
    have hfib : chartFiberCoord (I := I) y (f₁ t) = v := by
      rw [show f₁ t = (⟨y, v⟩ : TangentBundle I M) from hf₁_init]
      exact chartFiberCoord_mk_self (I := I) y v
    rw [hfib]
  have hz₀_int : (extChartAt I y y, v) ∈
      (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_ext_src : y ∈ (extChartAt I y).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
    have hp_target : extChartAt I y y ∈ (extChartAt I y).target :=
      (extChartAt I y).map_source hp_ext_src
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) y hp_target
  -- (D) Chart-phase ODE uniqueness re-centred at `t`: `c₁ =ᶠ c₂`.
  have hceq : c₁ =ᶠ[𝓝 t] c₂ :=
    chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (α := y)
      hz₀_int hc₁_t hc₂_t hc₁_phase hc₂_phase
  -- (E) Project the first-component equality back to `γ =ᶠ projectCurve f₁`.
  have hfst : ∀ᶠ s in 𝓝 t, extChartAt I y (γ s) = extChartAt I y (f₁ s).proj := by
    filter_upwards [hceq, hf_src_ev] with s hs hsrc
    have h1 : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
    have h2 : (c₂ s).1 = extChartAt I y (f₁ s).proj := by
      rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hsrc)]
      rw [hf₁_proj_t]
    rw [← h1, ← h2, hs]
  filter_upwards [hγ_src_ev, hf_src_ev, hfst] with s hγs hfs heq
  have hγ_es : γ s ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγs
  have hf_es : (f₁ s).proj ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hfs
  exact (extChartAt I y).injOn hγ_es hf_es heq

/-! ## 3. Joint continuity of the chained flow (the analytic residual)

The single remaining analytic input is the *uniform-in-`v`* joint continuity of
`(v, t) ↦ intrinsicGeodesic g hEnorm p v t` on a small ball `ball v₀ ρ ×ˢ [0, 1]`.
This is the genuine cross-chart-chained continuity-in-initial-conditions of the
geodesic flow.

### Sub-lemma decomposition of `intrinsicGeodesic_jointContinuity`

Fix `v₀ : T_p M`.  Set `γ₀ := intrinsicGeodesic g hEnorm p v₀` and let
`δ, q, s` be the finite chart cover of `[0, 1]` from
`intrinsicGeodesic_arc_finite_chart_cover`, with mesh times `t₀ = 0 < t₁ < … <
t_N` and chart base points `α_k := q tₖ` so that `γ₀([tₖ, tₖ₊₁]) ⊆ (chartAt H
α_k).source`.

1.  **Per-chart re-based continuous flow.** On the `k`-th subinterval, re-base the
    chart-phase flow at the foot `γ₀(tₖ)` via the proven cross-chart re-basing
    `Geodesic.bm_c_gc_cross_vf_projection_uniqueness`
    (`Geodesic/CrossVFReduction.lean`, no `sorry`) combined with the per-chart
    joint-`C¹` flow `SmoothFlow.exists_chartPhase_contDiffOn_isLocalFlow_combined`.
    This yields a flow `Φ_k : (E × E) × ℝ → E × E`, jointly continuous in
    `(z, t)`, and a radius `ρ_k > 0` such that for the phase initial condition
    `z_w` (depending continuously on the manifold velocity `w` at `γ₀(tₖ)`) the
    projection `proj(Φ_k(z_w, t - tₖ))` is a geodesic at `γ₀(tₖ)` with launch
    velocity `w`.

    Signature of the sub-lemma:
    ```
    perChartReContinuousFlow :
      IsGeodesicAt g γ₀ tₖ → ∃ (Φ_k) (ρ_k T_k > 0),
        ContinuousOn (fun (zt) => proj (Φ_k zt)) (ball z₀ ρ_k ×ˢ Ioo (-T_k) T_k) ∧
        (∀ z ∈ ball z₀ ρ_k, ∀ τ ∈ Ioo (-T_k) T_k,
          IsMIntegralCurveAt (lift Φ_k z) (geodesicVectorFieldChart g (γ₀ tₖ)) 0)
    ```
    (the chart-flow datum at `γ₀ tₖ` is the converse direction from the
    moving-foot geodesic equation to a chart-`γ₀(tₖ)`-centred integral curve
    matching `γ₀` near `tₖ`, recorded — fully proven and axiom-clean — as
    `intrinsicGeodesic_hasGeodesicEquationAt_to_lift` above, which is the mirror
    of `Geodesic.bm_c_gc_cross_vf_projection_uniqueness` but starting from
    `IsGeodesic` rather than `IsGeodesicAt`).

2.  **Uniqueness identification.** For `v` near `v₀`, the intrinsic geodesic
    `intrinsicGeodesic g hEnorm p v` and the re-based flow projection agree on a
    neighbourhood of each `tₖ`, by geodesic uniqueness with prescribed initial
    data `isGeodesicAt_eventuallyEq_of_lift_eq` (`Geodesic/Uniqueness.lean`, no
    `sorry`).  Continuity of `v ↦ (initial phase datum at γ₀(tₖ))` propagates
    through `Φ_k`'s joint continuity, giving continuity of
    `(v, t) ↦ intrinsicGeodesic g hEnorm p v t` on `ball v₀ ρ_k ×ˢ (tₖ-ε, tₖ+ε)`.

    Signature of the sub-lemma:
    ```
    perChartIntrinsicContinuity :
      ∃ ρ_k T_k > 0, ContinuousOn
        (fun (vt : T_p M × ℝ) => intrinsicGeodesic g hEnorm p vt.1 vt.2)
        (ball v₀ ρ_k ×ˢ Ioo (tₖ - T_k) (tₖ + T_k))
    ```

3.  **Junction gluing.** At each junction `tₖ₊₁` the launch velocity of the
    `k`-th flow equals the initial velocity of the `(k+1)`-th flow (continuity of
    the velocity, the `C¹`-in-time regularity `intrinsicGeodesic_contMDiffOn`),
    so the per-chart windows of step 2 overlap; taking `ρ := min_k ρ_k` and
    pasting the finitely many overlapping `ContinuousOn` pieces (compatible on
    overlaps, finite union, `ContinuousOn.union` / locally-on-an-open-cover
    gluing) yields joint continuity on `ball v₀ ρ ×ˢ [0, 1]`.

The chaining is *uniform in `v`* precisely because the `min_k ρ_k` ball is chosen
after the finite chart cover is fixed (the cover is determined by `γ₀ = γ_{v₀}`,
not by `v`), and the per-chart radii `ρ_k` are positive.  This is the same
uniform-in-`v` cross-junction joint continuity that the chart-fixed
`bm_c_expMap_chainedFlow_joint_continuity` carries as its residual, but here it is
*true* on all of `[0, 1]` (not just on a small ball) because the underlying object
is the genuine complete geodesic. -/

/-! ### Foot-varying per-chart flow projection

The existing `chartFlowOrbitLift` (`Exponential/ChartFlowToTangentLift.lean`) fixes
both the chart centre `α` and the phase basepoint at `(extChartAt I α α, v)`,
i.e. the foot is the chart centre.  For the cross-junction gluing the foot
`intrinsicGeodesic g p v tₖ` *varies* with `v`, so we need a version of the lift
in which the phase initial point `z ∈ E × E` is an explicit parameter (the foot's
chart coordinate paired with its chart velocity coordinate), both continuous in
`v`.  We package the resulting *flow projection* and its joint continuity here.

`flowProj α Φ z s := (extChartAt I α).symm (Φ (z, s)).1` is the base-manifold
projection of the chart-`α`-centred phase flow `Φ` started at the phase point `z`,
evaluated after running for time `s`.  Whenever `(Φ (z, s)).1` stays in the
(open) chart target `(extChartAt I α).target`, this projection is continuous
jointly in `(z, s)` because `Φ` is and `(extChartAt I α).symm` is continuous on
its target. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The base-manifold projection of the chart-`α`-centred phase flow `Φ` started
at phase point `z` and run for time `s`. -/
private def flowProj (α : M) (Φ : (E × E) × ℝ → E × E) (z : E × E) (s : ℝ) : M :=
  (extChartAt I α).symm (Φ (z, s)).1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Joint continuity of the foot-varying flow projection.** Suppose `Φ` is
continuous on the phase-product `ball z₀ ρ ×ˢ Ioo (-T) T`, the phase parameter
map `z : N → E × E` is continuous on the parameter set `s` with values in
`ball z₀ ρ`, and for every `(n, τ)` in `s ×ˢ Ioo (-T) T` the flowed first
component `(Φ (z n, τ)).1` lies in the (open) chart target `(extChartAt I α).target`.
Then `(n, τ) ↦ flowProj α Φ (z n) τ` is continuous on `s ×ˢ Ioo (-T) T`. -/
private theorem flowProj_continuousOn
    [I.Boundaryless]
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ T : ℝ}
    {N : Type*} [TopologicalSpace N] {z : N → E × E} {S : Set N}
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T))
    (hz_cont : ContinuousOn z S)
    (hz_ball : ∀ n ∈ S, z n ∈ Metric.ball z₀ ρ)
    (htgt : ∀ n ∈ S, ∀ τ ∈ Set.Ioo (-T) T,
      (Φ (z n, τ)).1 ∈ (extChartAt I α).target) :
    ContinuousOn (fun nτ : N × ℝ => flowProj (I := I) α Φ (z nτ.1) nτ.2)
      (S ×ˢ Set.Ioo (-T) T) := by
  classical
  -- The phase map `(n, τ) ↦ (z n, τ)` is continuous on `S ×ˢ Ioo (-T) T` and lands
  -- in `ball z₀ ρ ×ˢ Ioo (-T) T`.
  have hpair_cont : ContinuousOn (fun nτ : N × ℝ => (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact hz_cont.comp continuousOn_fst (fun x hx => hx.1)
    · exact continuousOn_snd
  have hpair_maps : Set.MapsTo (fun nτ : N × ℝ => (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T) := by
    intro nτ hnτ
    exact ⟨hz_ball nτ.1 hnτ.1, hnτ.2⟩
  -- `Φ ∘ (phase map)` is continuous on `S ×ˢ Ioo (-T) T`.
  have hΦcomp : ContinuousOn (fun nτ : N × ℝ => Φ (z nτ.1, nτ.2))
      (S ×ˢ Set.Ioo (-T) T) :=
    hΦ.comp hpair_cont hpair_maps
  -- Take the first component, which is continuous.
  have hfst : ContinuousOn (fun nτ : N × ℝ => (Φ (z nτ.1, nτ.2)).1)
      (S ×ˢ Set.Ioo (-T) T) :=
    (continuous_fst.comp_continuousOn hΦcomp)
  -- Compose with `(extChartAt I α).symm`, continuous on `(extChartAt I α).target`.
  have hsymm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (fun nτ : N × ℝ => (Φ (z nτ.1, nτ.2)).1)
      (S ×ˢ Set.Ioo (-T) T) (extChartAt I α).target := by
    intro nτ hnτ
    exact htgt nτ.1 hnτ.1 nτ.2 hnτ.2
  exact hsymm.comp hfst hmaps

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Per-chart foot-varying joint continuity, from a flow identification.**
This is the reusable producer of the induction step: on a window
`ball v₀ r ×ˢ Ioo (tₖ - ε) (tₖ + ε)`, suppose the intrinsic geodesic
`(v, t) ↦ intrinsicGeodesic g hEnorm p v t` agrees with the foot-varying flow
projection `flowProj α Φ (z v) (t - tₖ)`, where `Φ` is continuous on the phase
product `ball z₀ ρ ×ˢ Ioo (-T) T`, the phase parameter `z` is continuous in `v`
on `ball v₀ r` with values in `ball z₀ ρ`, and the flowed first component stays in
the chart target.  Then the intrinsic geodesic is jointly continuous on the
window.

The hypothesis `hident` is a genuine geometric *identification* of two a priori
distinct objects (the intrinsic geodesic and the projection of a per-chart phase
flow), supplied by geodesic uniqueness at the foot; it is **not** the continuity
conclusion.  Joint continuity then follows from `flowProj_continuousOn` and a
change of time variable `t ↦ t - tₖ`. -/
private theorem perChart_jointContinuity_of_flowIdentifiedOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {z : TangentSpace I p → E × E}
    {tₖ ε r ρ T : ℝ}
    (hεT : ε ≤ T)
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-T) T))
    (hz_cont : ContinuousOn z (Metric.ball v₀ r))
    (hz_ball : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball z₀ ρ)
    (htgt : ∀ v ∈ Metric.ball v₀ r, ∀ τ ∈ Set.Ioo (-ε) ε,
      (Φ (z v, τ)).1 ∈ (extChartAt I α).target)
    (hident : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - ε) (tₖ + ε),
      intrinsicGeodesic (I := I) g hEnorm p v t =
        flowProj (I := I) α Φ (z v) (t - tₖ)) :
    ContinuousOn
      (fun vt : TangentSpace I p × ℝ =>
        intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  -- The time-shift homeomorphism `t ↦ t - tₖ` maps the window
  -- `Ioo (tₖ - ε) (tₖ + ε)` onto `Ioo (-ε) ε`.
  have hshift_cont : ContinuousOn (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) :=
    (continuousOn_fst).prodMk ((continuousOn_snd).sub continuousOn_const)
  have hshift_maps : Set.MapsTo (fun vt : TangentSpace I p × ℝ => (vt.1, vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (-ε) ε) := by
    intro vt hvt
    refine ⟨hvt.1, ?_, ?_⟩
    · exact lt_sub_iff_add_lt.mpr (by linarith [hvt.2.1])
    · exact sub_lt_iff_lt_add.mpr (by linarith [hvt.2.2])
  -- The flow projection is jointly continuous on `ball v₀ r ×ˢ Ioo (-ε) ε`.
  have hbase_cont : ContinuousOn
      (fun vτ : TangentSpace I p × ℝ => flowProj (I := I) α Φ (z vτ.1) vτ.2)
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (-ε) ε) := by
    have hΦ' : ContinuousOn Φ ((Metric.ball z₀ ρ) ×ˢ Set.Ioo (-ε) ε) :=
      hΦ.mono (Set.prod_mono (le_refl _)
        (Set.Ioo_subset_Ioo (by linarith) hεT))
    exact flowProj_continuousOn (I := I) (α := α) (Φ := Φ) (z₀ := z₀)
      (ρ := ρ) (T := ε) (z := z) (S := Metric.ball v₀ r)
      hΦ' hz_cont hz_ball htgt
  -- Compose: `(v, t) ↦ flowProj α Φ (z v) (t - tₖ)` is continuous on the window.
  have hcomp_cont : ContinuousOn
      (fun vt : TangentSpace I p × ℝ => flowProj (I := I) α Φ (z vt.1) (vt.2 - tₖ))
      ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) :=
    hbase_cont.comp hshift_cont hshift_maps
  -- Rewrite via the identification.
  apply hcomp_cont.congr
  intro vt hvt
  exact hident vt.1 hvt.1 vt.2 hvt.2

/-! ### General uniform confinement of a parameter-varying flow orbit

The per-junction phase point `z v` varies with `v` (both the chart-coordinate of
the *foot* `intrinsicGeodesic g hEnorm p v tₖ` and its chart velocity move with
`v`); only at the base velocity does it sit at the flow's centre `z₀`.  The
following purely-topological lemma extracts, from joint continuity of the flow
`Φ` at the base phase-point–time `(z₀, 0)` together with continuity of the
phase-parameter map `z` at `v₀` (with `z v₀ = z₀`), a *uniform* window
`ball v₀ r' ×ˢ Ioo (-T') T'` on which the orbit `Φ (z v, s)` stays inside any
prescribed neighbourhood `W` of `z₀`.  This is the foot-varying generalisation of
`Exponential.exists_uniform_orbit_in_inner_ball` (which fixes the foot at the
chart centre and varies only the velocity). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Uniform confinement of a parameter-varying flow orbit.** Suppose `Φ` is
continuous on `ball z₀ ρ_f ×ˢ Ioo (-T_f) T_f` with `Φ (z₀, 0) = z₀`, the
phase-parameter map `z : N → E × E` is continuous at `v₀` with `z v₀ = z₀`, and
`W` is a neighbourhood of `z₀`.  Then there are a parameter neighbourhood `S` of
`v₀` with `z '' S ⊆ ball z₀ ρ_f` and a time horizon `T' ∈ (0, T_f)` such that the
orbit `Φ (z v, s)` lies in `W` for all `v ∈ S` and `s ∈ Ioo (-T') T'`. -/
private theorem flowOrbit_uniform_confinement
    {N : Type*} [TopologicalSpace N]
    {Φ : (E × E) × ℝ → E × E} {z₀ : E × E} {ρ_f T_f : ℝ}
    {z : N → E × E} {v₀ : N} {W : Set (E × E)}
    (hρ_f : 0 < ρ_f) (hT_f : 0 < T_f)
    (hΦ : ContinuousOn Φ ((Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f))
    (hΦ0 : Φ (z₀, 0) = z₀)
    (hz_cont : ContinuousAt z v₀) (hz0 : z v₀ = z₀)
    (hW : W ∈ 𝓝 z₀) :
    ∃ (S : Set N) (T' : ℝ), IsOpen S ∧ v₀ ∈ S ∧ 0 < T' ∧ T' < T_f ∧
      (∀ v ∈ S, z v ∈ Metric.ball z₀ ρ_f) ∧
      (∀ v ∈ S, ∀ s ∈ Set.Ioo (-T') T', Φ (z v, s) ∈ W) := by
  classical
  -- The flow domain is open and contains `(z₀, 0)`.
  have h_open : IsOpen ((Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hz₀0_mem : ((z₀, (0 : ℝ)) : (E × E) × ℝ) ∈
      (Metric.ball z₀ ρ_f) ×ˢ Set.Ioo (-T_f) T_f :=
    ⟨Metric.mem_ball_self hρ_f, ⟨by linarith, hT_f⟩⟩
  have hΦ_contAt : ContinuousAt Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) :=
    hΦ.continuousAt (h_open.mem_nhds hz₀0_mem)
  -- The composite `(v, s) ↦ Φ (z v, s)` is continuous at `(v₀, 0)`.
  have hpair_contAt : ContinuousAt (fun ws : N × ℝ => ((z ws.1, ws.2) : (E × E) × ℝ))
      ((v₀, (0 : ℝ)) : N × ℝ) :=
    (hz_cont.comp continuousAt_fst).prodMk continuousAt_snd
  have hΨ_contAt : ContinuousAt (fun ws : N × ℝ => Φ ((z ws.1, ws.2) : (E × E) × ℝ))
      ((v₀, (0 : ℝ)) : N × ℝ) := by
    have hval : ((z v₀, (0 : ℝ)) : (E × E) × ℝ) = ((z₀, (0 : ℝ)) : (E × E) × ℝ) := by
      rw [hz0]
    refine ContinuousAt.comp ?_ hpair_contAt
    rw [hval]; exact hΦ_contAt
  -- `W` and `ball z₀ ρ_f` are neighbourhoods of `z₀ = Φ (z₀, 0)`.
  have hW_nhds : W ∈ 𝓝 (Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ)) := by rw [hΦ0]; exact hW
  have h_orbit_preim : (fun ws : N × ℝ => Φ ((z ws.1, ws.2) : (E × E) × ℝ)) ⁻¹' W ∈
      𝓝 ((v₀, (0 : ℝ)) : N × ℝ) := by
    apply hΨ_contAt.preimage_mem_nhds
    have hval : Φ ((z v₀, (0 : ℝ)) : (E × E) × ℝ) = Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) := by
      rw [hz0]
    rw [hval]; exact hW_nhds
  -- The parameter-side preimage of `ball z₀ ρ_f` under `z` is a neighbourhood of `v₀`.
  have hz_preim : z ⁻¹' (Metric.ball z₀ ρ_f) ∈ 𝓝 v₀ := by
    apply hz_cont.preimage_mem_nhds
    rw [hz0]; exact Metric.ball_mem_nhds _ hρ_f
  -- Extract a product neighbourhood `S₀ ×ˢ V₀ ⊆ orbit-preimage of W`.
  obtain ⟨S₁, V₁, hS₁_open, hS₁_mem, hV₁_open, hV₁_mem, h_sub⟩ :=
    mem_nhds_prod_iff'.mp h_orbit_preim
  -- Intersect the parameter side with the `ball z₀ ρ_f`-preimage neighbourhood.
  obtain ⟨S₂, hS₂_sub, hS₂_open, hv₀_S₂⟩ := _root_.mem_nhds_iff.mp hz_preim
  set S : Set N := S₁ ∩ S₂ with hS_def
  have hS_open : IsOpen S := hS₁_open.inter hS₂_open
  have hv₀_S : v₀ ∈ S := ⟨hS₁_mem, hv₀_S₂⟩
  -- Time side: shrink `V₁` to `Ioo (-T') T'` with `T' < T_f`.
  obtain ⟨T₀, hT₀_pos, hT₀_sub⟩ := Metric.isOpen_iff.mp hV₁_open (0 : ℝ) hV₁_mem
  set T' : ℝ := min T₀ T_f / 2 with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]; have : 0 < min T₀ T_f := lt_min hT₀_pos hT_f; linarith
  have hT'_lt_Tf : T' < T_f := by
    rw [hT'_def]; have h1 : min T₀ T_f ≤ T_f := min_le_right _ _; linarith
  have hT'_lt_T₀ : T' < T₀ := by
    rw [hT'_def]; have h1 : min T₀ T_f ≤ T₀ := min_le_left _ _; linarith
  have hIoo_sub_V₁ : Set.Ioo (-T') T' ⊆ V₁ := by
    intro s hs
    apply hT₀_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨S, T', hS_open, hv₀_S, hT'_pos, hT'_lt_Tf, ?_, ?_⟩
  · intro v hv
    exact hS₂_sub hv.2
  · intro v hv s hs
    have hv_S₁ : v ∈ S₁ := hv.1
    have hs_V₁ : s ∈ V₁ := hIoo_sub_V₁ hs
    have hpair : (v, s) ∈ S₁ ×ˢ V₁ := ⟨hv_S₁, hs_V₁⟩
    exact h_sub hpair

/-! ### Geodesic-side fixed-chart phase ODE on a window

For the uniform identification we need the *geodesic side* expressed in a single
*fixed* chart `α` (the junction chart centre, generally distinct from the moving
foot).  The fixed-chart curve `s ↦ extChartAt I α (γ s)` paired with its
time-derivative satisfies the genuine chart-phase ODE `chartPhaseVF g α` wherever
`γ` stays in the chart-`α` source — this is the fixed-chart reading of the
moving-foot geodesic equation, supplied pointwise by
`Geodesic.hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt` (first-order
differentiability companion) and
`Geodesic.hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity` (second-order
velocity ODE). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Geodesic-side fixed-chart phase curve satisfies `chartPhaseVF` on a
window.** Let `γ` be a geodesic, continuous, whose values on an open set
`U ∋ t` all lie in the chart-`α` source.  Then the fixed-`α`-chart phase curve
`c s := (extChartAt I α (γ s), deriv (extChartAt I α ∘ γ) s)` satisfies the
chart-phase ODE `HasDerivAt c (chartPhaseVF g α (c s)) s` at every `s ∈ U`, and
`(c s).1 ∈ interior (extChartAt I α).target`.

This is the fixed-chart reading of the moving-foot geodesic equation: at each
`s ∈ U`, `γ s` lies in the chart-`α` source, so the moving-foot equation
`hγ.hasGeodesicEquationAt s` transforms (via the chart-transition Christoffel law)
into the fixed-`α`-chart second-order ODE, which combines with the first-order
differentiability companion into the first-order phase system on `E × E`. -/
private theorem geodesic_chartPhaseVF_on_open
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (hγ_cont : Continuous γ)
    {U : Set ℝ} (hU_open : IsOpen U)
    (hγ_src : ∀ s ∈ U, γ s ∈ (chartAt H α).source) :
    ∀ s ∈ U,
      HasDerivAt
        (fun r : ℝ =>
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ r,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ) r) : E × E))
        (chartPhaseVF (I := I) g α
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ s,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve
              (I := I) α γ) s) : E × E)) s ∧
      (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ s)
        ∈ interior (extChartAt I α).target := by
  classical
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
    with hw_def
  intro s hs
  have hsU_nhds : U ∈ 𝓝 s := hU_open.mem_nhds hs
  have hs_src : γ s ∈ (chartAt H α).source := hγ_src s hs
  -- First-order differentiability of the fixed-chart curve near `s`.
  have hev_first : ∀ᶠ r in 𝓝 s, HasDerivAt w (deriv w r) r :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt
      (I := I) g α hγ_cont.continuousAt hs_src (hγ s)
  have hfirst : HasDerivAt w (deriv w s) s := hev_first.self_of_nhds
  -- Second-order velocity ODE at `s`.
  have hsecond : HasDerivAt (deriv w)
      (- chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s)) s :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity
      (I := I) g α hγ_cont.continuousAt hs_src (hγ s)
  refine ⟨?_, ?_⟩
  · -- Combine into the phase ODE.
    have hpair : HasDerivAt
        (fun r : ℝ => (w r, deriv w r))
        ((deriv w s,
          - chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s))) s :=
      hfirst.prodMk hsecond
    have hrhs : chartPhaseVF (I := I) g α (w s, deriv w s) =
        (deriv w s,
          - chartChristoffelContraction (I := I) g α (deriv w s) (deriv w s) (w s)) := by
      simp only [chartPhaseVF_apply]
    rw [hrhs]; exact hpair
  · -- Chart-target interior membership.
    have hp_ext_src : γ s ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs_src
    have hp_target : extChartAt I α (γ s) ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hp_ext_src
    have hval : w s = extChartAt I α (γ s) := by simp [hw_def]
    rw [hval]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hp_target

/-! ### Per-junction uniform geodesic↔flow identification (the residual bootstrap)

The genuine analytic content of the assembly is the *uniform-in-`v`* identification
of the intrinsic geodesic with a foot-varying chart-phase flow projection on a
window `ball v₀ r ×ˢ Ioo (tₖ - T') (tₖ + T')`.  The following producer supplies
that identification from the per-junction data: a chart centre `α`, a jointly-`C¹`
per-chart flow `Φ` (from
`Geodesic.SmoothFlow.exists_chartPhase_contDiffOn_isLocalFlow_combined`), the
continuous-in-`v` phase point `z v` (chart-coordinate of the foot
`intrinsicGeodesic g hEnorm p v tₖ` paired with its chart velocity), uniform
confinement of both the geodesic and the flow orbit to a compact ball inside the
chart-target interior, and the matching of initial phase data at `tₖ`.

`chartPhaseVF_orbit_uniqueness_uniform_Ioo` then identifies the two chart-phase
solutions on the *whole* window (uniqueness on the compact confinement ball over
the entire `Ioo`), and projecting the first-component equality through
`(extChartAt I α).symm` yields the geodesic↔`flowProj` identification `hident`.

The hypotheses are genuine geometric inputs (confinement of the actual geodesic /
flow orbit to a ball, and matching initial data), **not** the continuity
conclusion; in particular the confinement is a true geometric fact about the
specific curves, not a packaging of the joint-continuity goal. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Per-junction uniform geodesic↔flow-projection identification.** On a window
`ball v₀ r ×ˢ Ioo (tₖ - T') (tₖ + T')`, with `Φ` continuous on the phase product
`ball z₀ ρ ×ˢ Ioo (-T) T` and satisfying the chart-phase ODE along each orbit
`Φ (z v, ·)` confined to the compact ball `closedBall z₀ R ⊆ interior target ×ˢ
univ`, the geodesic `intrinsicGeodesic g hEnorm p v` confined in chart `α` to the
same ball, and matching initial phase data `z v = (extChartAt I α (γ_v tₖ),
deriv (chartCurve α γ_v) tₖ)`, the intrinsic geodesic agrees with the foot-varying
flow projection `flowProj α Φ (z v) (t - tₖ)` on the window.

This is the uniform identification feeding `perChart_jointContinuity_of_flowIdentifiedOn`. -/
private theorem perJunction_flowIdentification
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    {α : M} {Φ : (E × E) × ℝ → E × E} {z₀ : E × E}
    {z : TangentSpace I p → E × E}
    {tₖ r R T' : ℝ}
    (hT'_pos : 0 < T')
    (hball : Metric.closedBall z₀ R ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s)
    (hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall z₀ R)
    (hgeo_src : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source)
    (hgeo_in : ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
        ∈ Metric.closedBall z₀ R)
    (hinit : ∀ v ∈ Metric.ball v₀ r,
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)
    (hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v) :
    ∀ v ∈ Metric.ball v₀ r, ∀ t ∈ Set.Ioo (tₖ - T') (tₖ + T'),
      intrinsicGeodesic (I := I) g hEnorm p v t =
        flowProj (I := I) α Φ (z v) (t - tₖ) := by
  classical
  intro v hv t ht
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_geo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
    with hw_def
  -- The geodesic-side phase curve, time-shifted to be centred at `tₖ`.
  set c₁ : ℝ → E × E := fun s => (w (tₖ + s), deriv w (tₖ + s)) with hc₁_def
  -- The flow-side phase curve.
  set c₂ : ℝ → E × E := fun s => Φ (z v, s) with hc₂_def
  -- Open window `U := Ioo (tₖ - T') (tₖ + T')` on which the geodesic is in chart `α`.
  set U : Set ℝ := Set.Ioo (tₖ - T') (tₖ + T') with hU_def
  have hU_open : IsOpen U := isOpen_Ioo
  have hsrc_U : ∀ s ∈ U, γ s ∈ (chartAt H α).source := by
    intro s hsU; exact hgeo_src v hv s hsU
  -- Geodesic-side phase ODE on `U` (in the fixed chart `α`).
  have hgeo_phase := geodesic_chartPhaseVF_on_open (I := I) (g := g) (α := α) (γ := γ)
    hγ_geo hγ_cont hU_open hsrc_U
  -- `c₁` satisfies `chartPhaseVF g α` on `Ioo (-T') T'` (via the time shift `s ↦ tₖ + s`).
  have hc₁_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    obtain ⟨hder, _⟩ := hgeo_phase (tₖ + s) htks
    -- `hder : HasDerivAt (fun r => (w r, deriv w r)) (chartPhaseVF g α (w (tₖ+s), deriv w (tₖ+s))) (tₖ+s)`.
    have hshift : HasDerivAt (fun r : ℝ => tₖ + r) 1 s := by
      simpa using (hasDerivAt_id s).const_add tₖ
    have hcomp := hder.scomp s hshift
    simp only [one_smul] at hcomp
    -- `hcomp : HasDerivAt ((fun r => (w r, deriv w r)) ∘ (fun r => tₖ + r)) (...) s`.
    -- The composition equals `c₁` and the right-hand side equals `chartPhaseVF g α (c₁ s)`.
    have hfun : ((fun r : ℝ => ((w r, deriv w r) : E × E)) ∘ fun r : ℝ => tₖ + r) = c₁ := by
      funext r; simp only [Function.comp_apply, hc₁_def]
    rw [hfun] at hcomp
    have hrhs : c₁ s = ((w (tₖ + s), deriv w (tₖ + s)) : E × E) := by rw [hc₁_def]
    rw [hrhs]; exact hcomp
  -- `c₂` satisfies `chartPhaseVF g α` on `Ioo (-T') T'`.
  have hc₂_phase : ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s := by
    intro s hs; exact hΦ_phase v hv s hs
  -- Both confined to `closedBall z₀ R`.
  have hc₁_in : ∀ s ∈ Set.Ioo (-T') T', c₁ s ∈ Metric.closedBall z₀ R := by
    intro s hs
    have htks : tₖ + s ∈ U := by
      rw [hU_def, Set.mem_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hgeo_in v hv (tₖ + s) htks
    rw [hc₁_def]; exact this
  have hc₂_in : ∀ s ∈ Set.Ioo (-T') T', c₂ s ∈ Metric.closedBall z₀ R := by
    intro s hs; exact hΦ_in v hv s hs
  -- Match at `0`.
  have hc₁_zero : c₁ 0 = z v := by
    rw [hc₁_def]; simp only [add_zero]; exact hinit v hv
  have hc₂_zero : c₂ 0 = z v := by rw [hc₂_def]; exact hΦinit v hv
  have hmatch : c₁ 0 = c₂ 0 := by rw [hc₁_zero, hc₂_zero]
  -- Uniform-in-parameter chart-phase ODE uniqueness on the compact ball.
  have heq : ∀ s ∈ Set.Ioo (-T') T', c₁ s = c₂ s :=
    chartPhaseVF_orbit_uniqueness_uniform_Ioo_closedBall (I := I) g α
      hball hT'_pos hc₁_phase hc₂_phase hc₁_in hc₂_in hmatch
  -- Evaluate at `s := t - tₖ ∈ Ioo (-T') T'`.
  have hs_mem : (t - tₖ) ∈ Set.Ioo (-T') T' := by
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · have := ht.1; rw [Set.mem_Ioo] at ht; linarith [ht.1]
    · rw [Set.mem_Ioo] at ht; linarith [ht.2]
  have hfst := congrArg Prod.fst (heq (t - tₖ) hs_mem)
  -- `(c₁ (t-tₖ)).1 = w (tₖ + (t - tₖ)) = w t = extChartAt I α (γ t)`.
  have hc₁_fst : (c₁ (t - tₖ)).1 = extChartAt I α (γ t) := by
    rw [hc₁_def]
    simp only []
    rw [show tₖ + (t - tₖ) = t by ring, hw_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
  have hc₂_fst : (c₂ (t - tₖ)).1 = (Φ (z v, t - tₖ)).1 := by rw [hc₂_def]
  rw [hc₁_fst, hc₂_fst] at hfst
  -- `hfst : extChartAt I α (γ t) = (Φ (z v, t - tₖ)).1`.
  -- Now `flowProj α Φ (z v) (t - tₖ) = (extChartAt I α).symm (Φ (z v, t - tₖ)).1`.
  have hγ_es : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hsrc_U t ht
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ t)) = γ t :=
    (extChartAt I α).left_inv hγ_es
  -- Goal (after `set γ`): `γ t = flowProj α Φ (z v) (t - tₖ)`.
  rw [flowProj, ← hfst, hsymm]

/-! ### Per-junction window producer (full assembly of the fully-proven inputs)

The following packages the three fully-proven per-junction producers
(`flowOrbit_uniform_confinement`, `perJunction_flowIdentification`,
`perChart_jointContinuity_of_flowIdentifiedOn`) together with the per-chart
joint-`C¹` phase flow `Φ` of
`Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined` into a single
*window* of joint continuity around a junction `tₖ`.

Its inputs are exactly the two genuinely cross-junction data the finite-cover
induction must propagate, supplied here as hypotheses (neither is the continuity
conclusion):

* `hz_cont`/`hz0` — continuity in `v` of the phase point
  `z v = (extChartAt I α (γ_v tₖ), deriv (chartCurve α γ_v) tₖ)`, with
  `z v₀` equal to the flow centre `(x₀, w₀)`;
* `hgeo` — uniform-in-`v` confinement of the geodesic to the chart `α` source and
  of its fixed-`α`-chart phase curve to the inner ball, on a window around `tₖ`,
  together with the matching of the geodesic's phase point at `tₖ` to `z v`.

The chart `α`, the flow `Φ`, and the inner-ball confinement of the flow orbit are
constructed *internally*: the orbit confinement comes from
`flowOrbit_uniform_confinement` (taking `W := ball (x₀, w₀) b.rIn`), and on the
inner ball the cutoff field equals the genuine `chartPhaseVF`, so the orbit solves
the chart-phase ODE; `perJunction_flowIdentification` then identifies the geodesic
with the flow projection and `perChart_jointContinuity_of_flowIdentifiedOn`
delivers joint continuity on the window. -/
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem intrinsicGeodesic_window_of_junction_data
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p)
    (α : M) {x₀ w₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target)
    {z : TangentSpace I p → E × E} {tₖ : ℝ} {rz : ℝ} (hrz : 0 < rz)
    (hz_cont : ContinuousOn z (Metric.ball v₀ rz)) (hz0 : z v₀ = (x₀, w₀))
    -- Uniform geodesic-side confinement on a window around `tₖ`:
    (hgeo : ∀ (b : ContDiffBump ((x₀, w₀) : E × E))
        (rwin εwin : ℝ),
      0 < rwin → 0 < εwin → rwin ≤ rz →
      Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
      (∀ v ∈ Metric.ball v₀ rwin, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) →
      (∀ v ∈ Metric.ball v₀ rwin, ∀ t ∈ Set.Ioo (tₖ - εwin) (tₖ + εwin),
        intrinsicGeodesic (I := I) g hEnorm p v t ∈ (chartAt H α).source) ∧
      (∀ v ∈ Metric.ball v₀ rwin, ∀ t ∈ Set.Ioo (tₖ - εwin) (tₖ + εwin),
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) t,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
          ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
      (∀ v ∈ Metric.ball v₀ rwin,
        ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v) tₖ,
          deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
            (intrinsicGeodesic (I := I) g hEnorm p v)) tₖ) : E × E) = z v)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ r) ×ˢ Set.Ioo (tₖ - ε) (tₖ + ε)) := by
  classical
  -- The per-chart joint-`C¹` phase flow `Φ` centred at the base phase point.
  obtain ⟨b, rPL, εPL, ρΦ, TΦ, Φ, hrPL, hεPL, hρΦ, hTΦ, hb_sub, hΦ_loc, hΦ_C1,
      hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined (I := I) (M := M)
      (g := g) (α := α) (x₀ := x₀) (v₀ := w₀) hx₀
  -- Continuity of `Φ` on the joint-`C¹` neighbourhood.
  have hΦ_cont : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρΦ) ×ˢ Set.Ioo (-TΦ) TΦ) :=
    hΦ_C1.continuousOn
  -- The confinement spatial radius `ρf := min ρΦ rPL` (≤ both the joint-`C¹` ball
  -- and the Picard ball), and time horizon `Tcap := min TΦ εPL`.
  have hrPL_pos : (0 : ℝ) < (rPL : ℝ) := by exact_mod_cast hrPL
  set ρf : ℝ := min ρΦ (rPL : ℝ) with hρf_def
  have hρf_pos : 0 < ρf := lt_min hρΦ hrPL_pos
  have hρf_le_ρΦ : ρf ≤ ρΦ := min_le_left _ _
  have hρf_le_rPL : ρf ≤ (rPL : ℝ) := min_le_right _ _
  set Tcap : ℝ := min TΦ εPL with hTcap_def
  have hTcap_pos : 0 < Tcap := lt_min hTΦ hεPL
  have hTcap_le_TΦ : Tcap ≤ TΦ := min_le_left _ _
  have hTcap_le_εPL : Tcap ≤ εPL := min_le_right _ _
  -- Restrict `Φ`-continuity to the smaller spatial ball and horizon.
  have hΦ_cont' : ContinuousOn Φ
      ((Metric.ball ((x₀, w₀) : E × E) ρf) ×ˢ Set.Ioo (-Tcap) Tcap) :=
    hΦ_cont.mono (Set.prod_mono (Metric.ball_subset_ball hρf_le_ρΦ)
      (Set.Ioo_subset_Ioo (by linarith [hTcap_le_TΦ]) hTcap_le_TΦ))
  -- Continuity of `z` at `v₀` (from the `ContinuousOn` on `ball v₀ rz`).
  have hz_contAt : ContinuousAt z v₀ :=
    hz_cont.continuousAt (Metric.ball_mem_nhds _ hrz)
  -- Inner-ball neighbourhood of the centre.
  have hW_nhds : Metric.ball ((x₀, w₀) : E × E) b.rIn ∈ 𝓝 ((x₀, w₀) : E × E) :=
    Metric.ball_mem_nhds _ b.rIn_pos
  -- Uniform confinement of the orbit to the inner ball.
  obtain ⟨S, T', hS_open, hv₀_S, hT'_pos, hT'_lt_Tcap, hz_ball_S, horbit_in⟩ :=
    flowOrbit_uniform_confinement (Φ := Φ) (z₀ := (x₀, w₀)) (ρ_f := ρf) (T_f := Tcap)
      (z := z) (v₀ := v₀) (W := Metric.ball ((x₀, w₀) : E × E) b.rIn)
      hρf_pos hTcap_pos hΦ_cont' hΦ_init0 hz_contAt hz0 hW_nhds
  -- Pick an open `ball v₀ r₀ ⊆ S`, then shrink to `r := min r₀ rz`.
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hS_open v₀ hv₀_S
  set r : ℝ := min r₀ rz with hr_def
  have hr_pos : 0 < r := lt_min hr₀_pos hrz
  have hr_le_r₀ : r ≤ r₀ := min_le_left _ _
  have hr_le_rz : r ≤ rz := min_le_right _ _
  have hr_sub : Metric.ball v₀ r ⊆ S :=
    subset_trans (Metric.ball_subset_ball hr_le_r₀) hr₀_sub
  -- Geometric facts about the bump radii.
  have hrIn_le_rOut : b.rIn ≤ b.rOut := le_of_lt b.rIn_lt_rOut
  have hballIn_sub_target : Metric.closedBall ((x₀, w₀) : E × E) b.rIn ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    subset_trans (Metric.closedBall_subset_closedBall hrIn_le_rOut) hb_sub
  -- `z v ∈ ball z₀ ρf ⊆ ball z₀ ρΦ` and `z v ∈ closedBall z₀ rPL` for `v ∈ ball v₀ r`.
  have hz_ball_ρf : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρf :=
    fun v hv => hz_ball_S v (hr_sub hv)
  have hz_ball_r : ∀ v ∈ Metric.ball v₀ r, z v ∈ Metric.ball ((x₀, w₀) : E × E) ρΦ :=
    fun v hv => Metric.ball_subset_ball hρf_le_ρΦ (hz_ball_ρf v hv)
  have hz_PL : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.closedBall ((x₀, w₀) : E × E) rPL := by
    intro v hv
    have := hz_ball_ρf v hv
    rw [Metric.mem_ball] at this
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le this hρf_le_rPL)
  -- `Φ (z v, 0) = z v` for `v ∈ ball v₀ r` (Picard initial law).
  have hΦinit : ∀ v ∈ Metric.ball v₀ r, Φ (z v, 0) = z v := by
    intro v hv
    exact hΦ_loc.apply_initial (z v) (hz_PL v hv)
  -- The flow-orbit stays in `closedBall z₀ b.rIn` on `Ioo (-T') T'`.
  have hΦ_in : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn := by
    intro v hv s hs
    exact Metric.ball_subset_closedBall (horbit_in v (hr_sub hv) s hs)
  -- `z v ∈ ball z₀ b.rIn` (orbit at `s = 0` is `z v`, which lies in the inner ball).
  have hz_ball_rIn : ∀ v ∈ Metric.ball v₀ r,
      z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn := by
    intro v hv
    have h0 : (0 : ℝ) ∈ Set.Ioo (-T') T' := ⟨by linarith, hT'_pos⟩
    have := horbit_in v (hr_sub hv) 0 h0
    rwa [hΦinit v hv] at this
  -- The flow-orbit ODE on `Ioo (-T') T'`: confined to the inner ball, the cutoff
  -- field equals `chartPhaseVF`, so the orbit solves the genuine chart-phase ODE.
  have hT'_le_εPL : T' ≤ εPL := le_of_lt (lt_of_lt_of_le hT'_lt_Tcap hTcap_le_εPL)
  have hΦ_phase : ∀ v ∈ Metric.ball v₀ r, ∀ s ∈ Set.Ioo (-T') T',
      HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVF (I := I) g α (Φ (z v, s))) s := by
    intro v hv s hs
    -- The flow's defining within-derivative at `s` over `Icc (-εPL) εPL`, value the
    -- cutoff field at the orbit point.
    have hs_Icc : s ∈ Set.Icc (-εPL) εPL := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hd := hΦ_loc.hasDerivWithinAt (z v) (hz_PL v hv) s hs_Icc
    -- Upgrade `HasDerivWithinAt` on `Icc` to `HasDerivAt` at the interior point `s`.
    have hIoo_nhds : Set.Ioo (-εPL) εPL ∈ 𝓝 s := by
      apply isOpen_Ioo.mem_nhds
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hs.1, hT'_le_εPL], by linarith [hs.2, hT'_le_εPL]⟩
    have hIcc_nhds : Set.Icc (-εPL) εPL ∈ 𝓝 s :=
      Filter.mem_of_superset hIoo_nhds Set.Ioo_subset_Icc_self
    have hd' : HasDerivAt (fun τ => Φ (z v, τ))
        (chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s))) s :=
      hd.hasDerivAt hIcc_nhds
    -- On the inner ball, the cutoff field equals `chartPhaseVF`.
    have horbit_inner : Φ (z v, s) ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn :=
      hΦ_in v hv s hs
    have hcutoff_eq :
        chartPhaseVFTime (I := I) g α (x₀, w₀) b s (Φ (z v, s)) =
          chartPhaseVF (I := I) g α (Φ (z v, s)) := by
      rw [chartPhaseVFTime_apply]
      exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α (x₀, w₀) b horbit_inner
    rwa [hcutoff_eq] at hd'
  -- The geodesic-side confinement at horizon `T'` from the hypothesis `hgeo`.
  obtain ⟨hgeo_src, hgeo_in, hinit⟩ := hgeo b r T' hr_pos hT'_pos hr_le_rz hb_sub
    hz_ball_rIn
  -- Identify the geodesic with the flow projection on the window.
  have hident := perJunction_flowIdentification (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := (x₀, w₀)) (z := z) (tₖ := tₖ) (r := r) (R := b.rIn)
    (T' := T') hT'_pos hballIn_sub_target hΦ_phase hΦ_in hgeo_src hgeo_in hinit hΦinit
  -- Deliver joint continuity on the window.
  refine ⟨r, T', hr_pos, hT'_pos, ?_⟩
  -- `htgt`: the flowed first component lies in the chart target, from inner-ball
  -- confinement (inner ball ⊆ interior target ×ˢ univ).
  have htgt : ∀ v ∈ Metric.ball v₀ r, ∀ τ ∈ Set.Ioo (-T') T',
      (Φ (z v, τ)).1 ∈ (extChartAt I α).target := by
    intro v hv τ hτ
    have hin := hΦ_in v hv τ hτ
    have := hballIn_sub_target hin
    exact interior_subset this.1
  -- `z` is continuous on `ball v₀ r ⊆ ball v₀ rz`.
  have hz_cont_r : ContinuousOn z (Metric.ball v₀ r) :=
    hz_cont.mono (Metric.ball_subset_ball hr_le_rz)
  exact perChart_jointContinuity_of_flowIdentifiedOn (I := I) g hEnorm p v₀
    (α := α) (Φ := Φ) (z₀ := (x₀, w₀)) (z := z) (tₖ := tₖ) (ε := T') (r := r)
    (ρ := ρΦ) (T := TΦ) (le_of_lt (lt_of_lt_of_le hT'_lt_Tcap hTcap_le_TΦ))
    hΦ_cont hz_cont_r hz_ball_r htgt hident

/-! ### Finite-cover assembly: from local time-windows to a uniform ball

The per-junction producer `perChart_jointContinuity_of_flowIdentifiedOn` yields
joint continuity on a *local* window `ball v₀ r ×ˢ Ioo (t - ε) (t + ε)` around
each time `t ∈ [0, 1]`.  The following purely-topological lemma assembles these
local windows into a single `ContinuousOn` on `ball v₀ ρ ×ˢ [0, 1]` for a uniform
`ρ > 0`: the open `ε`-balls in time cover the compact `[0, 1]`, a finite subcover
fixes finitely many windows, `ρ` is the minimum of the finitely many radii, and
the windows glue because joint continuity is a local property (each point of the
product lies in some window, whose `ContinuousOn` restricts to a
`ContinuousWithinAt`). -/
private theorem continuousOn_ball_prod_Icc_of_local_windows
    {V : Type*} [PseudoMetricSpace V] {Y : Type*} [TopologicalSpace Y]
    (v₀ : V) (f : V × ℝ → Y)
    (H : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
        ContinuousOn f ((Metric.ball v₀ r) ×ˢ Set.Ioo (t - ε) (t + ε))) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn f ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  -- Choose the window data per time.
  choose! r ε hr hε hcont using H
  -- The open `ε`-balls cover the compact `[0, 1]`.
  set U : Set.Icc (0 : ℝ) 1 → Set ℝ := fun t => Metric.ball (t : ℝ) (ε t) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun _ => Metric.isOpen_ball
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ t, U t := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp only [hU]
    exact Metric.mem_ball_self (hε x hx)
  obtain ⟨S, hS⟩ := isCompact_Icc.elim_finite_subcover U hUopen hcover
  -- `S` is nonempty (else `[0, 1] ⊆ ∅`, contradicting `0 ∈ [0, 1]`).
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    have hmem := hS h0
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨t, ht, _⟩ := hmem
    exact (Finset.notMem_empty t) ht
  -- The uniform radius: the minimum of the finitely many `r` over `S` (positive).
  set ρ : ℝ := S.inf' hSne (fun t => r (t : ℝ)) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, Finset.lt_inf'_iff]
    intro t _
    exact hr (t : ℝ) t.2
  have hρ_le : ∀ t ∈ S, ρ ≤ r (t : ℝ) := by
    intro t ht
    rw [hρ]; exact Finset.inf'_le _ ht
  refine ⟨ρ, hρpos, ?_⟩
  -- Prove `ContinuousOn` pointwise.
  rintro ⟨v, x⟩ ⟨hv, hx⟩
  -- The point's time lies in some chosen window's `ε`-ball.
  obtain ⟨t, ht_S, hW_eq⟩ := Set.mem_iUnion₂.mp (hS hx)
  simp only [hU] at hW_eq
  -- The window on which `f` is continuous.
  set Wt : Set (V × ℝ) :=
    (Metric.ball v₀ (r (t : ℝ))) ×ˢ Set.Ioo ((t : ℝ) - ε (t : ℝ)) ((t : ℝ) + ε (t : ℝ))
    with hWt
  have hcontWt : ContinuousOn f Wt := hcont (t : ℝ) t.2
  have hx_Ioo : x ∈ Set.Ioo ((t : ℝ) - ε (t : ℝ)) ((t : ℝ) + ε (t : ℝ)) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hW_eq
    exact ⟨by linarith [hW_eq.1], by linarith [hW_eq.2]⟩
  have hv_Wt : v ∈ Metric.ball v₀ (r (t : ℝ)) :=
    Metric.ball_subset_ball (hρ_le t ht_S) hv
  have hcwa : ContinuousWithinAt f Wt (v, x) := hcontWt _ ⟨hv_Wt, hx_Ioo⟩
  -- An open neighbourhood of `(v, x)` contained in `Wt`.
  set N : Set (V × ℝ) := (Metric.ball v₀ ρ) ×ˢ (Metric.ball (t : ℝ) (ε (t : ℝ))) with hN
  have hN_open : IsOpen N := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hpt_N : (v, x) ∈ N := ⟨hv, by
    rw [Metric.mem_ball, Real.dist_eq] at hW_eq ⊢; exact hW_eq⟩
  have hN_sub_Wt : N ⊆ Wt := by
    rintro ⟨w, y⟩ ⟨hw, hy⟩
    refine ⟨Metric.ball_subset_ball (hρ_le t ht_S) hw, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcwa_N : ContinuousWithinAt f N (v, x) := hcwa.mono hN_sub_Wt
  exact hcwa_N.mono_of_mem_nhdsWithin (nhdsWithin_le_nhds (hN_open.mem_nhds hpt_N))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Joint continuity of the chained intrinsic geodesic flow (analytic
residual).** For every launch velocity `v₀` there is a radius `ρ > 0` such that
`(v, t) ↦ intrinsicGeodesic g hEnorm p v t` is jointly continuous on
`ball v₀ ρ ×ˢ [0, 1]`.

Its closure is reduced to the per-junction phase-point/confinement data by the
fully-proven producers above:

* `flowProj_continuousOn` — the foot-varying flow projection
  `(n, τ) ↦ (extChartAt I α).symm (Φ (z n, τ)).1` is jointly continuous whenever
  the per-chart phase flow `Φ` is continuous, the phase parameter `z` is
  continuous, and the flowed first component stays in the chart target;
* `perChart_jointContinuity_of_flowIdentifiedOn` — given a *uniform-in-`v`*
  identification of the intrinsic geodesic with the foot-varying flow projection
  on a window `ball v₀ r ×ˢ Ioo (tₖ - ε) (tₖ + ε)`, the intrinsic geodesic is
  jointly continuous there;
* `geodesic_chartPhaseVF_on_open` — the geodesic's *fixed*-`α`-chart phase curve
  satisfies the genuine chart-phase ODE `chartPhaseVF g α` wherever the geodesic
  stays in the chart-`α` source (the fixed-chart reading of the moving-foot
  geodesic equation);
* `perJunction_flowIdentification` — the **uniform-in-`v` identification**
  `intrinsicGeodesic g hEnorm p v t = flowProj α Φ (z v) (t - tₖ)` on a window,
  from the geodesic-side and flow-side chart-phase ODEs together with confinement
  of both to a common compact ball and matching initial phase data, via
  `chartPhaseVF_orbit_uniqueness_uniform_Ioo`.  This is the genuine analytic
  heart (STEP 1, the residual bootstrap) — fully proven.

What remains is the finite-cover induction (STEP 2): supply, junction by junction
along the finite chart cover `intrinsicGeodesic_arc_finite_chart_cover`, the data
feeding `perJunction_flowIdentification` / `perChart_jointContinuity_of_flowIdentifiedOn`.
The per-chart phase flow `Φ` comes from
`Geodesic.SmoothFlow.exists_chartPhase_contDiffOn_isLocalFlow_combined` (jointly
`C¹` hence continuous), centred at the base-velocity phase point at the junction;
`flowOrbit_uniform_confinement` produces the uniform-in-`v` confinement window for
the flow orbit.  The base case `tₖ = 0` has chart centre `p` and phase point
`(extChartAt I p p, v)` (continuous in `v` directly).  The genuinely remaining
analytic content is the **cross-junction propagation of the phase-point
continuity** `z : v ↦ (extChartAt I α (γ_v tₖ), deriv (chartCurve α γ_v) tₖ)`: at
an interior junction the chart velocity `deriv (chartCurve α γ_v) tₖ` must be
shown continuous in `v`, which couples the joint continuity established on the
*previous* window (for the foot continuity) with the `C¹`-in-time regularity
`intrinsicGeodesic_contMDiffOn` and the `C¹` flow `Φ` (for the velocity
continuity).  Once that phase-point continuity is propagated, `ContinuousOn.union`
over the finite cover assembles joint continuity on `ball v₀ (min_k r_k) ×ˢ [0, 1]`.

Everything else in the file (`intrinsicGeodesic_compactArc`,
`intrinsicGeodesic_arc_finite_chart_cover`, and the producers above) is proved
unconditionally, and `expMapIntrinsic_continuous` follows from this residual in
one step. -/
theorem intrinsicGeodesic_jointContinuity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  -- Joint continuity is local in time; by `continuousOn_ball_prod_Icc_of_local_windows`
  -- it suffices to produce, at every base time `t ∈ [0, 1]`, a window
  -- `ball v₀ r ×ˢ Ioo (t - ε) (t + ε)` of joint continuity, with a uniform ball
  -- radius then extracted from the finite subcover of `[0, 1]`.
  classical
  -- `E` is finite-dimensional real normed, hence complete.
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine continuousOn_ball_prod_Icc_of_local_windows (V := TangentSpace I p) v₀
    (fun vt => intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2) ?_
  intro t ht
  -- The junction chart is centred at the base-velocity foot `α := γ_{v₀} t`.
  set α : M := intrinsicGeodesic (I := I) g hEnorm p v₀ t with hα_def
  -- The phase-point map `z v := (chart-coord of foot γ_v t, chart velocity of γ_v at t)`.
  set z : TangentSpace I p → E × E :=
    fun v =>
      ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v) t,
        deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
          (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E)
    with hz_def
  set x₀ : E := (z v₀).1 with hx₀_def
  set w₀ : E := (z v₀).2 with hw₀_def
  -- The base phase point's first component is `extChartAt I α α` (since `γ_{v₀} t = α`),
  -- which lies in the chart-target interior by boundarylessness.
  have hα_foot : intrinsicGeodesic (I := I) g hEnorm p v₀ t = α := rfl
  have hx₀_eq : x₀ = extChartAt I α α := by
    rw [hx₀_def, hz_def]
    simp only [DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve_def]
    rw [hα_foot]
  have hx₀ : x₀ ∈ interior (extChartAt I α).target := by
    rw [hx₀_eq]
    have hsrc : α ∈ (extChartAt I α).source := mem_extChartAt_source (I := I) α
    have htgt : extChartAt I α α ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α htgt
  have hz0 : z v₀ = (x₀, w₀) := by rw [hx₀_def, hw₀_def]
  -- The window now follows from the per-junction producer once the two genuinely
  -- cross-junction data — continuity of the phase point `z` in `v` near `v₀`, and
  -- the uniform geodesic-side confinement at the junction — are supplied.
  -- These are the residual content of the finite-cover induction.
  obtain ⟨rz, hrz, hz_cont, hgeo⟩ :
      ∃ rz : ℝ, 0 < rz ∧ ContinuousOn z (Metric.ball v₀ rz) ∧
      (∀ (b : ContDiffBump ((x₀, w₀) : E × E))
          (rwin εwin : ℝ),
        0 < rwin → 0 < εwin → rwin ≤ rz →
        Metric.closedBall ((x₀, w₀) : E × E) b.rOut ⊆
          (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) →
        (∀ v ∈ Metric.ball v₀ rwin, z v ∈ Metric.ball ((x₀, w₀) : E × E) b.rIn) →
        (∀ v ∈ Metric.ball v₀ rwin, ∀ s ∈ Set.Ioo (t - εwin) (t + εwin),
          intrinsicGeodesic (I := I) g hEnorm p v s ∈ (chartAt H α).source) ∧
        (∀ v ∈ Metric.ball v₀ rwin, ∀ s ∈ Set.Ioo (t - εwin) (t + εwin),
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v) s,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v)) s) : E × E)
            ∈ Metric.closedBall ((x₀, w₀) : E × E) b.rIn) ∧
        (∀ v ∈ Metric.ball v₀ rwin,
          ((DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v) t,
            deriv (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α
              (intrinsicGeodesic (I := I) g hEnorm p v)) t) : E × E) = z v)) := by
    -- RESIDUAL (the cross-junction induction).  This is the single remaining
    -- analytic input: at the base time `t`, the phase-point map
    -- `z v = (chartCurve α γ_v t, deriv (chartCurve α γ_v) t)` is continuous in `v`
    -- near `v₀`, and the geodesic stays uniformly (in `v`) in the chart-`α` source
    -- with its fixed-`α`-chart phase curve confined to the inner ball on a window,
    -- matching `z v` at `t`.  For `t = 0` (chart `α = p`) the first component of `z`
    -- is constant and the second is the trivialization-linear image of `v`, so `z`
    -- is continuous directly; the geodesic-side confinement and the interior
    -- junctions `t > 0` are obtained by inducting along the finite chart cover
    -- `intrinsicGeodesic_arc_finite_chart_cover`, coupling the joint continuity
    -- established on the previous window (foot continuity) with
    -- `intrinsicGeodesic_contMDiffOn` (`C¹`-in-time) and the `C¹` flow `Φ`
    -- (velocity continuity).  Everything downstream of this datum
    -- (`intrinsicGeodesic_window_of_junction_data`, the finite-cover assembly, and
    -- `expMapIntrinsic_continuous`) is fully proven.
    sorry
  exact intrinsicGeodesic_window_of_junction_data (I := I) g hEnorm p v₀ α
    (x₀ := x₀) (w₀ := w₀) hx₀ (z := z) (tₖ := t) (rz := rz) hrz hz_cont hz0 hgeo

/-! ## 4. Continuity of the intrinsic exponential map -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Continuity-from-joint reduction.** Given the per-ball joint continuity of
the chained intrinsic geodesic flow (the producer
`intrinsicGeodesic_jointContinuity`), the intrinsic exponential map
`v ↦ expMapIntrinsic g hEnorm p v` is continuous.

This is the structural reduction: `expMapIntrinsic g hEnorm p v =
intrinsicGeodesic g hEnorm p v 1` definitionally, and continuity at each `v₀`
follows from the joint continuity on the neighbourhood `ball v₀ ρ ×ˢ [0, 1]`
precomposed with the continuous slice map `v ↦ (v, 1)`.  It mirrors the
chart-fixed `bm_c_expMap_continuity_from_jointFlow` but consumes the *intrinsic*
joint-continuity producer.  Fully unconditional (no `sorry`); the only analytic
content is delegated to the hypothesis `hjoint`. -/
theorem expMapIntrinsic_continuous_of_jointContinuity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M)
    (hjoint : ∀ v₀ : TangentSpace I p, ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    Continuous (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) := by
  -- Continuity is pointwise: prove `ContinuousAt (expMapIntrinsic g hEnorm p) v₀`
  -- for each `v₀`.
  rw [continuous_iff_continuousAt]
  intro v₀
  -- Joint continuity of `(v, t) ↦ intrinsicGeodesic g hEnorm p v t` on a
  -- neighbourhood ball of `v₀` times `[0, 1]`.
  obtain ⟨ρ, hρ, hcont⟩ := hjoint v₀
  -- The slice map `v ↦ (v, 1)` is continuous and lands in the domain.
  set F : TangentSpace I p × ℝ → M :=
    fun vt => intrinsicGeodesic (I := I) g hEnorm p vt.1 vt.2 with hF_def
  set sl : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hsl_def
  -- `expMapIntrinsic g hEnorm p = F ∘ sl` (definitionally).
  have hcomp_eq :
      (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) = F ∘ sl := by
    funext v
    simp only [Function.comp_apply, hF_def, hsl_def, expMapIntrinsic]
  rw [hcomp_eq]
  -- `sl` is continuous and maps `ball v₀ ρ` into `ball v₀ ρ ×ˢ [0, 1]`.
  have hsl_cont : Continuous sl := by
    rw [hsl_def]; exact continuous_id.prodMk continuous_const
  have hsl_maps : Set.MapsTo sl (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    exact ⟨hv, ⟨zero_le_one, le_refl 1⟩⟩
  -- `ball v₀ ρ` is a neighbourhood of `v₀`.
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  -- `F ∘ sl` is continuous within `ball v₀ ρ` at `v₀`, hence continuous at `v₀`.
  have hcw : ContinuousWithinAt (F ∘ sl) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hcont.comp hsl_cont.continuousOn hsl_maps
  exact hcw.continuousAt hball_nhds

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Continuity of the intrinsic exponential map.** On a complete Riemannian
manifold the intrinsic exponential map `v ↦ expMapIntrinsic g hEnorm p v` is
continuous.

The compactness / diameter endpoint (`bonnetMyers_compact`) consumes this as
"`M = expMapIntrinsic g p '' closedBall` is a continuous image of a compact
set".

The proof is the reduction `expMapIntrinsic_continuous_of_jointContinuity` fed by
the joint-continuity producer `intrinsicGeodesic_jointContinuity`. -/
theorem expMapIntrinsic_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    Continuous (fun v : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p v) :=
  expMapIntrinsic_continuous_of_jointContinuity (I := I) g hEnorm p
    (fun v₀ => intrinsicGeodesic_jointContinuity (I := I) g hEnorm p v₀)

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
