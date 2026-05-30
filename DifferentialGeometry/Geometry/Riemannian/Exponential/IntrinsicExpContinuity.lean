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
    (the `IsGeodesicAt g γ₀ tₖ` hypothesis is the chart-flow datum produced by the
    extension engine of `IntrinsicExp.lean`; it is the converse direction
    `HasGeodesicEquationAt → IsGeodesicAt` for the intrinsic geodesic, recorded as
    `intrinsicGeodesic_isGeodesicAt` below).

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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Joint continuity of the chained intrinsic geodesic flow (analytic
residual).** For every launch velocity `v₀` there is a radius `ρ > 0` such that
`(v, t) ↦ intrinsicGeodesic g hEnorm p v t` is jointly continuous on
`ball v₀ ρ ×ˢ [0, 1]`.

This is the only `sorry` in the file; its sub-lemma decomposition is in the
section docstring above (per-chart re-based continuous flow via the proven
cross-chart re-basing `bm_c_gc_cross_vf_projection_uniqueness`, uniqueness
identification via `isGeodesicAt_eventuallyEq_of_lift_eq`, and finite junction
gluing).  Everything else in the file (`intrinsicGeodesic_compactArc`,
`intrinsicGeodesic_arc_finite_chart_cover`,
`expMapIntrinsic_continuous_of_jointContinuity`) is proved unconditionally, and
`expMapIntrinsic_continuous` follows from this residual in one step. -/
theorem intrinsicGeodesic_jointContinuity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
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
  sorry

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
