import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.Exponential.PreconnectedPropagation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.FlowC1Continuous
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

/-!
# Chain-of-charts continuity of the exponential map

This file collects the six chained-flow continuity steps used to deduce
`Continuous (expMap g p)` on a geodesically complete Riemannian manifold:
compactness of the geodesic segment `γ([0, 1])`, a finite chart-cover
partition via the Lebesgue-number lemma, per-chart joint-`C¹` local flows
from Picard–Lindelöf, continuity at chart junctions via the local-flow
group-property gluing, and the final continuity statement obtained by
specialising the joint flow to `t = 1`.

The detailed Lean types of the intermediate joint-flow predicates are
deferred to the proof phase; here we expose only the propositional
shells required to record the chain. The headline statement is
`bm_c_expMap_continuity_from_jointFlow`, whose signature is
`Continuous (expMap g p)`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

/-! ## 0. Local continuity of the maximal geodesic near `t = 0`

The canonical maximal geodesic is, by construction, a pointwise
`Classical.choose` of local integral-curve witnesses, so its continuity
is not automatic. Near `t = 0` it agrees with a single Picard–Lindelöf
lift on a ball (`picardLift_proj_eq_maximalGeodesic_on_ball`), and that
lift is continuous as a (projected) integral curve. This gives a fully
unconditional local continuity statement at `0`. -/

/-- The maximal geodesic `maximalGeodesic g p v` is continuous at `t = 0`.
Its value near `0` coincides with the projection of a single
Picard–Lindelöf integral curve `g_v` (via
`picardLift_proj_eq_maximalGeodesic_on_ball`), and that projection is
continuous as a base curve of an integral curve. -/
theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  -- A Picard–Lindelöf lift of the geodesic vector field at `(p, v)`.
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  -- The lift is continuous at `0` (integral curve), hence so is its
  -- projection to `M`.
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  -- `maximalGeodesic g p v = (g_v ·).proj` on a ball around `0`.
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm

/-! ## 1. Compactness of the geodesic segment image -/

/-- The image of `[0, 1]` under `maximalGeodesic g p v₀` is a compact
subset of `M`. -/
theorem bm_c_expMap_geodesicSegment_compactImage
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    IsCompact (maximalGeodesic (I := I) g p v₀ '' Set.Icc (0 : ℝ) 1) := by
  -- Continuous image of a compact set is compact. The unit interval
  -- `[0, 1]` is compact (`isCompact_Icc`).
  --
  -- The remaining content is the continuity of `maximalGeodesic g p v₀`
  -- on `[0, 1]`. The canonical maximal geodesic is a pointwise
  -- `Classical.choose` of local integral-curve witnesses, so continuity
  -- at a time `t` requires identifying it, near `t`, with a *single*
  -- continuous integral curve. Near `t = 0` this is fully unconditional
  -- (`maximalGeodesic_continuousAt_zero`, proved above via
  -- `picardLift_proj_eq_maximalGeodesic_on_ball`). At a general
  -- `t ∈ [0, 1]` the identification additionally needs:
  --
  --   * geodesic completeness, i.e. `[0, 1] ⊆ maximalGeodesicInterval`
  --     (`HopfRinow.bm_c_gc_assemble`), so that the arc is in the domain;
  --   * the cross-chart-basepoint integral-curve uniqueness
  --     `Geodesic.bm_c_gc_cross_vf_projection_uniqueness`, which re-bases
  --     the chart-fixed geodesic vector field at each `γ(t)` (the
  --     time-`0` chart of `p` need not cover the whole arc), producing a
  --     `γ(t)`-centred lift whose projection agrees with the maximal
  --     geodesic on a neighbourhood of `t`; that lift is continuous as a
  --     base curve of an integral curve.
  --
  -- Both prerequisites are presently `sorry`-backed elsewhere in the
  -- project (`HopfRinow.bm_c_gc_assemble`,
  -- `Geodesic.bm_c_gc_cross_vf_projection_uniqueness`), so consuming
  -- them here would propagate `sorryAx`. The single residual recorded
  -- here is exactly the whole-arc continuity that those two lemmas would
  -- supply.
  have h_cont :
      ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
    sorry
  exact isCompact_Icc.image_of_continuousOn h_cont

/-! ## 2. Finite chart-cover via the Lebesgue-number lemma -/

/-- Existence of a chart-cover partition of the unit interval along the
geodesic `maximalGeodesic g p v₀`: a `True`-shelled propositional shell
recording the witness `(n, t, idx)` produced by the Lebesgue-number
lemma. The detailed type is deferred. -/
theorem bm_c_expMap_finite_chartCover
    (_g : SmoothRiemannianMetric I M) (_p : M) (_v₀ : TangentSpace I _p) :
    True := by
  trivial

/-! ## 3. Per-chart joint-`C¹` local flow (Picard–Lindelöf) -/

/-- Per-chart Picard–Lindelöf local flow with joint-`C¹` regularity on a
product `ball × Ioo (-T) T`. The detailed type is deferred. -/
theorem bm_c_expMap_perChart_jointFlow
    (_g : SmoothRiemannianMetric I M) (_q : M) :
    True := by
  trivial

/-! ## 4. Continuity at a chart junction -/

/-- The composition of two adjacent chart flows is continuous in the
initial datum, and its projection to the tangent bundle is an integral
curve of the next chart's geodesic vector field near the junction time.
The detailed type is deferred. -/
theorem bm_c_expMap_chartJunction_continuity
    (_g : SmoothRiemannianMetric I M) (_p : M) (_v₀ : TangentSpace I _p) :
    True := by
  trivial

/-! ## 5. Joint continuity of the chained flow on a ball × `[0, 1]` -/

/-- For every initial velocity `v₀` there exists a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
continuous on `Metric.ball v₀ ρ × Set.Icc 0 1`. -/
theorem bm_c_expMap_chainedFlow_joint_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          maximalGeodesic (I := I) g p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  -- Joint continuity of the chained flow in `(v, t)`. The engine is the
  -- per-chart joint-`C¹` Picard–Lindelöf flow, which is available on a
  -- product `ball × Ioo (-T) T` around `(v, 0)` in a single chart
  -- (`Geodesic.SmoothFlow.exists_chartPhase_contDiffOn_isLocalFlow_combined`
  -- gives `ContDiffOn ℝ 1 Φ (ball ×ˢ Ioo (-T) T)`), and whose projection
  -- agrees with `maximalGeodesic` near `0` uniformly in `v`
  -- (`PreconnectedPropagation.exists_chartFlowOrbitLift_proj_eq_maximalGeodesic_data`).
  --
  -- Globalising this from the time-`0` chart to the whole interval
  -- `[0, 1]` requires chaining the per-chart joint flows across chart
  -- junctions (steps 2–4 of this file) and the *uniform-in-`v`*
  -- extension of the projection identity beyond the time-`0`
  -- neighbourhood — explicitly flagged as a separate downstream task in
  -- `exists_chartFlowOrbitLift_proj_eq_maximalGeodesic_data`. The
  -- cross-junction gluing rests on the same cross-chart-basepoint
  -- integral-curve uniqueness
  -- `Geodesic.bm_c_gc_cross_vf_projection_uniqueness` (currently
  -- `sorry`-backed) used for the single-curve continuity of step 1.
  -- The residual recorded here is precisely that uniform-in-`v`,
  -- cross-junction joint continuity.
  sorry

/-! ## 6. Continuity of `expMap g p` -/

/-- The exponential map `expMap g p` is continuous on `T_p M`.

This is obtained from the joint continuity of the chained flow
(`bm_c_expMap_chainedFlow_joint_continuity`) by restricting to the
`t = 1` slice: `expMap g p v = maximalGeodesic g p v 1` definitionally,
and continuity at each `v₀` follows from joint continuity on the
neighbourhood `ball v₀ ρ ×ˢ Icc 0 1`, precomposed with the continuous
slice map `v ↦ (v, 1)`. -/
theorem bm_c_expMap_continuity_from_jointFlow
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  -- Continuity is pointwise: prove `ContinuousAt (expMap g p) v₀` for each `v₀`.
  rw [continuous_iff_continuousAt]
  intro v₀
  -- Joint continuity of `(v, t) ↦ maximalGeodesic g p v t` on a
  -- neighbourhood ball of `v₀` times `[0, 1]`.
  obtain ⟨ρ, hρ, hjoint⟩ :=
    bm_c_expMap_chainedFlow_joint_continuity (I := I) g p v₀
  -- The slice map `v ↦ (v, 1)` is continuous and lands in the domain.
  set F : TangentSpace I p × ℝ → M :=
    fun vt => maximalGeodesic (I := I) g p vt.1 vt.2 with hF_def
  set s : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hs_def
  -- `expMap g p = F ∘ s` (definitionally, via `expMap_apply`).
  have hcomp_eq : expMap (I := I) g p = F ∘ s := by
    funext v
    simp only [Function.comp_apply, hF_def, hs_def, expMap]
  rw [hcomp_eq]
  -- `s` is continuous and maps `ball v₀ ρ` into `ball v₀ ρ ×ˢ Icc 0 1`.
  have hs_cont : Continuous s := by
    rw [hs_def]; exact continuous_id.prodMk continuous_const
  have hs_maps : Set.MapsTo s (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    refine ⟨hv, ?_⟩
    exact ⟨zero_le_one, le_refl 1⟩
  -- `ball v₀ ρ` is a neighbourhood of `v₀`.
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  -- `F ∘ s` is continuous within `ball v₀ ρ` at `v₀`, hence continuous at `v₀`.
  have hcw : ContinuousWithinAt (F ∘ s) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hjoint.comp hs_cont.continuousOn hs_maps
  exact hcw.continuousAt hball_nhds

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
