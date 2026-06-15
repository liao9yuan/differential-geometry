import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Exponential.ChartFlow.PreconnectedPropagation
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
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
`expMap_continuous`, whose signature is
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

/-- The base curve `γ` of a geodesic witness `IsGeodesicOnWithInitial g γ J p v`
is continuous on `J`: it is the bundle projection of a tangent-bundle integral
curve of the chart-fixed geodesic vector field, and integral curves are
continuous on their domain. -/
lemma IsGeodesicOnWithInitial.continuousOn_base
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    ContinuousOn γ J := by
  obtain ⟨f, hproj, _hf0, hf⟩ := hγ
  have hf_cont : ContinuousOn f J := hf.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr (fun t _ht => (hproj t).symm)

/-- **Identification of the maximal geodesic with a witness lift, under
foot-in-source.** If `f` is a tangent-bundle integral curve of the chart-`p`
geodesic vector field on an open preconnected `J ∋ 0`, starting at `⟨p, v⟩`,
whose base curve stays in `(chartAt H p).source` throughout `J`, then
`maximalGeodesic g p v` agrees with `t ↦ (f t).proj` on `J`.

This generalises `picardLift_proj_eq_maximalGeodesic_on_ball` from a ball
around `0` to any such witness interval.  The foot-in-source hypothesis is
unavoidable: it is exactly what `isMIntegralCurveOn_eq_of_isPreconnected`
requires to propagate the agreement across `J`, since the chart-`p` geodesic
vector field degenerates once the foot leaves `(chartAt H p).source`. -/
lemma maximalGeodesic_eqOn_lift_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    Set.EqOn (maximalGeodesic (I := I) g p v) (fun t => (f t).proj) J := by
  classical
  intro t ht
  have hwit : MaximalGeodesicWitness (I := I) g p v t :=
    ⟨projectCurve (I := I) f, J, hJ_open, hJ_conn, h0J, ht,
      ⟨f, fun s => rfl, hf0, hf_on⟩⟩
  have htmem : t ∈ maximalGeodesicInterval (I := I) g p v := hwit
  have hval : maximalGeodesic (I := I) g p v t = (f t).proj := by
    rw [maximalGeodesic_of_mem (I := I) htmem]
    obtain ⟨J', hJ'_open, hJ'_conn, h0J', htJ', f', hproj', hf'0, hf'_on⟩ :=
      maximalGeodesicChosenCurve_spec (I := I) g p v htmem
    set K : Set ℝ := J ∩ J' with hK_def
    have hK_open : IsOpen K := hJ_open.inter hJ'_open
    have hK_conn : IsPreconnected K := by
      have hJ_ord : Set.OrdConnected J := hJ_conn.ordConnected
      have hJ'_ord : Set.OrdConnected J' := hJ'_conn.ordConnected
      exact (hJ_ord.inter hJ'_ord).isPreconnected
    have h0_K : (0 : ℝ) ∈ K := ⟨h0J, h0J'⟩
    have ht_K : t ∈ K := ⟨ht, htJ'⟩
    have hf_on_K : IsMIntegralCurveOn f
        (geodesicVectorFieldChart (I := I) g p) K :=
      hf_on.mono Set.inter_subset_left
    have hf'_on_K : IsMIntegralCurveOn f'
        (geodesicVectorFieldChart (I := I) g p) K :=
      hf'_on.mono Set.inter_subset_right
    have hf_src_K : ∀ s ∈ K, (f s).proj ∈ (chartAt H p).source :=
      fun s hs => hsrc s hs.1
    have heqOn := isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g)
      (p := p) (f₁ := f) (f₂ := f') hK_open hK_conn h0_K hf_on_K hf'_on_K
      hf_src_K (by rw [hf0, hf'0])
    have ht_eq : f t = f' t := heqOn ht_K
    rw [ht_eq]
    exact (hproj' t).symm
  exact hval

/-- **Continuity of the maximal geodesic on a foot-in-source witness
interval.** Under the same hypotheses as
`maximalGeodesic_eqOn_lift_of_footInSource`, `maximalGeodesic g p v` is
continuous on `J`. -/
lemma maximalGeodesic_continuousOn_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    ContinuousOn (maximalGeodesic (I := I) g p v) J := by
  have heq := maximalGeodesic_eqOn_lift_of_footInSource (I := I)
    hJ_open hJ_conn h0J hf0 hf_on hsrc
  have hf_cont : ContinuousOn f J := hf_on.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr heq

/-- The maximal geodesic `maximalGeodesic g p v` is continuous at `t = 0`.
Its value near `0` coincides with the projection of a single
Picard–Lindelöf integral curve `g_v` (via
`picardLift_proj_eq_maximalGeodesic_on_ball`), and that projection is
continuous as a base curve of an integral curve. -/
theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm

/-- The image of `[0, 1]` under `maximalGeodesic g p v₀` is a compact
subset of `M`. -/
theorem expMap_geodesicSegment_compactImage
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    IsCompact (maximalGeodesic (I := I) g p v₀ '' Set.Icc (0 : ℝ) 1) := by
  have h_cont :
      ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
    sorry
  exact isCompact_Icc.image_of_continuousOn h_cont

/-- For every initial velocity `v₀` there exists a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
continuous on `Metric.ball v₀ ρ × Set.Icc 0 1`. -/
theorem expMap_chainedFlow_joint_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          maximalGeodesic (I := I) g p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

/-- **Joint `C¹` regularity of the chained geodesic flow on a ball.**
For a *nonzero* initial velocity `v₀`, there is a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
`ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1` on
`Metric.ball v₀ ρ ×ˢ Set.Icc 0 1`.

This is the `C¹`-in-`(v, t)` strengthening of
`expMap_chainedFlow_joint_continuity`; restricting it to the
`t = 1` slice and precomposing with the smooth slice map `w ↦ (w, 1)`
yields the off-zero exponential-map regularity
`expMap_contMDiffAt_of_ne_zero`. -/
theorem expMap_chainedFlow_joint_contMDiff
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : E)
    (hv₀ : (show TangentSpace I p from v₀) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1
        (fun vt : E × ℝ =>
          (maximalGeodesic (I := I) g p (show TangentSpace I p from vt.1) vt.2 : M))
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

/-- The exponential map `expMap g p : T_p M → M` is continuous.

The proof reduces continuity to `ContinuousAt (expMap g p) v₀` for each `v₀`,
then restricts the joint continuity of the chained flow
`expMap_chainedFlow_joint_continuity` to the `t = 1` slice: since
`expMap g p v = maximalGeodesic g p v 1` by definitional unfolding of
`expMap`, continuity at `v₀` follows from the joint continuity on the
neighbourhood `ball v₀ ρ ×ˢ Icc 0 1`, precomposed with the continuous
slice map `v ↦ (v, 1)`. -/
theorem expMap_continuous
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨ρ, hρ, hjoint⟩ :=
    expMap_chainedFlow_joint_continuity (I := I) g p v₀
  set F : TangentSpace I p × ℝ → M :=
    fun vt => maximalGeodesic (I := I) g p vt.1 vt.2 with hF_def
  set s : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hs_def
  have hcomp_eq : expMap (I := I) g p = F ∘ s := by
    funext v
    simp only [Function.comp_apply, hF_def, hs_def, expMap]
  rw [hcomp_eq]
  have hs_cont : Continuous s := by
    rw [hs_def]; exact continuous_id.prodMk continuous_const
  have hs_maps : Set.MapsTo s (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    refine ⟨hv, ?_⟩
    exact ⟨zero_le_one, le_refl 1⟩
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hcw : ContinuousWithinAt (F ∘ s) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hjoint.comp hs_cont.continuousOn hs_maps
  exact hcw.continuousAt hball_nhds

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
