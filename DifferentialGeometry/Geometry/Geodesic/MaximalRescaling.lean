import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.UniformChartFlowBridge
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformUniqueness
import DifferentialGeometry.Geometry.Geodesic.GeodesicEquationFromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.AffineReparam
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.MaximalUniqueness
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

section ChartFiberCoordSelfApply

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartFiberCoord_mk_self (α : M) (v : E) :
    chartFiberCoord (I := I) α (⟨α, v⟩ : TangentBundle I M) = v := by
  classical
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

section ChartPushLiftAtZero

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushLift_zero_of_init
    {f : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M)) :
    chartPushLift (I := I) f 0 0 = (extChartAt I p p, v) := by
  classical
  rw [chartPushLift_self_pair (I := I) f 0]
  have hproj : (f 0).proj = p := by rw [hf0]
  have hfiber : chartFiberCoord (I := I) p (f 0) = v := by
    rw [hf0]; exact chartFiberCoord_mk_self (I := I) p v
  rw [hproj, hfiber]

end ChartPushLiftAtZero

section RescaledChartOrbit

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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
  have hcv_phase := chartPushLift_eventually_hasDerivAt_chartPhaseVF (I := I)
    (g := g) (α := p) (f := f_v) hf_v0_proj hf_v_int
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
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := chartPushLift (I := I) f_v 0) (s₀ := s) (a := a) hs

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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

section ChartCoordUniqueness

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
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

omit [NeZero (Module.finrank ℝ E)] in
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
  have hphase := chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF
    (I := I) (g := g) (p := p) (f_v := f_v) hf_v0_proj hf_v_int a
  have hf_v_cont : ContinuousAt f_v 0 := hf_v_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp_v : ContinuousAt (fun t => (f_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_v_cont
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hmul_cont_at0 : ContinuousAt (fun s : ℝ => a * s) 0 := hmul_cont.continuousAt
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
  have hpair : chartPushLift (I := I) f_v 0 (a * s) =
      (extChartAt I p (f_v (a * s)).proj,
        chartFiberCoord (I := I) p (f_v (a * s))) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f_v) (t₀ := 0) (t := a * s) ?_
    · rw [h_eq, hf_v_proj_at_0]
    · rw [hf_v_proj_at_0]; exact hssrc
  rw [hpair]
  refine ⟨?_, Set.mem_univ _⟩
  have h_target : extChartAt I p (f_v (a * s)).proj ∈ (extChartAt I p).target := by
    have h_src : (f_v (a * s)).proj ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hssrc
    exact (extChartAt I p).map_source h_src
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target

omit [NeZero (Module.finrank ℝ E)] in
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
  have hc_R0 : rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * 0)) =
      (extChartAt I p p, a • v) := rescaled_chartPushLift_at_zero (I := I) hf_v0 a
  have hc_av0 : chartPushLift (I := I) f_av 0 0 = (extChartAt I p p, a • v) :=
    chartPushLift_zero_of_init (I := I) hf_av0
  have hz₀_target : (extChartAt I p p, a • v) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_src : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact mem_chart_source H p
    have h_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hp_src
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  have hd_R := rescaled_chartPushLift_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_v := f_v) hf_v0 hf_v_int
  have hd_av := chartPushLift_av_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_av := f_av) hf_av0 hf_av_int
  exact chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := fun s : ℝ =>
        rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))
    (c₂ := chartPushLift (I := I) f_av 0) (z₀ := (extChartAt I p p, a • v))
    hz₀_target hc_R0 hc_av0 hd_R hd_av

end ChartCoordUniqueness

section ManifoldProjection

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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

omit [NeZero (Module.finrank ℝ E)] in
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
  have heq := chartPushLift_rescaled_eq_chartPushLift_av_eventually
    (I := I) (g := g) (p := p) (a := a) (v := v)
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
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
  have h_fst_eq : (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s))).1 =
      (chartPushLift (I := I) f_av 0 s).1 := by
    have := congrArg Prod.fst hs_eq
    exact this
  have hlhs := rescaled_chartPushLift_fst (I := I) (f_v := f_v) (p := p)
    (a := a) (s := s) hf_v0_proj hs_v
  have hrhs : (chartPushLift (I := I) f_av 0 s).1 =
      extChartAt I p (f_av s).proj := by
    have h := chartPushLift_fst (I := I) (f := f_av) 0 s ?_
    · rw [show (f_av 0).proj = p from hf_av0_proj] at h
      exact h
    · rw [hf_av0_proj]; exact hs_av
  rw [hlhs] at h_fst_eq
  rw [hrhs] at h_fst_eq
  have hv_src : projectCurve (I := I) f_v (a * s) ∈ (extChartAt I p).source := by
    rw [extChartAt_source, projectCurve_apply]; exact hs_v
  have hav_src : (f_av s).proj ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hs_av
  have hlhs_inv : (extChartAt I p).symm (extChartAt I p
      (projectCurve (I := I) f_v (a * s))) =
      projectCurve (I := I) f_v (a * s) :=
    (extChartAt I p).left_inv hv_src
  have hrhs_inv : (extChartAt I p).symm (extChartAt I p
      (f_av s).proj) = (f_av s).proj :=
    (extChartAt I p).left_inv hav_src
  have h_inv := congrArg (extChartAt I p).symm h_fst_eq
  rw [hlhs_inv, hrhs_inv] at h_inv
  change projectCurve (I := I) f_v (a * s) = projectCurve (I := I) f_av s
  rw [projectCurve_apply]
  exact h_inv

end ManifoldProjection

section ChosenCurveRescaling

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicChosenCurve_rescale_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v)) :
    (fun s : ℝ =>
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s))
      =ᶠ[𝓝 (0 : ℝ)] maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom := by
  classical
  obtain ⟨J_v, hJv_open, _hJv_conn, h0_Jv, _ha_Jv, hwit_v⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v ha_dom
  obtain ⟨J_av, hJav_open, _hJav_conn, h0_Jav, _h1_Jav, hwit_av⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (a • v) h1_dom
  obtain ⟨f_v, hproj_v, hf_v0, hf_v_int_on⟩ := hwit_v
  obtain ⟨f_av, hproj_av, hf_av0, hf_av_int_on⟩ := hwit_av
  have chart_at_zero :
      ∀ {w : E} {f : ℝ → TangentBundle I M} {J : Set ℝ},
        IsOpen J → (0 : ℝ) ∈ J →
        f 0 = (⟨p, w⟩ : TangentBundle I M) →
        IsMIntegralCurveOn f (geodesicVectorField (I := I) g) J →
        IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 := by
    intro w f J hJ_open h0J hf0 hf_on
    have hf_at : IsMIntegralCurveAt f (geodesicVectorField (I := I) g) 0 :=
      hf_on.isMIntegralCurveAt (hJ_open.mem_nhds h0J)
    have hproj_cont : ContinuousAt (fun t => (f t).proj) 0 :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hf_at.continuousAt
    have hsrc0 : (f 0).proj ∈ (chartAt H p).source := by
      rw [hf0]
      exact mem_chart_source H p
    have hsrc : (fun t => (f t).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) :=
      hproj_cont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc0)
    rw [isMIntegralCurveAt_iff]
    let K := J ∩ (fun t => (f t).proj) ⁻¹' (chartAt H p).source
    refine ⟨K, inter_mem (hJ_open.mem_nhds h0J) hsrc, ?_⟩
    apply (chart_vf_on_iff (I := I) (f := f) (K := K) g p (fun _ ht => ht.2)).mpr
    exact hf_on.mono inter_subset_left
  have hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    chart_at_zero hJv_open h0_Jv hf_v0 hf_v_int_on
  have hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    chart_at_zero hJav_open h0_Jav hf_av0 hf_av_int_on
  have hrescale := projectCurve_rescale_eventually (I := I)
    (g := g) (p := p) (a := a) (v := (v : E))
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
  filter_upwards [hrescale] with s hs
  rw [projectCurve_apply, projectCurve_apply] at hs
  rw [← hproj_v (a * s), ← hproj_av s]
  exact hs

end ChosenCurveRescaling

section RescaleAtOneSmallScale

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicChosenCurve_rescale_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom 1 =
      maximalGeodesicChosenCurve (I := I) g p v ha_dom a := by
  have h := h1_in
  simp only [Set.mem_setOf_eq, mul_one] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] in
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

omit [NeZero (Module.finrank ℝ E)] in
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

section GlobalRescaling

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
private theorem scaledLift_gvf
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorField (I := I) g) S)
    (c d : ℝ) :
    IsMIntegralCurveOn
      (fun s : ℝ =>
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      (geodesicVectorField (I := I) g) {s : ℝ | c * s + d ∈ S} := by
  classical
  intro s₀ hs₀
  let u₀ : ℝ := c * s₀ + d
  let α : M := (f u₀).proj
  let T : Set ℝ := S ∩ (fun t => (f t).proj) ⁻¹' (chartAt H α).source
  have hu₀S : u₀ ∈ S := hs₀
  have hu₀src : (f u₀).proj ∈ (chartAt H α).source := by
    simp only [α]
    exact mem_chart_source H (f u₀).proj
  have hproj_cont : ContinuousWithinAt (fun t => (f t).proj) S u₀ :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp_continuousWithinAt
      (hf.continuousWithinAt hu₀S)
  have hsrc_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝[S] u₀ :=
    hproj_cont.preimage_mem_nhdsWithin
      ((chartAt H α).open_source.mem_nhds hu₀src)
  have hT_nhds : T ∈ 𝓝[S] u₀ := by
    dsimp only [T]
    exact inter_mem self_mem_nhdsWithin hsrc_nhds
  have hTsrc : ∀ t ∈ T, (f t).proj ∈ (chartAt H α).source :=
    fun _ ht => ht.2
  have hf_chart :
      IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) T := by
    apply (chart_vf_on_iff (I := I) g α hTsrc).mpr
    exact hf.mono inter_subset_left
  have hscaled := scaledTangentLift_transport (I := I) g α hf_chart c d
  have hs₀T : c * s₀ + d ∈ T := by
    rw [show c * s₀ + d = u₀ from rfl]
    exact ⟨hu₀S, hu₀src⟩
  have hderiv := hscaled s₀ hs₀T
  have haff_cont : Continuous (fun s : ℝ => c * s + d) :=
    (continuous_const.mul continuous_id).add continuous_const
  have hpreT : {s : ℝ | c * s + d ∈ T} ∈ 𝓝[{s : ℝ | c * s + d ∈ S}] s₀ := by
    change (fun s : ℝ => c * s + d) ⁻¹' T ∈
      𝓝[(fun s : ℝ => c * s + d) ⁻¹' S] s₀
    exact haff_cont.continuousAt.continuousWithinAt.preimage_mem_nhdsWithin'' hT_nhds rfl
  have hderiv' := hderiv.mono_of_mem_nhdsWithin hpreT
  have hLsrc :
      ((⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ :
        TangentBundle I M)).proj ∈ (chartAt H α).source := by
    change (f u₀).proj ∈ (chartAt H α).source
    exact hu₀src
  simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
    (I := I) g α hLsrc] using hderiv'

omit [NeZero (Module.finrank ℝ E)] in
/-- Nonzero radial rescaling identifies a supported raw exponential value
with the corresponding point of the maximal geodesic. -/
theorem expMap_smul_max_ne
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {a : ℝ} (ha : a ≠ 0) (hav : a • v ∈ expDomain (I := I) g p) :
    a ∈ maximalGeodesicInterval (I := I) g p v ∧
      expMap (I := I) g p (a • v) = maximalGeodesic (I := I) g p v a := by
  classical
  have h1av : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v) := hav
  obtain ⟨γ, J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ := h1av
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  let γv : ℝ → M := fun s => γ (a⁻¹ * s)
  let fv : ℝ → TangentBundle I M := fun s =>
    (⟨(f (a⁻¹ * s)).proj, a⁻¹ • (f (a⁻¹ * s)).snd⟩ : TangentBundle I M)
  let Jv : Set ℝ := {s : ℝ | a⁻¹ * s ∈ J}
  have hJv_open : IsOpen Jv :=
    hJ_open.preimage (continuous_const.mul continuous_id)
  have hJv_conn : IsPreconnected Jv := by
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · exact (hJ_conn.ordConnected.preimage_anti
        (fun _ _ hst => mul_le_mul_of_nonpos_left hst (inv_nonpos.mpr ha_neg.le))).isPreconnected
    · exact (hJ_conn.ordConnected.preimage_mono
        (fun _ _ hst => mul_le_mul_of_nonneg_left hst (inv_nonneg.mpr ha_pos.le))).isPreconnected
  have h0Jv : (0 : ℝ) ∈ Jv := by
    change a⁻¹ * 0 ∈ J
    simpa only [mul_zero] using h0J
  have haJv : a ∈ Jv := by
    change a⁻¹ * a ∈ J
    simpa only [inv_mul_cancel₀ ha] using h1J
  have hfv_proj : ∀ s, (fv s).proj = γv s := by
    intro s
    change (f (a⁻¹ * s)).proj = γ (a⁻¹ * s)
    exact hproj (a⁻¹ * s)
  have hfv0 : fv 0 = (⟨p, v⟩ : TangentBundle I M) := by
    dsimp only [fv]
    rw [mul_zero]
    rw [hf0]
    refine TotalSpace.ext rfl ?_
    apply heq_of_eq
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hfv_on :
      IsMIntegralCurveOn fv (geodesicVectorField (I := I) g) Jv := by
    have hscaled := scaledLift_gvf (I := I) g hf_on a⁻¹ 0
    have hcurve :
        (fun s : ℝ =>
          (⟨(f (a⁻¹ * s + 0)).proj, a⁻¹ • (f (a⁻¹ * s + 0)).snd⟩ :
            TangentBundle I M)) = fv := by
      funext s
      dsimp only [fv]
      rw [add_zero]
    have hset : {s : ℝ | a⁻¹ * s + 0 ∈ J} = Jv := by
      ext s
      change (a⁻¹ * s + 0 ∈ J) ↔ (a⁻¹ * s ∈ J)
      rw [add_zero]
    rw [hcurve] at hscaled
    rw [hset] at hscaled
    exact hscaled
  have hγv : IsGeodesicOnWithInitial (I := I) g γv Jv p v :=
    ⟨fv, hfv_proj, hfv0, hfv_on⟩
  have hγav : IsGeodesicOnWithInitial (I := I) g γ J p (a • v) :=
    ⟨f, hproj, hf0, hf_on⟩
  have ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v :=
    ⟨γv, Jv, hJv_open, hJv_conn, h0Jv, haJv, hγv⟩
  have hEq_v := maximalGeo_eqOn (I := I) g hJv_open hJv_conn h0Jv hγv
  have hEq_av := maximalGeo_eqOn (I := I) g hJ_open hJ_conn h0J hγav
  have hmax_eq : maximalGeodesic (I := I) g p v a =
      maximalGeodesic (I := I) g p (a • v) 1 := by
    calc
      maximalGeodesic (I := I) g p v a = γv a := hEq_v haJv
      _ = γ 1 := by simp only [γv, inv_mul_cancel₀ ha]
      _ = maximalGeodesic (I := I) g p (a • v) 1 := (hEq_av h1J).symm
  refine ⟨ha_dom, ?_⟩
  rw [expMap_def]
  exact hmax_eq.symm

omit [NeZero (Module.finrank ℝ E)] in
/-- Positive radial rescaling identifies a supported raw exponential value
with the corresponding point of the maximal geodesic. -/
theorem expMap_smul_eq_max
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {a : ℝ} (ha : 0 < a) (hav : a • v ∈ expDomain (I := I) g p) :
    a ∈ maximalGeodesicInterval (I := I) g p v ∧
      expMap (I := I) g p (a • v) = maximalGeodesic (I := I) g p v a :=
  expMap_smul_max_ne (I := I) g p v ha.ne' hav

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
/-- The raw exponential domain is closed under radial contraction. -/
theorem smul_mem_expDomain
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (hv : v ∈ expDomain (I := I) g p)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • v ∈ expDomain (I := I) g p := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · simpa only [zero_smul] using zero_mem_expDomain (I := I) g p
  have h1v : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v := hv
  obtain ⟨γ, J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ := h1v
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  let γt : ℝ → M := fun s => γ (t * s)
  let ft : ℝ → TangentBundle I M := fun s =>
    (⟨(f (t * s)).proj, t • (f (t * s)).snd⟩ : TangentBundle I M)
  let Jt : Set ℝ := {s : ℝ | t * s ∈ J}
  have hJt_open : IsOpen Jt :=
    hJ_open.preimage (continuous_const.mul continuous_id)
  have hJt_conn : IsPreconnected Jt := by
    exact (hJ_conn.ordConnected.preimage_mono
      (fun _ _ hst => mul_le_mul_of_nonneg_left hst ht_pos.le)).isPreconnected
  have h0Jt : (0 : ℝ) ∈ Jt := by
    change t * 0 ∈ J
    simpa only [mul_zero] using h0J
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ J :=
    hJ_conn.ordConnected.out h0J h1J
  have h1Jt : (1 : ℝ) ∈ Jt := by
    change t * 1 ∈ J
    simpa only [mul_one] using hIcc ht
  have hft_proj : ∀ s, (ft s).proj = γt s := by
    intro s
    change (f (t * s)).proj = γ (t * s)
    exact hproj (t * s)
  have hft0 : ft 0 = (⟨p, t • v⟩ : TangentBundle I M) := by
    dsimp only [ft]
    rw [mul_zero, hf0]
  have hft_on :
      IsMIntegralCurveOn ft (geodesicVectorField (I := I) g) Jt := by
    have hscaled := scaledLift_gvf (I := I) g hf_on t 0
    have hcurve :
        (fun s : ℝ =>
          (⟨(f (t * s + 0)).proj, t • (f (t * s + 0)).snd⟩ :
            TangentBundle I M)) = ft := by
      funext s
      dsimp only [ft]
      rw [add_zero]
    have hset : {s : ℝ | t * s + 0 ∈ J} = Jt := by
      ext s
      change (t * s + 0 ∈ J) ↔ (t * s ∈ J)
      rw [add_zero]
    rw [hcurve] at hscaled
    rw [hset] at hscaled
    exact hscaled
  have hγt : IsGeodesicOnWithInitial (I := I) g γt Jt p (t • v) :=
    ⟨ft, hft_proj, hft0, hft_on⟩
  change (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (t • v)
  exact ⟨γt, Jt, hJt_open, hJt_conn, h0Jt, h1Jt, hγt⟩

omit [NeZero (Module.finrank ℝ E)] in
/-- One supported positive radial endpoint is realized by a prescribed-velocity
geodesic on an open preconnected interval containing the whole preceding segment. -/
theorem radialGeo_of_end
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {r : ℝ} (hr : 0 < r) (hr_exp : r • v ∈ expDomain (I := I) g p) :
    ∃ (γ : ℝ → M) (J : Set ℝ),
      IsOpen J ∧ IsPreconnected J ∧ Set.Icc (0 : ℝ) r ⊆ J ∧
        IsGeodesicOnWithInitial (I := I) g γ J p v ∧
        γ r = expMap (I := I) g p (r • v) := by
  have hr_scale := expMap_smul_eq_max (I := I) g p v hr hr_exp
  obtain ⟨γ, J, hJ_open, hJ_conn, h0J, hrJ, hγ⟩ := hr_scale.1
  have hIcc : Set.Icc (0 : ℝ) r ⊆ J :=
    hJ_conn.ordConnected.out h0J hrJ
  have hEq := maximalGeo_eqOn (I := I) g hJ_open hJ_conn h0J hγ
  refine ⟨γ, J, hJ_open, hJ_conn, hIcc, hγ, ?_⟩
  exact (hEq hrJ).symm.trans hr_scale.2.symm

omit [NeZero (Module.finrank ℝ E)] in
/-- Pointwise raw exponential support along a positive radial segment is
realized by one prescribed-velocity geodesic on a common open interval. -/
theorem radialGeo_of_dom
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {r : ℝ} (hr : 0 < r)
    (hdom : ∀ {t : ℝ}, 0 < t → t ≤ r → t • v ∈ expDomain (I := I) g p) :
    ∃ (γ : ℝ → M) (J : Set ℝ),
      IsOpen J ∧ IsPreconnected J ∧ Set.Icc (0 : ℝ) r ⊆ J ∧
        IsGeodesicOnWithInitial (I := I) g γ J p v ∧
        Set.EqOn γ (fun t => expMap (I := I) g p (t • v)) (Set.Icc 0 r) := by
  have hr_exp : r • v ∈ expDomain (I := I) g p := hdom hr le_rfl
  obtain ⟨γ, J, hJ_open, hJ_conn, hIcc, hγ, _hr_eq⟩ :=
    radialGeo_of_end (I := I) g p v hr hr_exp
  have h0J : (0 : ℝ) ∈ J := hIcc ⟨le_rfl, hr.le⟩
  have hEq := maximalGeo_eqOn (I := I) g hJ_open hJ_conn h0J hγ
  refine ⟨γ, J, hJ_open, hJ_conn, hIcc, hγ, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · change γ 0 = expMap (I := I) g p (0 • v)
    rw [zero_smul, expMap_zero (I := I), hγ.start_eq]
  · calc
      γ t = maximalGeodesic (I := I) g p v t := (hEq (hIcc ht)).symm
      _ = expMap (I := I) g p (t • v) :=
        (expMap_smul_eq_max (I := I) g p v ht_pos (hdom ht_pos ht.2)).2.symm

end GlobalRescaling

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
