import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartTransition
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_apply_snd
    (q : TangentBundle I M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).2 =
      (trivializationAt E (TangentSpace I) q.proj).continuousLinearMapAt ℝ p.proj p.snd := by
  classical
  have hp_base : p.proj ∈ (trivializationAt E (TangentSpace I) q.proj).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have hcoe :=
    (trivializationAt E (TangentSpace I) q.proj).coe_linearMapAt_of_mem
      (R := ℝ) hp_base
  have hcoe_at :
      (trivializationAt E (TangentSpace I) q.proj).linearMapAt ℝ p.proj p.snd =
      (trivializationAt E (TangentSpace I) q.proj p).2 := by
    have h := congrFun hcoe p.snd
    exact h
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  change (trivializationAt E (TangentSpace I) q.proj p).2 = _
  rw [← hcoe_at]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_apply_fst
    (q : TangentBundle I M) {p : TangentBundle I M}
    (_hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).1 = extChartAt I q.proj p.proj := by
  classical
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  have hp1 : (trivializationAt E (TangentSpace I) q.proj p).1 = p.proj :=
    TangentBundle.trivializationAt_fst _ _
  rw [hp1]

end Exponential

namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartFiberCoord_eq_tangentCoordChange
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α p =
      tangentCoordChange I p.proj α p.proj (p.snd : E) := by
  classical
  unfold chartFiberCoord
  have hp_E_base : p.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  have hcoeE :=
    (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
      (R := ℝ) hp_E_base
  have hh : (trivializationAt E (TangentSpace I) α).linearMapAt ℝ p.proj p.snd =
      (trivializationAt E (TangentSpace I) α p).snd := by
    have := congrFun hcoeE p.snd
    exact this
  have hcore :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj =
        (tangentBundleCore I M).coordChange (achart H p.proj) (achart H α) p.proj :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
      (b₀ := α) (b := p.proj) hp
  have happ :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj :
        E → E) p.snd =
        tangentCoordChange I p.proj α p.proj p.snd := by
    rw [hcore]; rfl
  change (trivializationAt E (TangentSpace I) α p).snd = _
  rw [← hh]
  change ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj :
    E → E) p.snd = _
  rw [happ]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fst_continuousLinearMapAt_secondaryTriv
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p w).1 =
      tangentCoordChange I p.proj α p.proj w.1 := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_TM : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff]; exact hp
  have hcore2 :
      e.continuousLinearMapAt ℝ p =
        (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
          (achart (ModelProd H E) p)
          (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_TM
  have hcc :
      e.continuousLinearMapAt ℝ p =
        tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p :=
    hcore2
  have hp_src_p : p ∈ (extChartAt I.tangent p).source :=
    mem_extChartAt_source (I := I.tangent) p
  have hp_src_α0 : p ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hp_TM
  have hFTM :
      HasFDerivWithinAt
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
          (extChartAt I.tangent p).symm)
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p)
        (range I.tangent)
        ((extChartAt I.tangent p) p) :=
    hasFDerivWithinAt_tangentCoordChange (I := I.tangent) (M := TangentBundle I M)
      (x := p) (y := (⟨α, (0 : E)⟩ : TangentBundle I M)) (z := p)
      ⟨hp_src_p, hp_src_α0⟩
  set FTM : E × E → E × E :=
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
      (extChartAt I.tangent p).symm with hFTM_def
  set basepoint : E × E := (extChartAt I.tangent p) p with hbase_def
  have hFTM_fst :
      HasFDerivWithinAt (fun z : E × E => (FTM z).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hFTM.fst
  set FM : E → E :=
    (extChartAt I α) ∘ (extChartAt I p.proj).symm with hFM_def
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hproj_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  set U : Set (TangentBundle I M) :=
    (extChartAt I.tangent p).source ∩
      (Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source) with hU_def
  have hU_open : IsOpen U :=
    ((isOpen_extChartAt_source (I := I.tangent) p).inter (hα_open.preimage hproj_cont))
  have hU_mem : p ∈ U := by
    refine ⟨?_, ?_⟩
    · exact mem_extChartAt_source (I := I.tangent) p
    · simpa using hp
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hU_mem
  have hVnhds :
      (extChartAt I.tangent p) '' U ∈
        𝓝[range I.tangent] basepoint := by
    rw [hbase_def, ← map_extChartAt_nhds (I := I.tangent) p]
    exact Filter.image_mem_map hU_nhds
  have hfst_FTM_eq_FM :
      (fun z : E × E => (FTM z).1) =ᶠ[𝓝[range I.tangent] basepoint]
        (fun z : E × E => FM z.1) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(extChartAt I.tangent p) '' U, hVnhds, ?_⟩
    rintro z ⟨q, hqU, hqEq⟩
    have hq_src : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hsymm : (extChartAt I.tangent p).symm z = q := by
      rw [← hqEq]; exact (extChartAt I.tangent p).left_inv hq_src
    have hq_proj : q.proj ∈ (chartAt H α).source := hqU.2
    change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm z)).1 = FM z.1
    rw [hsymm]
    rw [extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := q) hq_proj]
    have hz1 : z.1 = extChartAt I p.proj q.proj := by
      rw [← hqEq]
      have hq_proj_src_p : q.proj ∈ (chartAt H p.proj).source := by
        have := hq_src
        rw [extChartAt_source] at this
        rw [TangentBundle.mem_chart_source_iff] at this
        exact this
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := q) hq_proj_src_p
    rw [hz1]
    change extChartAt I α q.proj =
      (extChartAt I α) ((extChartAt I p.proj).symm
        (extChartAt I p.proj q.proj))
    have hq_proj_src : q.proj ∈ (extChartAt I p.proj).source := by
      rw [extChartAt_source]
      have := hq_src
      rw [extChartAt_source] at this
      rw [TangentBundle.mem_chart_source_iff] at this
      exact this
    rw [(extChartAt I p.proj).left_inv hq_proj_src]
  have hfst_basepoint :
      (fun z : E × E => (FTM z).1) basepoint = (fun z : E × E => FM z.1) basepoint := by
    have hsymmp : (extChartAt I.tangent p).symm basepoint = p := by
      rw [hbase_def]
      exact (extChartAt I.tangent p).left_inv
        (mem_extChartAt_source (I := I.tangent) p)
    change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm basepoint)).1 = FM basepoint.1
    rw [hsymmp]
    rw [extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p) hp]
    have hbase_fst : basepoint.1 = extChartAt I p.proj p.proj := by
      rw [hbase_def]
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
        (mem_chart_source H p.proj)
    rw [hbase_fst]
    change extChartAt I α p.proj =
      (extChartAt I α) ((extChartAt I p.proj).symm
        (extChartAt I p.proj p.proj))
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
  have hFM_fst_FT :
      HasFDerivWithinAt (fun z : E × E => FM z.1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hFTM_fst.congr_of_eventuallyEq hfst_FTM_eq_FM hfst_basepoint
  have hp_E_src : p.proj ∈ (extChartAt I p.proj).source :=
    mem_extChartAt_source (I := I) p.proj
  have hp_E_src_α : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hp
  have hFM_hasD :
      HasFDerivWithinAt FM (tangentCoordChange I p.proj α p.proj)
        (range I) (extChartAt I p.proj p.proj) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (M := M)
      (x := p.proj) (y := α) (z := p.proj) ⟨hp_E_src, hp_E_src_α⟩
  have hfst_hasD :
      HasFDerivWithinAt (Prod.fst : E × E → E) (ContinuousLinearMap.fst ℝ E E)
        (range I.tangent) basepoint :=
    hasFDerivWithinAt_fst
  have hmaps : MapsTo (Prod.fst : E × E → E) (range I.tangent) (range I) := by
    intro x hx
    have hxr : x ∈ (range I) ×ˢ (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) := by
      have : range (I.tangent : ModelWithCorners ℝ (E × E) (ModelProd H E)) =
          range I ×ˢ range (𝓘(ℝ, E) : ModelWithCorners ℝ E E) :=
        ModelWithCorners.range_prod
      rw [← this]; exact hx
    exact hxr.1
  have hFM_comp_fst :
      HasFDerivWithinAt (FM ∘ (Prod.fst : E × E → E))
        ((tangentCoordChange I p.proj α p.proj).comp
          (ContinuousLinearMap.fst ℝ E E))
        (range I.tangent) basepoint := by
    have hbase_fst : basepoint.1 = extChartAt I p.proj p.proj := by
      rw [hbase_def]
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
        (mem_chart_source H p.proj)
    have hFM_at_basepoint :
        HasFDerivWithinAt FM (tangentCoordChange I p.proj α p.proj) (range I) basepoint.1 := by
      rw [hbase_fst]; exact hFM_hasD
    exact HasFDerivWithinAt.comp basepoint
      (g := FM) (f := (Prod.fst : E × E → E))
      (g' := tangentCoordChange I p.proj α p.proj)
      (f' := ContinuousLinearMap.fst ℝ E E)
      (s := range I.tangent) (t := range I)
      hFM_at_basepoint hfst_hasD hmaps
  have huniqueMD : UniqueDiffWithinAt ℝ (range I.tangent) basepoint :=
    ModelWithCorners.uniqueDiffWithinAt_image I.tangent
  have heq_clm :
      (ContinuousLinearMap.fst ℝ E E).comp
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) =
      (tangentCoordChange I p.proj α p.proj).comp
        (ContinuousLinearMap.fst ℝ E E) := by
    have h1 :
        HasFDerivWithinAt (FM ∘ (Prod.fst : E × E → E))
          ((ContinuousLinearMap.fst ℝ E E).comp
            (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
          (range I.tangent) basepoint := hFM_fst_FT
    exact huniqueMD.eq h1 hFM_comp_fst
  have hgoal :
      ((e.continuousLinearMapAt ℝ p) w).1 =
        tangentCoordChange I p.proj α p.proj w.1 := by
    rw [hcc]
    have := congrArg (· w) heq_clm
    have heq_app :
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w =
        ((tangentCoordChange I p.proj α p.proj).comp
          (ContinuousLinearMap.fst ℝ E E) :
            E × E →L[ℝ] E) w := by
      rw [heq_clm]
    change ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w = _
    rw [heq_app]
    rfl
  exact hgoal

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma extChartAt_tangent_apply_snd_tangentCoordChange
    (q : TangentBundle I M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).2 =
      tangentCoordChange I p.proj q.proj p.proj (p.snd : E) := by
  classical
  have hsnd := extChartAt_tangent_apply_snd (I := I) (q := q) (p := p) hp
  have hp_base : p.proj ∈ (trivializationAt E (TangentSpace I) q.proj).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  have hcoe :=
    (trivializationAt E (TangentSpace I) q.proj).coe_linearMapAt_of_mem (R := ℝ) hp_base
  have hCLM_eq_fiber :
      (trivializationAt E (TangentSpace I) q.proj).continuousLinearMapAt ℝ p.proj p.snd =
        chartFiberCoord (I := I) q.proj p := by
    change (trivializationAt E (TangentSpace I) q.proj).linearMapAt ℝ p.proj p.snd = _
    have := congrFun hcoe p.snd
    rw [this]
    rfl
  rw [hsnd, hCLM_eq_fiber]
  exact chartFiberCoord_eq_tangentCoordChange (I := I) (α := q.proj) (p := p) hp

def secondaryTrivFiberComponentMap (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  tangentCoordChange I p.proj α ((extChartAt I p.proj).symm z.1) z.2

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma snd_continuousLinearMapAt_secondaryTriv
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p w).2 =
      (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent)
        ((extChartAt I.tangent p) p)) w := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_TM : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff]; exact hp
  have hcc :
      e.continuousLinearMapAt ℝ p =
        tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_TM
  have hp_src_p : p ∈ (extChartAt I.tangent p).source :=
    mem_extChartAt_source (I := I.tangent) p
  have hp_src_α0 : p ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hp_TM
  set Ψ : E × E → E × E :=
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
      (extChartAt I.tangent p).symm with hΨ_def
  set basepoint : E × E := (extChartAt I.tangent p) p with hbase_def
  have hΨ :
      HasFDerivWithinAt Ψ
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p)
        (range I.tangent) basepoint :=
    hasFDerivWithinAt_tangentCoordChange (I := I.tangent) (M := TangentBundle I M)
      (x := p) (y := (⟨α, (0 : E)⟩ : TangentBundle I M)) (z := p)
      ⟨hp_src_p, hp_src_α0⟩
  have hΨ_snd :
      HasFDerivWithinAt (fun z : E × E => (Ψ z).2)
        ((ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hΨ.snd
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hproj_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  set U : Set (TangentBundle I M) :=
    (extChartAt I.tangent p).source ∩
      (Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source) with hU_def
  have hU_open : IsOpen U :=
    ((isOpen_extChartAt_source (I := I.tangent) p).inter (hα_open.preimage hproj_cont))
  have hU_mem : p ∈ U := by
    refine ⟨mem_extChartAt_source (I := I.tangent) p, ?_⟩
    simpa using hp
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hU_mem
  have hVnhds :
      (extChartAt I.tangent p) '' U ∈ 𝓝[range I.tangent] basepoint := by
    rw [hbase_def, ← map_extChartAt_nhds (I := I.tangent) p]
    exact Filter.image_mem_map hU_nhds
  have hpoint : ∀ {q : TangentBundle I M}, q ∈ U →
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) q).2 =
        secondaryTrivFiberComponentMap (I := I) α p ((extChartAt I.tangent p) q) := by
    intro q hqU
    have hq_src : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hq_proj_src_α : q.proj ∈ (chartAt H α).source := hqU.2
    have hq_proj_src_p : q.proj ∈ (chartAt H p.proj).source := by
      have := hq_src
      rw [extChartAt_source] at this
      rw [TangentBundle.mem_chart_source_iff] at this
      exact this
    have hLHS :
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) q).2 =
          tangentCoordChange I q.proj α q.proj (q.snd : E) :=
      extChartAt_tangent_apply_snd_tangentCoordChange (I := I)
        (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := q) hq_proj_src_α
    have hz1 : ((extChartAt I.tangent p) q).1 = extChartAt I p.proj q.proj :=
      extChartAt_tangent_apply_fst (I := I) (q := p) (p := q) hq_proj_src_p
    have hz2 : ((extChartAt I.tangent p) q).2 =
        tangentCoordChange I q.proj p.proj q.proj (q.snd : E) :=
      extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := q) hq_proj_src_p
    have hq_proj_ext_src : q.proj ∈ (extChartAt I p.proj).source := by
      rw [extChartAt_source]; exact hq_proj_src_p
    have hsymm_z1 :
        (extChartAt I p.proj).symm (((extChartAt I.tangent p) q).1) = q.proj := by
      rw [hz1]; exact (extChartAt I p.proj).left_inv hq_proj_ext_src
    have hq_proj_ext_src_α : q.proj ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hq_proj_src_α
    unfold secondaryTrivFiberComponentMap
    rw [hsymm_z1, hz2]
    have hq_proj_ext_src_self : q.proj ∈ (extChartAt I q.proj).source :=
      mem_extChartAt_source (I := I) q.proj
    rw [tangentCoordChange_comp (I := I) (w := q.proj) (x := p.proj) (y := α)
      (z := q.proj) (v := (q.snd : E))
      ⟨⟨hq_proj_ext_src_self, hq_proj_ext_src⟩, hq_proj_ext_src_α⟩]
    exact hLHS.symm
  have hsnd_Ψ_eq :
      (secondaryTrivFiberComponentMap (I := I) α p) =ᶠ[𝓝[range I.tangent] basepoint]
        (fun z : E × E => (Ψ z).2) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(extChartAt I.tangent p) '' U, hVnhds, ?_⟩
    rintro z ⟨q, hqU, hqEq⟩
    have hq_src : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hsymm : (extChartAt I.tangent p).symm z = q := by
      rw [← hqEq]; exact (extChartAt I.tangent p).left_inv hq_src
    change secondaryTrivFiberComponentMap (I := I) α p z =
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm z)).2
    rw [hsymm, ← hqEq]
    exact (hpoint hqU).symm
  have hsnd_basepoint :
      (secondaryTrivFiberComponentMap (I := I) α p) basepoint =
        (fun z : E × E => (Ψ z).2) basepoint := by
    have hsymmp : (extChartAt I.tangent p).symm basepoint = p := by
      rw [hbase_def]
      exact (extChartAt I.tangent p).left_inv
        (mem_extChartAt_source (I := I.tangent) p)
    change secondaryTrivFiberComponentMap (I := I) α p basepoint =
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm basepoint)).2
    rw [hsymmp, hbase_def]
    exact (hpoint hU_mem).symm
  have hform_hasD :
      HasFDerivWithinAt (secondaryTrivFiberComponentMap (I := I) α p)
        ((ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hΨ_snd.congr_of_eventuallyEq hsnd_Ψ_eq hsnd_basepoint
  have hfderivWithin_eq :
      fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) basepoint =
        (ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
    hform_hasD.fderivWithin (ModelWithCorners.uniqueDiffWithinAt_image I.tangent)
  rw [hcc]
  rw [hfderivWithin_eq]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_fst [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) := by
  classical
  have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
  have htriv := trivializationAt_apply_geodesicVectorFieldChart
    (I := I) g α (p := p) hp_dom
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_base : p ∈ e.baseSet := by
    rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]
    exact hp_dom
  have hcoe :=
    e.coe_linearMapAt_of_mem (R := ℝ) hp_base
  have hlin_at_gvf :
      (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
        geodesicVectorFieldChartFiber (I := I) g α p := by
    have h2 := congrArg Prod.snd htriv
    change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
    have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
    rw [hh]; exact h2
  have hfst_eq :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        (geodesicVectorFieldChartFiber (I := I) g α p).1 :=
    congrArg Prod.fst hlin_at_gvf
  have hLHS :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) :=
    fst_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
      (geodesicVectorFieldChart (I := I) g α p)
  have hRHS :
      (geodesicVectorFieldChartFiber (I := I) g α p).1 =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    change chartFiberCoord (I := I) α p = _
    exact chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp
  have hcc_eq :
      tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    rw [← hLHS, hfst_eq, hRHS]
  have hp_E_src : p.proj ∈ (extChartAt I p.proj).source :=
    mem_extChartAt_source (I := I) p.proj
  have hp_E_src_α : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hp
  have hself :
      tangentCoordChange I p.proj p.proj p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) =
        (geodesicVectorFieldChart (I := I) g α p : E × E).1 :=
    tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj)
      (v := (geodesicVectorFieldChart (I := I) g α p : E × E).1) hp_E_src
  have hself_snd :
      tangentCoordChange I p.proj p.proj p.proj (p.snd : E) = p.snd :=
    tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj)
      (v := p.snd) hp_E_src
  have h_comp1 :
      tangentCoordChange I α p.proj p.proj
          (tangentCoordChange I p.proj α p.proj
            ((geodesicVectorFieldChart (I := I) g α p : E × E).1)) =
        tangentCoordChange I p.proj p.proj p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) :=
    tangentCoordChange_comp (I := I) (w := p.proj) (x := α) (y := p.proj)
      (z := p.proj)
      (v := (geodesicVectorFieldChart (I := I) g α p : E × E).1)
      ⟨⟨hp_E_src, hp_E_src_α⟩, hp_E_src⟩
  have h_comp2 :
      tangentCoordChange I α p.proj p.proj
          (tangentCoordChange I p.proj α p.proj (p.snd : E)) =
        tangentCoordChange I p.proj p.proj p.proj (p.snd : E) :=
    tangentCoordChange_comp (I := I) (w := p.proj) (x := α) (y := p.proj)
      (z := p.proj) (v := p.snd) ⟨⟨hp_E_src, hp_E_src_α⟩, hp_E_src⟩
  have : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = p.snd := by
    rw [← hself]
    rw [← h_comp1]
    rw [hcc_eq]
    rw [h_comp2]
    exact hself_snd
  exact this

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (x y : M) (z : M) :
    tangentCoordChange I x y z =
      chartTransitionAt (I := I) x y (extChartAt I x z) := by
  rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

private def applyJac (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  chartTransitionAt (I := I) p.proj α z.1 z.2

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma secondaryTrivSndForm_eventuallyEq_applyJac [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    secondaryTrivFiberComponentMap (I := I) α p =ᶠ[𝓝 ((extChartAt I.tangent p) p)]
      applyJac (I := I) α p := by
  classical
  have hbp1 : ((extChartAt I.tangent p) p).1 = extChartAt I p.proj p.proj :=
    extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  set U : Set (E × E) :=
    {z : E × E | z.1 ∈ (extChartAt I p.proj).target ∧
      (extChartAt I p.proj).symm z.1 ∈ (chartAt H α).source} with hU_def
  have hUopen : IsOpen U := by
    have h1 : IsOpen ((extChartAt I p.proj).target) :=
      isOpen_extChartAt_target (I := I) p.proj
    have hcont : ContinuousOn (extChartAt I p.proj).symm (extChartAt I p.proj).target :=
      continuousOn_extChartAt_symm (I := I) p.proj
    have hset : U = (Prod.fst ⁻¹' (extChartAt I p.proj).target) ∩
        (Prod.fst ⁻¹' ((extChartAt I p.proj).target ∩
          (extChartAt I p.proj).symm ⁻¹' (chartAt H α).source)) := by
      ext z
      simp only [hU_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    rw [hset]
    refine (h1.preimage continuous_fst).inter ((IsOpen.preimage continuous_fst) ?_)
    exact hcont.isOpen_inter_preimage h1 (chartAt H α).open_source
  have hbp_memU : ((extChartAt I.tangent p) p) ∈ U := by
    rw [hU_def, Set.mem_setOf_eq, hbp1]
    refine ⟨(extChartAt I p.proj).map_source (mem_extChartAt_source (I := I) p.proj), ?_⟩
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
    exact hp
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hbp_memU) ?_
  intro z hz
  obtain ⟨hz_tgt, hz_src⟩ := hz
  unfold secondaryTrivFiberComponentMap applyJac
  rw [tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α ((extChartAt I p.proj).symm z.1)]
  congr 2
  exact (extChartAt I p.proj).right_inv hz_tgt

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma differentiableAt_chartTransitionAt [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) α β z) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hsmooth : ContDiffOn ℝ ∞ (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) :=
    chartTransitionAt_smooth (I := I) α β
  exact (hsmooth.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma fderiv_applyJac_apply [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    fderiv ℝ (applyJac (I := I) α p) ((extChartAt I.tangent p) p) w =
      chartTransitionAt (I := I) p.proj α ((extChartAt I.tangent p) p).1 w.2 +
        (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          ((extChartAt I.tangent p) p).1 w.1) (((extChartAt I.tangent p) p).2) := by
  classical
  set bp := (extChartAt I.tangent p) p with hbp
  have hbp1 : bp.1 = extChartAt I p.proj p.proj := by
    rw [hbp]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hx_src : bp.1 ∈ chartTransitionSource (I := I) p.proj α := by
    rw [hbp1]
    exact extChartAt_mem_chartTransitionSource (I := I) p.proj α
      (mem_chart_source H p.proj) hp
  set c : E × E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z.1 with hc
  set u : E × E → E := fun z => z.2 with hu
  have hcA : DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1 :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  have hc_diff : DifferentiableAt ℝ c bp :=
    hcA.comp bp (differentiableAt_fst)
  have hu_diff : DifferentiableAt ℝ u bp := differentiableAt_snd
  have hfd : fderiv ℝ (fun z => (c z) (u z)) bp =
      (c bp).comp (fderiv ℝ u bp) + (fderiv ℝ c bp).flip (u bp) :=
    fderiv_clm_apply hc_diff hu_diff
  have happly_eq : applyJac (I := I) α p = fun z => (c z) (u z) := by
    funext z; rfl
  rw [happly_eq, hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hu_fderiv : fderiv ℝ u bp = ContinuousLinearMap.snd ℝ E E := fderiv_snd
  rw [hu_fderiv]
  have hc_fderiv : fderiv ℝ c bp w =
      (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1) (w.1) := by
    have hceq : c = (fun x => chartTransitionAt (I := I) p.proj α x) ∘ Prod.fst := by
      funext z; rfl
    rw [hceq]
    rw [fderiv_comp bp hcA differentiableAt_fst]
    simp only [ContinuousLinearMap.comp_apply, fderiv_fst, ContinuousLinearMap.coe_fst']
  rw [hc_fderiv]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartCoord_fderiv_chartTransitionAt [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (c : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoord (E := E) c
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          (extChartAt I p.proj p.proj) v) v) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) p.proj α z c j)
          (extChartAt I p.proj p.proj) *
          chartCoord (E := E) i v * chartCoord (E := E) j v := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set A : E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z with hA
  have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
    extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
  have hcA : DifferentiableAt ℝ A x₀ :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_src
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord c) with hcoordCLM
  set eval : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp (ContinuousLinearMap.apply ℝ E v) with heval
  have hstep1 :
      chartCoord (E := E) c ((fderiv ℝ A x₀ v) v) = eval (fderiv ℝ A x₀ v) := by
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    rfl
  have hstep2 : eval (fderiv ℝ A x₀ v) = fderiv ℝ (fun z => eval (A z)) x₀ v := by
    have hcomp_hasD : HasFDerivAt (fun z => eval (A z))
        (eval.comp (fderiv ℝ A x₀)) x₀ :=
      eval.hasFDerivAt.comp x₀ hcA.hasFDerivAt
    rw [hcomp_hasD.fderiv]
    rfl
  have heval_eq : (fun z => eval (A z)) =
      (fun z => ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) := by
    funext z
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hA,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    change chartCoord (E := E) c (chartTransitionAt (I := I) p.proj α z v) = _
    exact chartCoord_chartTransitionAt (I := I) p.proj α z v c
  rw [hstep1, hstep2, heval_eq]
  have hsum_fderiv :
      fderiv ℝ (fun z => ∑ i : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) p.proj α z c i * chartCoord (E := E) i v) x₀ v =
        ∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v := by
    have hdiff : ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
          chartCoord (E := E) i v) x₀ := by
      intro i
      exact (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src).mul_const _
    rw [fderiv_fun_sum (fun i _ => hdiff i)]
    rw [ContinuousLinearMap.sum_apply]
  rw [hsum_fderiv]
  have hLHS_expand :
      (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) p.proj α z c i *
            chartCoord (E := E) i v) x₀ v) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) p.proj α z c i) x₀ *
            chartCoord (E := E) k v * chartCoord (E := E) i v := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_mul_const (chartTransitionJacEntry_differentiableAt (I := I) p.proj α c i hx_src) _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) p.proj α c i x₀ v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hLHS_expand]
  rw [Finset.sum_comm]

private theorem chart_eq_global_ne
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = geodesicVectorField (I := I) g p := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set bp := (extChartAt I.tangent p) p with hbp
  have hbp1 : bp.1 = x₀ := by
    rw [hbp, hx₀]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p) (mem_chart_source H p.proj)
  have hbp2 : bp.2 = (p.snd : E) := by
    rw [hbp]
    rw [extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := p)
      (mem_chart_source H p.proj)]
    exact tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj) (v := p.snd)
      (mem_extChartAt_source (I := I) p.proj)
  have hfst : (geodesicVectorFieldChart (I := I) g α p : E × E).1 =
      (geodesicVectorField (I := I) g p : E × E).1 := by
    rw [geodesicVectorFieldChart_fst (I := I) g α hp]
    rfl
  have hsnd : (geodesicVectorFieldChart (I := I) g α p : E × E).2 =
      (geodesicVectorField (I := I) g p : E × E).2 := by
    set X := (geodesicVectorFieldChart (I := I) g α p : E × E).2 with hX
    have hgvf1 : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) :=
      geodesicVectorFieldChart_fst (I := I) g α hp
    have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
    have htriv := trivializationAt_apply_geodesicVectorFieldChart
      (I := I) g α (p := p) hp_dom
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
    have hp_base : p ∈ e.baseSet := by
      rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp_dom
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hp_base
    have hlin_at_gvf :
        (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      have h2 := congrArg Prod.snd htriv
      change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
      have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
      rw [hh]; exact h2
    have hsnd_clm :
        ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).2 =
          (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
            (geodesicVectorFieldChart (I := I) g α p) :=
      snd_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
        (geodesicVectorFieldChart (I := I) g α p)
    have hkey0 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
          (geodesicVectorFieldChart (I := I) g α p) := by
      rw [← hsnd_clm, hlin_at_gvf]
    have hrangeT : (range (I.tangent) : Set (E × E)) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)
    have hfderiv_eq :
        fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp =
          fderiv ℝ (applyJac (I := I) α p) bp := by
      rw [hrangeT, fderivWithin_univ]
      exact Filter.EventuallyEq.fderiv_eq
        (secondaryTrivSndForm_eventuallyEq_applyJac (I := I) α hp)
    rw [hfderiv_eq] at hkey0
    have hfderiv_apply :
        fderiv ℝ (applyJac (I := I) α p) bp (geodesicVectorFieldChart (I := I) g α p) =
          chartTransitionAt (I := I) p.proj α x₀ X +
            (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀ (p.snd : E))
              (p.snd : E) := by
      have := fderiv_applyJac_apply (I := I) α hp (geodesicVectorFieldChart (I := I) g α p)
      rw [this, hbp1, hbp2, hgvf1]
    rw [hfderiv_apply] at hkey0
    set Dterm : E := (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀
      (p.snd : E)) (p.snd : E) with hDterm
    set v := chartFiberCoord (I := I) α p with hv
    have hfiber2 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        - chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj) := rfl
    rw [hfiber2] at hkey0
    have htransform :
        chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ =
          chartTransitionAt (I := I) α p.proj
              (chartTransitionMap (I := I) p.proj α x₀)
              (chartChristoffelContraction (I := I) g α
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionAt (I := I) p.proj α x₀ (p.snd))
                (chartTransitionMap (I := I) p.proj α x₀))
            + chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      have := chartChristoffelContraction_transform (I := I) g p.proj α
        (p := p.proj) (mem_chart_source H p.proj) hp (p.snd) (p.snd)
      rw [hx₀]; exact this
    have hTx₀ : chartTransitionMap (I := I) p.proj α x₀ = extChartAt I α p.proj := by
      rw [hx₀]
      exact chartTransitionMap_apply_extChartAt (I := I) p.proj α (mem_chart_source H p.proj)
    have hJsnd : chartTransitionAt (I := I) p.proj α x₀ (p.snd) = v := by
      rw [hv, hx₀, ← tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α p.proj]
      exact (chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp).symm
    rw [hTx₀, hJsnd] at htransform
    have hcorr :
        chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm =
          chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      refine (chartModelBasis E).ext_elem (fun k => ?_)
      change chartCoord (E := E) k
          (chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm) =
        chartCoord (E := E) k
          (chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀)
      rw [chartCoord_chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm k]
      rw [chartTransitionSecondDerivCorrection_def]
      rw [show chartCoord (E := E) k
          (∑ k' : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k' c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd))) •
              chartModelBasis E k') =
          ∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i
                    (fun z => chartTransitionJacEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i (p.snd) * chartCoord (E := E) j (p.snd)) from ?_]
      · rw [hTx₀]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hDterm, chartCoord_fderiv_chartTransitionAt (I := I) α hp c (p.snd)]
      · rw [chartCoord_def, map_sum, Finsupp.finset_sum_apply]
        rw [Finset.sum_eq_single k]
        · rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k,
            Finsupp.single_eq_same, smul_eq_mul, mul_one]
        · intro k' _ hk'
          rw [map_smul, Finsupp.smul_apply, (chartModelBasis E).repr_self k']
          rw [Finsupp.single_eq_of_ne (Ne.symm hk'), smul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
    have hx_src : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
      extChartAt_mem_chartTransitionSource (I := I) p.proj α (mem_chart_source H p.proj) hp
    have hinv : chartTransitionAt (I := I) α p.proj
        (chartTransitionMap (I := I) p.proj α x₀)
        (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) p.proj α hx_src
      have := congrArg (fun L : E →L[ℝ] E => L X) hcomp
      simpa using this
    set RJ : E →L[ℝ] E := chartTransitionAt (I := I) α p.proj
      (chartTransitionMap (I := I) p.proj α x₀) with hRJ
    have happ := congrArg (fun y => RJ y) hkey0
    simp only at happ
    rw [map_add] at happ
    have hRJ_X : RJ (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      rw [hRJ]; exact hinv
    rw [hRJ_X] at happ
    have hRJ_D : RJ Dterm =
        chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]; exact hcorr
    rw [hRJ_D] at happ
    rw [map_neg] at happ
    have hRJ_Gamma :
        RJ (chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj)) =
          chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ -
            chartTransitionSecondDerivCorrection (I := I) p.proj α (p.snd) (p.snd) x₀ := by
      rw [hRJ, hTx₀]
      rw [eq_sub_iff_add_eq]
      exact htransform.symm
    rw [hRJ_Gamma] at happ
    have hXval : X = - chartChristoffelContraction (I := I) g p.proj (p.snd) (p.snd) x₀ := by
      rw [neg_sub, sub_eq_neg_add] at happ
      exact (add_right_cancel happ).symm
    rw [hXval, geodesicVectorField_snd]
  apply Prod.ext hfst hsnd

omit [NeZero (Module.finrank ℝ E)] in
/-- The fixed-chart and global geodesic vector fields agree wherever the
fixed chart is defined. -/
theorem geodesicVectorFieldChart_eq_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorField (I := I) g p := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have hzero : ∀ x : E, x = 0 :=
      finrank_zero_iff_forall_zero.mp hdim
    letI : Subsingleton E :=
      ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    apply Prod.ext <;> exact Subsingleton.elim _ _
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact chart_eq_global_ne (I := I) g α hp

omit [NeZero (Module.finrank ℝ E)] in
/-- On a fixed chart domain, the chart and global geodesic vector fields have
the same integral curves. -/
theorem chart_vf_on_iff
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {K : Set ℝ}
    (hsrc : ∀ t ∈ K, (f t).proj ∈ (chartAt H α).source) :
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) K ↔
      IsMIntegralCurveOn f (geodesicVectorField (I := I) g) K := by
  constructor <;> intro hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht
  · simpa only [geodesicVectorFieldChart_eq_geodesicVectorField
      (I := I) g α (hsrc t ht)] using hf t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVF_smooth
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorField (I := I) g p⟩ :
          TangentBundle I.tangent (TangentBundle I M))) := by
  intro p
  let α : M := p.proj
  have hp : p.proj ∈ (chartAt H α).source := by
    simp [α]
  have hsmooth := geodesicVectorFieldChart_contMDiffAt (I := I) g α hp
  refine hsmooth.congr_of_eventuallyEq ?_
  have hnhds : geodesicChartDomain (I := I) α ∈ nhds p :=
    (geodesicChartDomain_isOpen (I := I) (M := M) α).mem_nhds hp
  filter_upwards [hnhds] with q hq
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq ((geodesicVectorFieldChart_eq_geodesicVectorField
    (I := I) g α hq).symm)

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
