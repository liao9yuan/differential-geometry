import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.GeodesicEquationBridge
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option linter.unusedSectionVars false

/-!
# Manifold derivative of the projection of an integral curve

For an integral curve `f : ℝ → TangentBundle I M` of the chart-fixed
geodesic vector field `geodesicVectorFieldChart g α` at a base time `t₀`,
the projection curve `γ t := (f t).proj` carries a manifold derivative at
`t₀` equal to the fibre vector `(f t₀).snd : TangentSpace I (f t₀).proj`.

This is the manifold-level "horizontal lift" identity: a curve in `T M`
whose tangent vector (in the secondary tangent bundle `T(T M)`) is the
canonical geodesic vector field projects to a base curve whose
manifold derivative is the fibre component of the lift.
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
open DifferentialGeometry.Geometry.Riemannian.Exponential

/-! ## Part A — chart-α fibre coordinate as a tangent coord change -/

/-- **`chartFiberCoord` as a `tangentCoordChange`.** When `p.proj` lies
in the chart-source at `α`, the chart-`α` fibre coordinate of `p : T M`
equals the tangent coordinate change of `p.snd` from the chart at
`p.proj` to the chart at `α`. -/
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

/-! ## Part B — first-component identity for the secondary trivialisation -/

/-- The first component of the secondary trivialisation's `continuousLinearMapAt`
at a `T M` point `p` with `p.proj ∈ chartAt H α source` equals
`tangentCoordChange I p.proj α p.proj ∘ Prod.fst`. This expresses the
block-triangular structure of the chart-transition fderiv on `T M`:
the base-chart change only sees the H-component. -/
lemma fst_continuousLinearMapAt_secondaryTriv
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p w).1 =
      tangentCoordChange I p.proj α p.proj w.1 := by
  classical
  -- Phase 1. Express `e.continuousLinearMapAt ℝ p` as `tangentCoordChange I.tangent p ⟨α,0⟩ p`
  -- (the secondary core coord change at p).
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
  -- The secondary core coord change is `tangentCoordChange I.tangent p ⟨α,0⟩ p`
  -- (a fderiv of the chart transition on T M).
  have hcc :
      e.continuousLinearMapAt ℝ p =
        tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p :=
    hcore2
  -- Phase 2. The chart transition's fderiv: hasFDerivWithinAt for it.
  have hp_src_p : p ∈ (extChartAt I.tangent p).source :=
    mem_extChartAt_source (I := I.tangent) p
  have hp_src_α0 : p ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hp_TM
  -- `hasFDerivWithinAt_tangentCoordChange` on the secondary tangent bundle
  -- gives the chart transition's fderiv.
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
  -- Phase 3. Take Prod.fst of `hFTM`: the .1-component of `FTM` has fderiv
  -- `(Prod.fst CLM).comp (tangentCoordChange ...)`.
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
  -- Phase 4. Show eventually `(FTM z).1 = FM z.1` on `range I.tangent` near basepoint,
  -- where `FM := extChartAt I α ∘ (extChartAt I p.proj).symm`. Use `extChartAt_tangent_apply_fst`.
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
  -- Pointwise basepoint check (needed for `congr_of_eventuallyEq`).
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
  -- Transfer the fderiv across the eventual equality.
  have hFM_fst_FT :
      HasFDerivWithinAt (fun z : E × E => FM z.1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hFTM_fst.congr_of_eventuallyEq hfst_FTM_eq_FM hfst_basepoint
  -- Phase 5. Independently compute the fderiv of `FM ∘ Prod.fst` via chain rule
  -- (base chart transition on `M`).
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
  -- `MapsTo Prod.fst (range I.tangent) (range I)`: since `range I.tangent = range I × univ`.
  have hmaps : MapsTo (Prod.fst : E × E → E) (range I.tangent) (range I) := by
    intro x hx
    -- range I.tangent = range (I.prod 𝓘(ℝ, E)) = range I ×ˢ range 𝓘(ℝ, E).
    have hxr : x ∈ (range I) ×ˢ (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) := by
      have : range (I.tangent : ModelWithCorners ℝ (E × E) (ModelProd H E)) =
          range I ×ˢ range (𝓘(ℝ, E) : ModelWithCorners ℝ E E) :=
        ModelWithCorners.range_prod
      rw [← this]; exact hx
    exact hxr.1
  -- Compose: `HasFDerivWithinAt (FM ∘ Prod.fst) (tangentCoordChange-fderiv ∘ fst CLM)
  -- (range I.tangent) basepoint`.
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
  -- Phase 6. Both `hFM_fst_FT` and `hFM_comp_fst` give fderivs of `FM ∘ Prod.fst`
  -- on `range I.tangent` at `basepoint`. By `UniqueDiffWithinAt`, they coincide.
  have huniqueMD : UniqueDiffWithinAt ℝ (range I.tangent) basepoint :=
    ModelWithCorners.uniqueDiffWithinAt_image I.tangent
  have heq_clm :
      (ContinuousLinearMap.fst ℝ E E).comp
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) =
      (tangentCoordChange I p.proj α p.proj).comp
        (ContinuousLinearMap.fst ℝ E E) := by
    -- Note: `FM ∘ Prod.fst = fun z => FM z.1` as functions; they're defeq.
    have h1 :
        HasFDerivWithinAt (FM ∘ (Prod.fst : E × E → E))
          ((ContinuousLinearMap.fst ℝ E E).comp
            (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
          (range I.tangent) basepoint := hFM_fst_FT
    exact huniqueMD.eq h1 hFM_comp_fst
  -- Phase 7. Apply the CLM equality to `w`. Combine with `hcc`.
  have hgoal :
      ((e.continuousLinearMapAt ℝ p) w).1 =
        tangentCoordChange I p.proj α p.proj w.1 := by
    rw [hcc]
    have := congrArg (· w) heq_clm
    -- `((Prod.fst CLM).comp (cc)) w = (tcc).comp (Prod.fst CLM) w`.
    -- LHS: `((cc w).1)`. RHS: `tcc w.1`.
    -- We extract the equality at w.
    have heq_app :
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w =
        ((tangentCoordChange I p.proj α p.proj).comp
          (ContinuousLinearMap.fst ℝ E E) :
            E × E →L[ℝ] E) w := by
      rw [heq_clm]
    -- Unpack the comp-applied formula on both sides.
    change ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w = _
    rw [heq_app]
    rfl
  exact hgoal

/-! ## Part C — first fibre component of the chart-fixed geodesic VF -/

/-- **First fibre component of the chart-fixed geodesic vector field.**
For a chart basepoint `α : M` and a tangent-bundle point `p : T M`
whose projection lies in the chart-source at `α`, the first component
(in the canonical `E × E` representation of `TangentSpace I.tangent p`)
of `geodesicVectorFieldChart g α p` equals the fibre vector `p.snd`. -/
theorem geodesicVectorFieldChart_fst [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) := by
  classical
  -- The triv-applied identity gives `e.continuousLinearMapAt ℝ p (gvfChart g α p) = gvfFiber g α p`.
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
  -- Take .1 of both sides.
  have hfst_eq :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        (geodesicVectorFieldChartFiber (I := I) g α p).1 :=
    congrArg Prod.fst hlin_at_gvf
  -- LHS = tangentCoordChange I p.proj α p.proj (gvfChart g α p).1 by Part B.
  have hLHS :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) :=
    fst_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
      (geodesicVectorFieldChart (I := I) g α p)
  -- RHS .1 = chartFiberCoord α p = tangentCoordChange I p.proj α p.proj p.snd by Part A.
  have hRHS :
      (geodesicVectorFieldChartFiber (I := I) g α p).1 =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    change chartFiberCoord (I := I) α p = _
    exact chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp
  -- Combine: tcc-image equal.
  have hcc_eq :
      tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    rw [← hLHS, hfst_eq, hRHS]
  -- Apply the inverse coord change `tangentCoordChange I α p.proj p.proj`.
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
  -- Apply `tangentCoordChange_comp` with w = p.proj, x = α, y = p.proj, z = p.proj.
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
  -- Conclude by chaining.
  have : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = p.snd := by
    rw [← hself]
    rw [← h_comp1]
    rw [hcc_eq]
    rw [h_comp2]
    exact hself_snd
  exact this

/-! ## Part D — main theorem -/

/-- **Manifold derivative of the projection of an integral curve.** For a
local integral curve `f : ℝ → TangentBundle I M` of the chart-fixed
geodesic vector field `geodesicVectorFieldChart g α` at base time `t₀`,
whose projection `(f t₀).proj` lies in the chart-source at `α`, the
manifold derivative of the projection curve `t ↦ (f t).proj`, evaluated
at `t₀ : ℝ` against the unit tangent vector `1 : ℝ`, equals the fibre
vector `(f t₀).snd : TangentSpace I (f t₀).proj`. -/
theorem IsMIntegralCurveAt.mfderiv_proj_one [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : ℝ → TangentBundle I M}
    {α : M} {t₀ : ℝ}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀)
    (hsrc : (f t₀).proj ∈ (chartAt H α).source) :
    mfderiv 𝓘(ℝ, ℝ) I (fun t => (f t).proj) t₀ (1 : ℝ) = (f t₀).snd := by
  classical
  -- Step 1. Chart-pushed HasDerivAt at `t₀`: derivative is `gvfChart g α (f t₀)`.
  have hpush :=
    chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α) (t₀ := t₀)
      (f := f) hf
  have hpush_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g α f t₀ t₀) t₀ := hpush.self_of_nhds
  have hpush_t₀' : HasDerivAt (chartPushLift (I := I) f t₀)
      (geodesicVectorFieldChart (I := I) g α (f t₀)) t₀ := by
    rw [← chartPushVF_self (I := I) g α f t₀]
    exact hpush_t₀
  -- Step 2. Take Prod.fst.
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
    hasFDerivAt_fst
  have hfst :
      HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
        ((geodesicVectorFieldChart (I := I) g α (f t₀) : E × E).1) t₀ :=
    hfst_clm.comp_hasDerivAt t₀ hpush_t₀'
  -- Step 3. Rewrite `(chartPushLift f t₀ t).1 = extChartAt I (f t₀).proj (f t).proj`.
  have hfun_eq :
      (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
        (fun t : ℝ => extChartAt I (f t₀).proj (f t).proj) := by
    funext t
    exact chartPushLift_fst_eq (I := I) (f := f) t₀ t
  rw [hfun_eq] at hfst
  -- Step 4. Replace `(gvfChart g α (f t₀)).1` with `(f t₀).snd`.
  have hfst_eq_snd : (geodesicVectorFieldChart (I := I) g α (f t₀) : E × E).1 =
      ((f t₀).snd : E) :=
    geodesicVectorFieldChart_fst (I := I) g α (p := f t₀) hsrc
  rw [hfst_eq_snd] at hfst
  -- Step 5. Convert to HasMFDerivAt 𝓘(ℝ,ℝ) I.
  -- γ := fun t => (f t).proj.
  set γ : ℝ → M := fun t => (f t).proj with hγ_def
  -- γ is continuous at t₀.
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hγ_cont : ContinuousAt γ t₀ :=
    hπ_cont.continuousAt.comp hf.continuousAt
  -- The chart on ℝ at t₀ is trivial: extChartAt 𝓘(ℝ,ℝ) t₀ = id.
  -- writtenInExtChartAt 𝓘(ℝ,ℝ) I t₀ γ = extChartAt I (γ t₀) ∘ γ ∘ id = extChartAt I (f t₀).proj ∘ γ.
  -- Convert HasDerivAt to HasFDerivAt.
  have hfd : HasFDerivAt (extChartAt I (f t₀).proj ∘ γ)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E))) t₀ :=
    hfst.hasFDerivAt
  -- HasFDerivWithinAt (range 𝓘(ℝ,ℝ) = univ).
  have hfdw : HasFDerivWithinAt (extChartAt I (f t₀).proj ∘ γ)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E)))
      (range 𝓘(ℝ, ℝ)) t₀ := by
    rw [ModelWithCorners.range_eq_univ]
    exact hfd.hasFDerivWithinAt
  -- Package as HasMFDerivAt.
  have hMF : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E)) := by
    refine ⟨hγ_cont, ?_⟩
    -- writtenInExtChartAt 𝓘(ℝ,ℝ) I t₀ γ = extChartAt I (γ t₀) ∘ γ ∘ (extChartAt 𝓘(ℝ,ℝ) t₀).symm
    --   = extChartAt I (f t₀).proj ∘ γ ∘ id = extChartAt I (f t₀).proj ∘ γ.
    -- And extChartAt 𝓘(ℝ,ℝ) t₀ t₀ = t₀.
    have hext_self : extChartAt 𝓘(ℝ, ℝ) t₀ t₀ = t₀ := by
      simp
    rw [hext_self]
    -- The writtenInExtChartAt unfolds.
    -- Goal: HasFDerivWithinAt (writtenInExtChartAt 𝓘(ℝ,ℝ) I t₀ γ) _ (range 𝓘(ℝ,ℝ)) t₀.
    have hrewrite :
        writtenInExtChartAt 𝓘(ℝ, ℝ) I t₀ γ = extChartAt I (f t₀).proj ∘ γ := by
      funext s
      simp [writtenInExtChartAt, hγ_def]
    rw [hrewrite]
    exact hfdw
  -- Step 6. Extract mfderiv: mfderiv γ t₀ = smulRight 1 (f t₀).snd.
  have hmfd : mfderiv 𝓘(ℝ, ℝ) I γ t₀ =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) := hMF.mfderiv
  -- Apply at 1.
  have happly : mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) (1 : ℝ) := by
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) hmfd
  -- smulRight (1) v 1 = v: `smulRight L v x = (L x) • v`.
  have hsr_apply :
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((f t₀).snd : E) (1 : ℝ) =
        ((f t₀).snd : E) := by
    rw [ContinuousLinearMap.smulRight_apply]; simp
  rw [happly]
  exact hsr_apply

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
