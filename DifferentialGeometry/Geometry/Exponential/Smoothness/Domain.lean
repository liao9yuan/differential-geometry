import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Geodesic.MaximalUniqueness

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private lemma chartFiberCoord_mk_self (p : M) (v : E) :
    chartFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M) = v := by
  classical
  change (trivializationAt E (TangentSpace I) p
      (⟨p, v⟩ : TangentBundle I M)).2 = v
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_src : p ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hp_mem
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp_mem
  have hcore :
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p =
        (tangentBundleCore I M).coordChange (achart H p) (achart H p) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (𝕜 := ℝ) (b₀ := p) (b := p) hp_mem
  have hself : ∀ w : E, tangentCoordChange I p p p w = w :=
    fun w => tangentCoordChange_self (I := I) (x := p) (z := p) (v := w) hp_src
  have hcore_at :
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v = v := by
    rw [hcore]
    exact hself v
  have happly :
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v =
        (trivializationAt E (TangentSpace I) p
          (⟨p, v⟩ : TangentBundle I M)).2 := by
    change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ p) v = _
    have hcoe :=
      (trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
        (R := ℝ) hbase
    exact congrFun hcoe v
  rw [← happly, hcore_at]

omit [FiniteDimensional ℝ E] in
private lemma tangentFiber_contMDiff (p : M) :
    ContMDiff 𝓘(ℝ, E) I.tangent ∞
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
  let e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := by
    change p ∈ (trivializationAt E (TangentSpace I) p).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hpair : ContMDiff 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ∞
      (fun v : E => (p, v)) := contMDiff_const.prodMk contMDiff_id
  have hmaps : ∀ v : E, (p, v) ∈ e.target := by
    intro v
    rw [Bundle.Trivialization.target_eq]
    exact ⟨hp, Set.mem_univ _⟩
  have hsymm : ContMDiff 𝓘(ℝ, E) I.tangent ∞
      (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) := by
    apply contMDiffOn_univ.mp
    exact e.contMDiffOn_symm.comp hpair.contMDiffOn (fun v _ => hmaps v)
  have heq : (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) =
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
    funext v
    have hsrc : (⟨p, v⟩ : TangentBundle I M) ∈ e.source := by
      rw [e.mem_source]
      exact hp
    have heval :
        e.toOpenPartialHomeomorph (⟨p, v⟩ : TangentBundle I M) = (p, v) := by
      apply Prod.ext
      · rfl
      · exact chartFiberCoord_mk_self (I := I) p v
    rw [← heval]
    exact e.left_inv hsrc
  rw [← heq]
  exact hsymm

private theorem exists_expFlow_nhds
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    ∃ U : Set E, IsOpen U ∧ v ∈ U ∧
      ∃ F : E → M,
        ContMDiff 𝓘(ℝ, E) I ∞ F ∧
        (∀ w ∈ U, (show TangentSpace I p from w) ∈ expDomain (I := I) g p) ∧
        (∀ w ∈ U, expMap (I := I) g p (show TangentSpace I p from w) = F w) := by
  classical
  change MaximalGeodesicWitness (I := I) g p v 1 at hv
  obtain ⟨_γ, J, hJ_open, hJ_conn, h0J, h1J, f, _hproj, hf0, hf_on⟩ := hv
  obtain ⟨ε0, hε0_pos, hball0⟩ := Metric.isOpen_iff.mp hJ_open 0 h0J
  obtain ⟨ε1, hε1_pos, hball1⟩ := Metric.isOpen_iff.mp hJ_open 1 h1J
  let δ : ℝ := min ε0 ε1 / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ₀ : δ < ε0 := by
    dsimp [δ]
    have hmin : min ε0 ε1 ≤ ε0 := min_le_left _ _
    nlinarith
  have hδ₁ : δ < ε1 := by
    dsimp [δ]
    have hmin : min ε0 ε1 ≤ ε1 := min_le_right _ _
    nlinarith
  let c : ℝ := -δ
  let a : ℝ := -δ / 2
  let b : ℝ := 1 + δ / 2
  let d : ℝ := 1 + δ
  have hc_lt_a : c < a := by dsimp [c, a]; linarith
  have ha_lt_zero : a < 0 := by dsimp [a]; linarith
  have hone_lt_b : 1 < b := by dsimp [b]; linarith
  have hb_lt_d : b < d := by dsimp [b, d]; linarith
  have hcJ : c ∈ J := by
    apply hball0
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [c]
    rw [sub_zero, abs_neg, abs_of_nonneg hδ_pos.le]
    exact hδ₀
  have hdJ : d ∈ J := by
    apply hball1
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [d]
    rw [add_sub_cancel_left, abs_of_nonneg hδ_pos.le]
    exact hδ₁
  have hcdJ : Set.Icc c d ⊆ J := hJ_conn.ordConnected.out hcJ hdJ
  have h0cd : (0 : ℝ) ∈ Set.Ioo c d := by
    constructor <;> dsimp [c, d] <;> linarith
  have h0ab : (0 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> linarith
  have h1ab : (1 : ℝ) ∈ Set.Ioo a b := by
    constructor <;> linarith
  let K : Set (TangentBundle I M) := f '' Set.Icc c d
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn ((hf_on.mono hcdJ).continuousOn)
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_bump_nhds (I := I.tangent) hK
  change {q : TangentBundle I M | χ q = 1} ∈ 𝓝ˢ K at hχone
  obtain ⟨O, hO_open, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχone
  let X : (q : TangentBundle I M) → TangentSpace I.tangent q :=
    fun q => χ q • geodesicVectorField (I := I) g q
  have hX : ContMDiff I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    exact hχ.smul_section (geodesicVF_smooth (I := I) g)
  have hXc : IsCompact (tsupport X) := by
    simpa only [X] using hχc.smul_right
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hcomplete : ∀ q : TangentBundle I M,
      ∃ η : ℝ → TangentBundle I M, η 0 = q ∧ IsMIntegralCurve η X :=
    exists_globalIntegralCurve_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I.tangent) I.tangent ∞
      (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) :=
    contMDiff_globalFlow_joint_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  have hf_X : IsMIntegralCurveOn f X (Set.Ioo c d) := by
    have hf_g := hf_on.mono (Set.Ioo_subset_Icc_self.trans hcdJ)
    intro t ht
    have hftK : f t ∈ K := ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
    have hχt : χ (f t) = 1 := hOχ (hKO hftK)
    simpa only [X, hχt, one_smul] using hf_g t ht
  let q₀ : TangentBundle I M := ⟨p, v⟩
  have hcut_eq : Set.EqOn (curveAt X hcomplete q₀) f (Set.Ioo c d) := by
    apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := (0 : ℝ)) h0cd (hX.of_le (by norm_num))
      ((curveAt_integralCurve X hcomplete q₀).isMIntegralCurveOn (Set.Ioo c d)) hf_X
    rw [curveAt_zero, hf0]
  let S : Set (ℝ × TangentBundle I M) :=
    (fun z : ℝ × TangentBundle I M => curveAt X hcomplete z.2 z.1) ⁻¹' O
  have hS_open : IsOpen S := hO_open.preimage hflow.continuous
  have hslice : Set.Icc a b ×ˢ ({q₀} : Set (TangentBundle I M)) ⊆ S := by
    rintro ⟨t, q⟩ ⟨ht, rfl⟩
    have htcd : t ∈ Set.Ioo c d := ⟨lt_of_lt_of_le hc_lt_a ht.1,
      lt_of_le_of_lt ht.2 hb_lt_d⟩
    exact hKO ⟨t, ⟨le_of_lt htcd.1, le_of_lt htcd.2⟩, (hcut_eq htcd).symm⟩
  obtain ⟨W, U₀, _hW_open, hU₀_open, hIccW, hq₀U, hWU⟩ :=
    generalized_tube_lemma (isCompact_Icc : IsCompact (Set.Icc a b))
      (isCompact_singleton : IsCompact ({q₀} : Set (TangentBundle I M))) hS_open hslice
  have hq₀U' : q₀ ∈ U₀ := hq₀U rfl
  let U : Set E := (fun w : E => (⟨p, w⟩ : TangentBundle I M)) ⁻¹' U₀
  have hU_open : IsOpen U := hU₀_open.preimage (tangentFiber_contMDiff (I := I) p).continuous
  have hvU : v ∈ U := by
    change q₀ ∈ U₀
    exact hq₀U'
  let F : E → M := fun w => (curveAt X hcomplete
    (⟨p, w⟩ : TangentBundle I M) 1).proj
  have hF : ContMDiff 𝓘(ℝ, E) I ∞ F := by
    have hlaunch : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod I.tangent) ∞
        (fun w : E => ((1 : ℝ), (⟨p, w⟩ : TangentBundle I M))) :=
      contMDiff_const.prodMk (tangentFiber_contMDiff (I := I) p)
    have hlift : ContMDiff 𝓘(ℝ, E) I.tangent ∞
        (fun w : E => curveAt X hcomplete
          (⟨p, w⟩ : TangentBundle I M) 1) := by
      simpa only using hflow.comp hlaunch
    exact (contMDiff_proj (TangentSpace I)).comp hlift
  have hnear (w : E) (hw : w ∈ U) :
      (show TangentSpace I p from w) ∈ expDomain (I := I) g p ∧
        expMap (I := I) g p (show TangentSpace I p from w) = F w := by
    let q : TangentBundle I M := ⟨p, w⟩
    let η : ℝ → TangentBundle I M := curveAt X hcomplete q
    have hη_g : IsMIntegralCurveOn η (geodesicVectorField (I := I) g)
        (Set.Ioo a b) := by
      intro t ht
      have hflowO : curveAt X hcomplete q t ∈ O := by
        have hpair : (t, q) ∈ W ×ˢ U₀ :=
          ⟨hIccW ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hw⟩
        exact hWU hpair
      have hχt : χ (η t) = 1 := hOχ hflowO
      have hder := (curveAt_integralCurve X hcomplete q).isMIntegralCurveOn
        (Set.Ioo a b) t ht
      simpa only [η, X, hχt, one_smul] using hder
    have hgeo : IsGeodesicOnWithInitial (I := I) g
        (projectCurve (I := I) η) (Set.Ioo a b) p w := by
      refine ⟨η, (fun _ => rfl), ?_, hη_g⟩
      simp only [η, q, curveAt_zero]
    have hwdom : (show TangentSpace I p from w) ∈ expDomain (I := I) g p := by
      change MaximalGeodesicWitness (I := I) g p w 1
      exact ⟨projectCurve (I := I) η, Set.Ioo a b, isOpen_Ioo,
        isPreconnected_Ioo, h0ab, h1ab, hgeo⟩
    have heq := maximalGeo_eqOn (I := I) g isOpen_Ioo isPreconnected_Ioo h0ab hgeo
    refine ⟨hwdom, ?_⟩
    simpa only [expMap_def, F, projectCurve_apply, η, q] using heq h1ab
  exact ⟨U, hU_open, hvU, F, hF, (fun w hw => (hnear w hw).1),
    (fun w hw => (hnear w hw).2)⟩

/-- The raw exponential map is smooth at every velocity for which its maximal
geodesic is defined at time one. -/
theorem expMap_contMDiffAt
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w)) v := by
  obtain ⟨U, hU_open, hvU, F, hF, _hdom, heq⟩ :=
    exists_expFlow_nhds (I := I) g p hv
  have heq_ev :
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w)) =ᶠ[𝓝 v] F :=
    Filter.eventuallyEq_of_mem (hU_open.mem_nhds hvU) (fun w hw => heq w hw)
  exact hF.contMDiffAt.congr_of_eventuallyEq heq_ev

/-- The raw exponential domain at a fixed base point is open. -/
theorem isOpen_expDomain
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (expDomain (I := I) g p) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  obtain ⟨U, hU_open, hvU, _F, _hF, hdom, _heq⟩ :=
    exists_expFlow_nhds (I := I) g p hv
  exact Filter.mem_of_superset (hU_open.mem_nhds hvU) hdom

/-- The raw exponential map is smooth on its maximal time-one domain. -/
theorem expMap_contMDiffOn
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun w : E => expMap (I := I) g p (show TangentSpace I p from w))
      (expDomain (I := I) g p) :=
  fun _ hv => (expMap_contMDiffAt (I := I) g p hv).contMDiffWithinAt

/-- A raw radial exponential curve supported on a compact time segment has a
global smooth extension with the same germ at every time in that segment. -/
theorem exists_raw_ray_ext
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    {L : ℝ} (hL : 0 < L)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p) :
    ∃ γg : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γg ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L, γg =ᶠ[𝓝 t]
        (fun s : ℝ => expMap (I := I) g p
          (show TangentSpace I p from s • u)) := by
  let U : Set ℝ := {t | (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p}
  have hU : IsOpen U :=
    (isOpen_expDomain (I := I) g p).preimage (continuous_id.smul continuous_const)
  have hseg : Set.Icc (0 : ℝ) L ⊆ U := fun t ht => hdom t ht
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hU hseg
  let a : ℝ := -(margin / 2)
  let d : ℝ := L + margin / 2
  let eps : ℝ := margin / 4
  have ha0 : a < 0 := by dsimp only [a]; linarith
  have hLd : L < d := by dsimp only [d]; linarith
  have had : a < d := lt_trans ha0 (hL.trans hLd)
  have heps : 0 < eps := by dsimp only [eps]; linarith
  obtain ⟨ρ, hρ, hρ_id, _hρ_deriv, hρ_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  have hρU : ∀ s : ℝ, ρ s ∈ U := by
    intro s
    apply hbuffer
    by_cases hs0 : ρ s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (ρ s) 0 margin
        (Set.Icc (0 : ℝ) L) ⟨le_rfl, hL.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      have hlo := (hρ_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsL : ρ s ≤ L
      · refine Metric.mem_cthickening_of_dist_le (ρ s) (ρ s) margin
          (Set.Icc (0 : ℝ) L) ⟨(not_le.mp hs0).le, hsL⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (ρ s) L margin
          (Set.Icc (0 : ℝ) L) ⟨hL.le, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsL).le)]
        have hhi := (hρ_range s).2
        dsimp only [d, eps] at hhi
        linarith
  have hρMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρ
  let γg : ℝ → M := fun s =>
    expMap (I := I) g p (show TangentSpace I p from ρ s • u)
  have hγg : ContMDiff 𝓘(ℝ, ℝ) I ∞ γg := by
    exact (expMap_contMDiffOn (I := I) g p).comp_contMDiff
      (hρMD.smul contMDiff_const) hρU
  refine ⟨γg, hγg, ?_⟩
  intro t ht
  have hIoo : Set.Ioo a d ∈ 𝓝 t :=
    Ioo_mem_nhds (lt_of_lt_of_le ha0 ht.1) (lt_of_le_of_lt ht.2 hLd)
  filter_upwards [hIoo] with s hs
  change expMap (I := I) g p (show TangentSpace I p from ρ s • u) =
    expMap (I := I) g p (show TangentSpace I p from s • u)
  rw [hρ_id s ⟨hs.1.le, hs.2.le⟩]

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
