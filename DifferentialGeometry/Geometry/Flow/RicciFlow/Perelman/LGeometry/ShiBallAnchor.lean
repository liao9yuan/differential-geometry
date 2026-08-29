import DifferentialGeometry.Analysis.ODE.TubeStability
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.RicciFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.RicciBound

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [FiniteDimensional Real E] [T2Space M] [SigmaCompactSpace M] in
private theorem arcLength_mono
    (g : SmoothRiemannianMetric I M) {gamma : Real → M} {u : Real}
    (hu : u ∈ Set.Icc (0 : Real) 1)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma) :
    Variation.arcLength (I := I) g gamma 0 u ≤
      Variation.arcLength (I := I) g gamma 0 1 := by
  unfold Variation.arcLength
  apply intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
  · filter_upwards with s
    exact Real.sqrt_nonneg _
  · exact
      MeasureTheory.IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le zero_le_one] using
          Geodesic.speedSqrt_integrableOn_Icc_of_C1
            (I := I) g zero_le_one hgamma.contMDiffOn)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem arcLength_contOn
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {a b t : Real} (hab : a ≤ b)
    (hcar : Set.Icc 0 t ⊆ D.carrier)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma) :
    ContinuousOn
      (fun s ↦ Variation.arcLength
        (I := I) (S.base.metric s) gamma a b)
      (Set.Icc 0 t) := by
  classical
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let F : Real × Real → Real := fun q ↦
    Real.sqrt ((S.base.metric q.1).inner (gamma q.2) (v q.2) (v q.2))
  let K : Set (Real × Real) := Set.Icc 0 t ×ˢ Set.Icc a b
  have hvLift : Continuous (fun u : Real ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hFcont : ContinuousOn F K := by
    rw [continuousOn_iff_continuous_restrict]
    have htime : Continuous (fun q : ↥K ↦ ((q : Real × Real).1)) :=
      continuous_fst.comp continuous_subtype_val
    have hparam : Continuous (fun q : ↥K ↦ ((q : Real × Real).2)) :=
      continuous_snd.comp continuous_subtype_val
    have hbase : Continuous (fun q : ↥K ↦ gamma ((q : Real × Real).2)) :=
      hgamma.continuous.comp hparam
    have hvec : ∀ _i : Fin 2, Continuous (fun q : ↥K ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma ((q : Real × Real).2)) (v ((q : Real × Real).2))) :=
      fun _i ↦ hvLift.comp hparam
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥K)
        (τ := fun q ↦ ((q : Real × Real).1))
        (b := fun q ↦ gamma ((q : Real × Real).2))
        htime (fun q ↦ hcar q.2.1) hbase
        (v := fun _i q ↦ v ((q : Real × Real).2)) hvec
    exact (Real.continuous_sqrt.comp heval).congr (fun q ↦ by
      change Real.sqrt _ = Real.sqrt
        ((S.base.metric ((q : Real × Real).1)).inner
          (gamma ((q : Real × Real).2))
          (v ((q : Real × Real).2)) (v ((q : Real × Real).2)))
      dsimp only
      rw [Tensor0SBundle.metricTensorField_apply]
      rfl)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFcont
  intro s hs
  unfold Variation.arcLength
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun r u ↦ F (r, u)) (bound := fun _ ↦ C)
      (s := Set.Icc 0 t)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((hFcont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu ↦ ⟨hr, by
        simpa only [uIcc_of_le hab] using
          uIoc_subset_uIcc hu⟩))).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with r hr using
      MeasureTheory.ae_of_all _ (fun u hu ↦ by
        exact hC (r, u) ⟨hr, by
          simpa only [uIcc_of_le hab] using
            uIoc_subset_uIcc hu⟩)
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_of_all _ fun u hu ↦ by
      have huIcc : u ∈ Set.Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hu
      have hpair : ContinuousWithinAt (fun r : Real ↦ (r, u))
          (Set.Icc 0 t) s :=
        continuousWithinAt_id.prodMk continuousWithinAt_const
      have hmaps : MapsTo (fun r : Real ↦ (r, u))
          (Set.Icc 0 t) K := fun r hr ↦ ⟨hr, huIcc⟩
      simpa only [Function.comp_apply] using
        (hFcont (s, u) ⟨hs, huIcc⟩).comp
          (f := fun r : Real ↦ (r, u)) (x := s) hpair hmaps

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem no_first_exit
    {f : Real → Real} {t R : Real}
    (ht : 0 < t) (hR : f t < R)
    (hcont : ContinuousOn f (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ioo 0 t, f s ≤ R →
      DifferentiableAt Real f s ∧ 0 ≤ deriv f s) :
    ∀ s ∈ Set.Icc 0 t, f s < R := by
  intro s hs
  by_contra hnot
  have hbad : R ≤ f s := le_of_not_gt hnot
  let g : Real → Real := fun q ↦ f (t - q)
  have hgcont : ContinuousOn g (Set.Icc 0 t) := by
    apply hcont.comp
      (continuous_const.sub continuous_id).continuousOn
    intro q hq
    exact ⟨sub_nonneg.mpr hq.2, sub_le_self t hq.1⟩
  have hg0 : g 0 < R := by
    simpa only [g, sub_zero] using hR
  have hcross : ∃ q ∈ Set.Icc 0 t, R ≤ g q := by
    refine ⟨t - s, ⟨sub_nonneg.mpr hs.2, sub_le_iff_le_add.mpr ?_⟩, ?_⟩
    · linarith [hs.1]
    · simpa only [g, sub_sub_cancel] using hbad
  obtain ⟨q, hq, hqeq, hqbelow⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc
      ht.le hgcont hg0 hcross
  have htail : ∀ r ∈ Set.Icc (t - q) t, f r ≤ R := by
    intro r hr
    have htr : t - r ∈ Set.Icc 0 q := by
      exact ⟨sub_nonneg.mpr hr.2, sub_le_iff_le_add.mpr (by linarith [hr.1])⟩
    simpa only [g, sub_sub_cancel] using hqbelow (t - r) htr
  have hmono : MonotoneOn f (Set.Icc (t - q) t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (t - q) t)
    · exact hcont.mono (fun r hr ↦
        ⟨le_trans (sub_nonneg.mpr hq.2) hr.1, hr.2⟩)
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := by
        have hleft : 0 ≤ t - q := sub_nonneg.mpr hq.2
        exact hleft.trans_lt hr.1
      exact (hderiv r ⟨hr0, hr.2⟩
        (htail r ⟨hr.1.le, hr.2.le⟩)).1.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := by
        exact (sub_nonneg.mpr hq.2).trans_lt hr.1
      exact (hderiv r ⟨hr0, hr.2⟩
        (htail r ⟨hr.1.le, hr.2.le⟩)).2
  have hleftmem : t - q ∈ Set.Icc (t - q) t :=
    ⟨le_rfl, sub_le_self t hq.1⟩
  have htmem : t ∈ Set.Icc (t - q) t :=
    ⟨sub_le_self t hq.1, le_rfl⟩
  have hle : f (t - q) ≤ f t := hmono hleftmem htmem hleftmem.2
  have hleft_eq : f (t - q) = R := by
    simpa only [g, sub_sub_cancel] using hqeq
  rw [hleft_eq] at hle
  exact (not_le_of_gt hR) hle

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem no_last_exit
    {f : Real → Real} {t R : Real}
    (ht : 0 < t) (hR : f 0 < R)
    (hcont : ContinuousOn f (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ioo 0 t, f s ≤ R →
      DifferentiableAt Real f s ∧ deriv f s ≤ 0) :
    ∀ s ∈ Set.Icc 0 t, f s < R := by
  intro s hs
  by_contra hnot
  have hcross : ∃ q ∈ Set.Icc 0 t, R ≤ f q :=
    ⟨s, hs, le_of_not_gt hnot⟩
  obtain ⟨q, hq, hqeq, hqbelow⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc
      ht.le hcont hR hcross
  have hmono : AntitoneOn f (Set.Icc 0 q) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) q)
    · exact hcont.mono (fun r hr ↦
        ⟨hr.1, hr.2.trans hq.2⟩)
    · intro r hr
      rw [interior_Icc] at hr
      exact (hderiv r ⟨hr.1, hr.2.trans_le hq.2⟩
        (hqbelow r ⟨hr.1.le, hr.2.le⟩)).1.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hderiv r ⟨hr.1, hr.2.trans_le hq.2⟩
        (hqbelow r ⟨hr.1.le, hr.2.le⟩)).2
  have hqle : f q ≤ f 0 :=
    hmono (left_mem_Icc.mpr hq.1) (right_mem_Icc.mpr hq.1) hq.1
  rw [hqeq] at hqle
  exact (not_le_of_gt hR) hqle

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem pathLength_deriv_le
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {a b t A : Real}
    (hab : a ≤ b)
    (ht : t ∈ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hvel : ∀ u ∈ Set.Icc a b,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0)
    (hRic : ∀ u ∈ Set.Icc a b,
      |ricciTensor (I := I) (S.base.metric t) (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))| ≤
        A * (S.base.metric t).inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) :
    deriv
        (fun s ↦ Variation.arcLength
          (I := I) (S.base.metric s) gamma a b) t ≤
      A * Variation.arcLength
        (I := I) (S.base.metric t) gamma a b := by
  classical
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let G : Real → Real :=
    fun u ↦ (S.base.metric t).inner (gamma u) (v u) (v u)
  let Ric : Real → Real :=
    fun u ↦ ricciTensor (I := I) (S.base.metric t) (gamma u) (v u) (v u)
  let Q : Real → Real := fun u ↦ -Ric u / Real.sqrt (G u)
  have hvLift : Continuous (fun u : Real ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hGcont : ContinuousOn G (Set.Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Set.Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Set.Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥(Set.Icc a b))
        (τ := fun _u ↦ t)
        (b := fun u ↦ gamma (u : Real))
        continuous_const
        (fun _u ↦ D.regular_subset ht)
        hbase
        (v := fun _i u ↦ v (u : Real))
        hvec
    refine heval.congr (fun u ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtCont :
      ContinuousOn
        (fun u ↦ S.ricciAt t (gamma u) (vec2 (I := I) (v u) (v u)))
        (Set.Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    have hbase : Continuous (fun u : ↥(Set.Icc a b) ↦ gamma (u : Real)) :=
      hgamma.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Set.Icc a b) ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma (u : Real)) (v (u : Real))) :=
      fun _i ↦ hvLift.comp continuous_subtype_val
    have heval := hS.ricciCont.eval_continuous
      (P := ↥(Set.Icc a b))
      (τ := fun _u ↦ t)
      (b := fun u ↦ gamma (u : Real))
      continuous_const
      (fun _u ↦ D.regular_subset ht)
      hbase
      (v := fun _i u ↦ v (u : Real)) hvec
    refine heval.congr (fun u ↦ ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (fun _i : Fin 2 ↦ v (u : Real)) =
        metricRicciAt (I := I) (S.base.metric t) (gamma (u : Real))
          (vec2 (I := I) (v (u : Real)) (v (u : Real)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicCont : ContinuousOn Ric (Set.Icc a b) := by
    refine hRicAtCont.congr (fun u _hu ↦ ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric t) (gamma u) (v u) (v u)).symm
  have hspeedCont : ContinuousOn (fun u ↦ Real.sqrt (G u)) (Set.Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hGcont
  have hQcont : ContinuousOn Q (Set.Icc a b) := by
    change ContinuousOn (fun u ↦ -Ric u / Real.sqrt (G u)) (Set.Icc a b)
    apply ContinuousOn.div hRicCont.neg hspeedCont
    intro u hu
    exact ne_of_gt (Real.sqrt_pos.2
      ((S.base.metric t).pos (gamma u) (v u) (hvel u hu)))
  have hleftInt : IntervalIntegrable Q MeasureTheory.volume a b :=
    hQcont.intervalIntegrable_of_Icc hab
  have hrightInt :
      IntervalIntegrable (fun u ↦ A * Real.sqrt (G u))
        MeasureTheory.volume a b :=
    (continuousOn_const.mul hspeedCont).intervalIntegrable_of_Icc hab
  have hpoint : ∀ u ∈ Set.Icc a b, Q u ≤ A * Real.sqrt (G u) := by
    intro u hu
    have hGpos : 0 < G u :=
      (S.base.metric t).pos (gamma u) (v u) (hvel u hu)
    have hRicGe : -A * G u ≤ Ric u := by
      simpa only [neg_mul] using
        (neg_le_neg (by simpa only [Ric, G, v] using hRic u hu)).trans
          (neg_abs_le (Ric u))
    dsimp only [Q]
    rw [div_le_iff₀ (Real.sqrt_pos.2 hGpos)]
    rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hGpos)]
    linarith
  have hmono :
      (∫ u in a..b, Q u) ≤
        ∫ u in a..b, A * Real.sqrt (G u) :=
    intervalIntegral.integral_mono_on hab hleftInt hrightInt hpoint
  have hderiv := pathLength_timeDeriv_of_ricciFlow
    (I := I) S hS hab ht gamma hgamma hvel
  rw [hderiv.deriv, Variation.arcLength,
    ← intervalIntegral.integral_const_mul]
  simpa only [Q, Ric, G, v] using hmono

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A point whose scaled distance is strictly inside an Rm-controlled flow
ball has its initial distance anchored by its later scaled distance. -/
private theorem dist0_le_core
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real} (ht : 0 ≤ t)
    (hreg : Set.Ioc 0 t ⊆ D.regular)
    (htB : Set.Icc 0 t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
      ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x := by
  classical
  by_cases hOx : B.center = x
  · subst x
    simp only [riemannianEDistOf_self, mul_zero, le_refl]
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      le_refl]
  letI : IsManifold I 1 M :=
    IsManifold.of_le
      (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(S.base.metric t).toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun y : M ↦ TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner,
      (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := hcomplete_t.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t) := by
    intro y w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    congr 2
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let g := S.base.metric t
  let v : TangentSpace I B.center :=
    minimizingVec (I := I) g hEnorm B.center x
  let gamma : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm B.center v
  let L : Real → Real := fun s ↦
    Variation.arcLength (I := I) (S.base.metric s) gamma 0 1
  let f : Real → Real := fun s ↦ Real.exp (Lambda * s) * L s
  have hLambda : 0 < Lambda := by
    have hdNat : 0 < Module.finrank Real E :=
      Nat.pos_of_ne_zero (NeZero.ne _)
    have hd : 0 < d := by
      dsimp only [d]
      exact_mod_cast hdNat
    exact div_pos (sq_pos_of_pos hd) (sq_pos_of_pos B.radius_pos)
  have hdist_t :
      riemannianEDistOf (I := I) (S.base.metric t) B.center x =
        riemannianEDist I B.center x := by
    exact riemannianEDistOf_eq_riemannianEDist
      (I := I) (S.base.metric t) hEnorm B.center x
  have hfin_t :
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≠
        (⊤ : ENNReal) := by
    intro htop
    have hcoef0 :
        ENNReal.ofReal (Real.exp (Lambda * t)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    rw [htop, ENNReal.mul_top hcoef0] at hx
    exact (not_lt_of_ge le_top) hx
  have hfin : riemannianEDist I B.center x ≠ (⊤ : ENNReal) := by
    simpa only [hdist_t] using hfin_t
  have hvne : v ≠ 0 := by
    intro hv
    have hexp := minimizingVec_exp
      (I := I) g hEnorm B.center x
    dsimp only [v] at hv
    rw [hv, expMapIntrinsic_zero] at hexp
    exact hOx hexp
  have hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma := by
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn
        (I := I) g hEnorm B.center v)
  have hvel : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0 := by
    intro u _hu
    exact intrGeo_vel_ne (I := I) g hEnorm B.center v hvne u
  have hL_t :
      L t = (riemannianEDistOf
        (I := I) (S.base.metric t) B.center x).toReal := by
    have hgamma_min :
        gamma = minJoin (I := I) g hEnorm B.center x := by
      funext u
      rfl
    dsimp only [L]
    rw [hgamma_min, minJoin_arcLength, ← hdist_t]
  have hf_t :
      f t = Real.exp (Lambda * t) *
        (riemannianEDistOf
          (I := I) (S.base.metric t) B.center x).toReal := by
    simp only [f, hL_t]
  have hf_t_lt : f t < B.radius := by
    have hmulfin :
        ENNReal.ofReal (Real.exp (Lambda * t)) *
            riemannianEDistOf (I := I) (S.base.metric t) B.center x ≠
          (⊤ : ENNReal) :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_t
    have hreal :=
      (ENNReal.toReal_lt_toReal hmulfin ENNReal.ofReal_ne_top).2
        (by simpa only [Lambda, d] using hx)
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal B.radius_pos.le] at hreal
    rw [hf_t]
    exact hreal
  have hL_nonneg : ∀ s : Real, 0 ≤ L s := by
    intro s
    dsimp only [L]
    unfold Variation.arcLength
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun u _hu ↦ Real.sqrt_nonneg _)
  have hL_diff : ∀ s ∈ Set.Ioc 0 t, DifferentiableAt Real L s := by
    intro s hs
    simpa only [L] using
      (pathLength_timeDeriv_of_ricciFlow
        (I := I) S hS zero_le_one (hreg hs) gamma hgamma hvel).differentiableAt
  have hf_cont : ContinuousOn f (Set.Icc 0 t) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul
        (arcLength_contOn (I := I) hS
          zero_le_one (fun s hs ↦ hB.1 (htB hs)) gamma hgamma)
  have hlocal : ∀ s ∈ Set.Ioo 0 t, f s ≤ B.radius →
      DifferentiableAt Real f s ∧ 0 ≤ deriv f s := by
    intro s hs hfs
    have hsIcc : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.le⟩
    have hexp_one : 1 < Real.exp (Lambda * s) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (mul_pos hLambda hs.1)
    have hLs_lt : L s < B.radius := by
      rcases eq_or_lt_of_le (hL_nonneg s) with hL0 | hLpos
      · simpa only [← hL0] using B.radius_pos
      · calc
          L s < Real.exp (Lambda * s) * L s := by
            simpa only [one_mul] using
              mul_lt_mul_of_pos_right hexp_one hLpos
          _ = f s := rfl
          _ ≤ B.radius := hfs
    have hcurve : ∀ u ∈ Set.Icc (0 : Real) 1,
        gamma u ∈ B.setAt s := by
      intro u hu
      have hprefix :
          Variation.arcLength (I := I) (S.base.metric s) gamma 0 u ≤
            L s := by
        exact arcLength_mono (I := I) (S.base.metric s) hu hgamma
      have hgamma_u : ContMDiffOn 𝓘(Real, Real) I 1 gamma
          (Set.Icc 0 u) := hgamma.contMDiffOn
      have hedist := edistOf_le_arcLength
        (I := I) (S.base.metric s) hu.1 hgamma_u
      rw [show gamma 0 = B.center by
        exact intrinsicGeodesic_zero
          (I := I) g hEnorm B.center v] at hedist
      exact hedist.trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2
          (hprefix.trans_lt hLs_lt))
    have hsqrt : Real.sqrt (1 / B.radius ^ 4) = 1 / B.radius ^ 2 := by
      have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
      rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
      rw [show 1 / (B.radius ^ 2) ^ 2 =
          (1 / B.radius ^ 2) ^ 2 by field_simp]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
    have hL_lower : -Lambda * L s ≤ deriv L s := by
      simpa only [L] using
        pathLength_deriv_ge
          (I := I) S hS (A := Lambda) zero_le_one
            (hreg ⟨hs.1, hs.2.le⟩)
            gamma hgamma hvel
            (fun u hu ↦ by
              have hRic := ricci_abs_of_rm
                (I := I) B hB (htB hsIcc) (hcurve u hu)
                  (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
              rw [hsqrt] at hRic
              simpa only [Lambda, d, div_eq_mul_inv, one_mul] using hRic)
    have hexpDiff : DifferentiableAt Real
        (fun r : Real ↦ Real.exp (Lambda * r)) s := by
      fun_prop
    have hfDiff : DifferentiableAt Real f s := by
      exact hexpDiff.mul (hL_diff s ⟨hs.1, hs.2.le⟩)
    have hfDeriv : deriv f s =
        Real.exp (Lambda * s) * (deriv L s + Lambda * L s) := by
      dsimp only [f]
      change deriv ((fun r : Real ↦ Real.exp (Lambda * r)) * L) s = _
      rw [deriv_mul hexpDiff (hL_diff s ⟨hs.1, hs.2.le⟩)]
      rw [show deriv (fun r : Real ↦ Real.exp (Lambda * r)) s =
          Real.exp (Lambda * s) * Lambda by
        simpa only [zero_mul, zero_add, mul_one] using
          ((Real.hasDerivAt_exp (Lambda * s)).comp s
            ((hasDerivAt_const s Lambda).mul (hasDerivAt_id s))).deriv]
      ring
    refine ⟨hfDiff, ?_⟩
    rw [hfDeriv]
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hbelow : ∀ s ∈ Set.Icc 0 t, f s < B.radius :=
    no_first_exit htpos hf_t_lt hf_cont hlocal
  have hf_mono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : Real) t) hf_cont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hlocal s hs
        (hbelow s ⟨hs.1.le, hs.2.le⟩).le).1.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hlocal s hs (hbelow s ⟨hs.1.le, hs.2.le⟩).le).2
  have hf0_le : f 0 ≤ f t :=
    hf_mono (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  have hdist0 :
      riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
        ENNReal.ofReal (L 0) := by
    have hedist := edistOf_le_arcLength
      (I := I) (S.base.metric 0) zero_le_one hgamma.contMDiffOn
    rw [show gamma 0 = B.center by
      exact intrinsicGeodesic_zero
        (I := I) g hEnorm B.center v,
      show gamma 1 = x by
        simpa only [gamma, g, v, expMapIntrinsic_def] using
          minimizingVec_exp (I := I) g hEnorm B.center x] at hedist
    exact hedist
  have hlen : L 0 ≤ Real.exp (Lambda * t) *
      (riemannianEDistOf
        (I := I) (S.base.metric t) B.center x).toReal := by
    calc
      L 0 = f 0 := by simp only [f, mul_zero, Real.exp_zero, one_mul]
      _ ≤ f t := hf0_le
      _ = Real.exp (Lambda * t) *
          (riemannianEDistOf
            (I := I) (S.base.metric t) B.center x).toReal := hf_t
  calc
    riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
        ENNReal.ofReal (L 0) := hdist0
    _ ≤ ENNReal.ofReal (Real.exp (Lambda * t) *
        (riemannianEDistOf
          (I := I) (S.base.metric t) B.center x).toReal) :=
      ENNReal.ofReal_le_ofReal hlen
    _ = ENNReal.ofReal (Real.exp (Lambda * t)) *
        riemannianEDistOf
          (I := I) (S.base.metric t) B.center x := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        ENNReal.ofReal_toReal hfin_t]
    _ = ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x := by
      rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem dist0_fwd_core
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real} (ht : 0 ≤ t)
    (hreg : Set.Ioc 0 t ⊆ D.regular)
    (htB : Set.Icc 0 t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_0 : RiemannianMetricComplete (I := I) (S.base.metric 0))
    {x : M}
    (hx : ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric 0) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
      ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric 0) B.center x := by
  classical
  by_cases hOx : B.center = x
  · subst x
    simp only [riemannianEDistOf_self, mul_zero, le_refl]
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, le_refl]
  letI : IsManifold I 1 M := IsManifold.of_le
    (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(S.base.metric 0).toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y) :=
    ⟨⟨(S.base.metric 0).inner, (S.base.metric 0).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := hcomplete_0.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric 0) := by
    intro y w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    congr 2
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let g := S.base.metric 0
  let v : TangentSpace I B.center := minimizingVec (I := I) g hEnorm B.center x
  let gamma : Real → M := intrinsicGeodesic (I := I) g hEnorm B.center v
  let L : Real → Real := fun s ↦
    Variation.arcLength (I := I) (S.base.metric s) gamma 0 1
  let f : Real → Real := fun s ↦ Real.exp (Lambda * (t - s)) * L s
  have hLambda : 0 < Lambda := by
    have hdNat : 0 < Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
    have hd : 0 < d := by
      dsimp only [d]
      exact_mod_cast hdNat
    exact div_pos (sq_pos_of_pos hd) (sq_pos_of_pos B.radius_pos)
  have hdist_0 :
      riemannianEDistOf (I := I) (S.base.metric 0) B.center x =
        riemannianEDist I B.center x :=
    riemannianEDistOf_eq_riemannianEDist
      (I := I) (S.base.metric 0) hEnorm B.center x
  have hfin_0 :
      riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≠
        (⊤ : ENNReal) := by
    intro htop
    have hcoef0 : ENNReal.ofReal (Real.exp (Lambda * t)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    rw [htop, ENNReal.mul_top hcoef0] at hx
    exact (not_lt_of_ge le_top) hx
  have hfin : riemannianEDist I B.center x ≠ (⊤ : ENNReal) := by
    simpa only [hdist_0] using hfin_0
  have hvne : v ≠ 0 := by
    intro hv
    have hexp := minimizingVec_exp (I := I) g hEnorm B.center x
    dsimp only [v] at hv
    rw [hv, expMapIntrinsic_zero] at hexp
    exact hOx hexp
  have hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma :=
    contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm B.center v)
  have hvel : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0 := by
    intro u _hu
    exact intrGeo_vel_ne (I := I) g hEnorm B.center v hvne u
  have hL_0 : L 0 = (riemannianEDistOf
      (I := I) (S.base.metric 0) B.center x).toReal := by
    have hgamma_min : gamma = minJoin (I := I) g hEnorm B.center x := by
      funext u
      rfl
    dsimp only [L]
    rw [hgamma_min, minJoin_arcLength, ← hdist_0]
  have hf_0 : f 0 = Real.exp (Lambda * t) *
      (riemannianEDistOf (I := I) (S.base.metric 0) B.center x).toReal := by
    simp only [f, hL_0, sub_zero]
  have hf_0_lt : f 0 < B.radius := by
    have hmulfin : ENNReal.ofReal (Real.exp (Lambda * t)) *
          riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≠
        (⊤ : ENNReal) :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_0
    have hreal := (ENNReal.toReal_lt_toReal hmulfin ENNReal.ofReal_ne_top).2
      (by simpa only [Lambda, d] using hx)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal B.radius_pos.le] at hreal
    rw [hf_0]
    exact hreal
  have hL_nonneg : ∀ s : Real, 0 ≤ L s := by
    intro s
    dsimp only [L]
    unfold Variation.arcLength
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun u _hu ↦ Real.sqrt_nonneg _)
  have hL_diff : ∀ s ∈ Set.Ioc 0 t, DifferentiableAt Real L s := by
    intro s hs
    simpa only [L] using (pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS zero_le_one (hreg hs) gamma hgamma hvel).differentiableAt
  have hf_cont : ContinuousOn f (Set.Icc 0 t) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn.mul
        (arcLength_contOn (I := I) hS zero_le_one
          (fun s hs ↦ hB.1 (htB hs)) gamma hgamma)
  have hlocal : ∀ s ∈ Set.Ioo 0 t, f s ≤ B.radius →
      DifferentiableAt Real f s ∧ deriv f s ≤ 0 := by
    intro s hs hfs
    have hsIcc : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.le⟩
    have hexp_one : 1 < Real.exp (Lambda * (t - s)) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (mul_pos hLambda (sub_pos.mpr hs.2))
    have hLs_lt : L s < B.radius := by
      rcases eq_or_lt_of_le (hL_nonneg s) with hL0 | hLpos
      · simpa only [← hL0] using B.radius_pos
      · calc
          L s < Real.exp (Lambda * (t - s)) * L s := by
            simpa only [one_mul] using mul_lt_mul_of_pos_right hexp_one hLpos
          _ = f s := rfl
          _ ≤ B.radius := hfs
    have hcurve : ∀ u ∈ Set.Icc (0 : Real) 1, gamma u ∈ B.setAt s := by
      intro u hu
      have hprefix : Variation.arcLength
          (I := I) (S.base.metric s) gamma 0 u ≤ L s :=
        arcLength_mono (I := I) (S.base.metric s) hu hgamma
      have hedist := edistOf_le_arcLength
        (I := I) (S.base.metric s) hu.1 hgamma.contMDiffOn
      rw [show gamma 0 = B.center by
        exact intrinsicGeodesic_zero (I := I) g hEnorm B.center v] at hedist
      exact hedist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2
        (hprefix.trans_lt hLs_lt))
    have hsqrt : Real.sqrt (1 / B.radius ^ 4) = 1 / B.radius ^ 2 := by
      have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
      rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
      rw [show 1 / (B.radius ^ 2) ^ 2 = (1 / B.radius ^ 2) ^ 2 by field_simp]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
    have hL_upper : deriv L s ≤ Lambda * L s := by
      simpa only [L] using pathLength_deriv_le
        (I := I) hS (A := Lambda) zero_le_one
          (hreg ⟨hs.1, hs.2.le⟩) gamma hgamma hvel
          (fun u hu ↦ by
            have hRic := ricci_abs_of_rm
              (I := I) B hB (htB hsIcc) (hcurve u hu)
                (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
            rw [hsqrt] at hRic
            simpa only [Lambda, d, div_eq_mul_inv, one_mul] using hRic)
    have hexpDiff : DifferentiableAt Real
        (fun r : Real ↦ Real.exp (Lambda * (t - r))) s := by fun_prop
    have hfDiff : DifferentiableAt Real f s :=
      hexpDiff.mul (hL_diff s ⟨hs.1, hs.2.le⟩)
    have hfDeriv : deriv f s = Real.exp (Lambda * (t - s)) *
        (deriv L s - Lambda * L s) := by
      dsimp only [f]
      change deriv ((fun r : Real ↦ Real.exp (Lambda * (t - r))) * L) s = _
      rw [deriv_mul hexpDiff (hL_diff s ⟨hs.1, hs.2.le⟩)]
      rw [show deriv (fun r : Real ↦ Real.exp (Lambda * (t - r))) s =
          -Real.exp (Lambda * (t - s)) * Lambda by
        convert ((Real.hasDerivAt_exp (Lambda * (t - s))).comp s
          ((hasDerivAt_const s Lambda).mul
            ((hasDerivAt_const s t).sub (hasDerivAt_id s)))).deriv using 1
        all_goals ring]
      ring
    refine ⟨hfDiff, ?_⟩
    rw [hfDeriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hbelow : ∀ s ∈ Set.Icc 0 t, f s < B.radius :=
    no_last_exit htpos hf_0_lt hf_cont hlocal
  have hf_anti : AntitoneOn f (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) t) hf_cont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hlocal s hs (hbelow s ⟨hs.1.le, hs.2.le⟩).le).1.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hlocal s hs (hbelow s ⟨hs.1.le, hs.2.le⟩).le).2
  have hf_t_le : f t ≤ f 0 :=
    hf_anti (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  have hdist_t : riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
      ENNReal.ofReal (L t) := by
    have hedist := edistOf_le_arcLength
      (I := I) (S.base.metric t) zero_le_one hgamma.contMDiffOn
    rw [show gamma 0 = B.center by
      exact intrinsicGeodesic_zero (I := I) g hEnorm B.center v,
      show gamma 1 = x by
        simpa only [gamma, g, v, expMapIntrinsic_def] using
          minimizingVec_exp (I := I) g hEnorm B.center x] at hedist
    exact hedist
  have hlen : L t ≤ Real.exp (Lambda * t) *
      (riemannianEDistOf (I := I) (S.base.metric 0) B.center x).toReal := by
    calc
      L t = f t := by simp only [f, sub_self, mul_zero, Real.exp_zero, one_mul]
      _ ≤ f 0 := hf_t_le
      _ = Real.exp (Lambda * t) *
          (riemannianEDistOf (I := I) (S.base.metric 0) B.center x).toReal := hf_0
  calc
    riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
        ENNReal.ofReal (L t) := hdist_t
    _ ≤ ENNReal.ofReal (Real.exp (Lambda * t) *
        (riemannianEDistOf (I := I) (S.base.metric 0) B.center x).toReal) :=
      ENNReal.ofReal_le_ofReal hlen
    _ = ENNReal.ofReal (Real.exp (Lambda * t)) *
        riemannianEDistOf (I := I) (S.base.metric 0) B.center x := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hfin_0]
    _ = ENNReal.ofReal
          (Real.exp
            (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric 0) B.center x := by rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem distPair_core
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {s t : Real} (hst : s ≤ t)
    (hreg : Set.Ioc s t ⊆ D.regular)
    (hstB : Set.Icc s t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_s : RiemannianMetricComplete (I := I) (S.base.metric s))
    (hcomplete_t : RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal
          (Real.exp
            (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) *
              (t - s))) *
        riemannianEDistOf (I := I) (S.base.metric s) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x ∧
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x := by
  let delta : Real := t - s
  let d : Real := Module.finrank Real E
  let Lambda : Real := d ^ 2 / B.radius ^ 2
  let D' := D.timeShift s
  let S' : SolutionOn (I := I) (M := M) D' := S.timeShift s
  let time' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D' :=
    ⟨(time : Real) - s, by
      change (time : Real) - s + s ∈ D.carrier
      simpa only [sub_add_cancel] using time.2⟩
  let B' : FlowMetricBall S' time' := {
    center := B.center
    radius := B.radius
    radius_pos := B.radius_pos }
  have hdelta : 0 ≤ delta := sub_nonneg.mpr hst
  have hS' : IsSolutionOn (I := I) S' := by
    simpa only [S'] using isSolutionOn_timeShift (I := I) hS s
  have hB' : B'.IsRmControlled := by
    constructor
    · intro r hr
      change r + s ∈ D.carrier
      apply hB.1
      dsimp only [B', time'] at hr ⊢
      constructor <;> linarith [hr.1, hr.2]
    · intro r hr y hy
      have hr' : r + s ∈
          Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) := by
        dsimp only [B', time'] at hr
        constructor <;> linarith [hr.1, hr.2]
      have hy' : y ∈ B.setAt (r + s) := by
        simpa only [B', FlowMetricBall.setAt, S',
          SolutionOn.timeShift_base_metric] using hy
      have hraw := hB.2 (r + s) hr' y hy'
      simpa only [B', FlowMetricBall.rmNormSq, S',
        SolutionOn.timeShift_base_metric] using hraw
  have hreg' : Set.Ioc 0 delta ⊆ D'.regular := by
    intro r hr
    change r + s ∈ D.regular
    apply hreg
    dsimp only [delta] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hstB' : Set.Icc 0 delta ⊆
      Set.Icc ((time' : Real) - B'.radius ^ 2) (time' : Real) := by
    intro r hr
    have hrst : r + s ∈ Set.Icc s t := by
      dsimp only [delta] at hr
      constructor <;> linarith [hr.1, hr.2]
    have hraw := hstB hrst
    dsimp only [B', time']
    constructor <;> linarith [hraw.1, hraw.2]
  have hcomplete_0' :
      RiemannianMetricComplete (I := I) (S'.base.metric 0) := by
    simpa only [S', SolutionOn.timeShift_base_metric, zero_add] using hcomplete_s
  have hcomplete_delta' :
      RiemannianMetricComplete (I := I) (S'.base.metric delta) := by
    simpa only [S', SolutionOn.timeShift_base_metric, delta, sub_add_cancel] using
      hcomplete_t
  have hLambda : 0 ≤ Lambda :=
    div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  have hcoef : ENNReal.ofReal (Real.exp (Lambda * delta)) ≤
      ENNReal.ofReal (Real.exp (2 * Lambda * delta)) :=
    ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by nlinarith [hLambda, hdelta]))
  have hx_one : ENNReal.ofReal (Real.exp (Lambda * delta)) *
        riemannianEDistOf (I := I) (S.base.metric s) B.center x <
      ENNReal.ofReal B.radius := by
    exact (mul_le_mul_left hcoef _).trans_lt
      (by simpa only [Lambda, delta, d] using hx)
  have hforward' := dist0_fwd_core (I := I) hS' B' hB' hdelta hreg' hstB'
    hcomplete_0' (x := x) (by
      simpa only [B', S', SolutionOn.timeShift_base_metric, zero_add,
        Lambda, delta, d] using hx_one)
  have hforward :
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
        ENNReal.ofReal (Real.exp (Lambda * delta)) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x := by
    simpa only [B', S', SolutionOn.timeShift_base_metric, zero_add,
      delta, sub_add_cancel, Lambda, d] using hforward'
  have hcoef_mul : ENNReal.ofReal (Real.exp (Lambda * delta)) *
        ENNReal.ofReal (Real.exp (Lambda * delta)) =
      ENNReal.ofReal (Real.exp (2 * Lambda * delta)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hx_late : ENNReal.ofReal (Real.exp (Lambda * delta)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x <
      ENNReal.ofReal B.radius := by
    calc
      ENNReal.ofReal (Real.exp (Lambda * delta)) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
          ENNReal.ofReal (Real.exp (Lambda * delta)) *
            (ENNReal.ofReal (Real.exp (Lambda * delta)) *
              riemannianEDistOf
                (I := I) (S.base.metric s) B.center x) :=
        mul_le_mul_right hforward _
      _ = ENNReal.ofReal (Real.exp (2 * Lambda * delta)) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x := by
        rw [← mul_assoc, hcoef_mul]
      _ < ENNReal.ofReal B.radius := by
        simpa only [Lambda, delta, d] using hx
  have hback' := dist0_le_core (I := I) hS' B' hB' hdelta hreg' hstB'
    hcomplete_delta' (x := x) (by
      simpa only [B', S', SolutionOn.timeShift_base_metric, delta,
        sub_add_cancel, Lambda, d] using hx_late)
  have hback :
      riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
        ENNReal.ofReal (Real.exp (Lambda * delta)) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x := by
    simpa only [B', S', SolutionOn.timeShift_base_metric, zero_add,
      delta, sub_add_cancel, Lambda, d] using hback'
  exact ⟨by simpa only [Lambda, delta, d] using hback,
    by simpa only [Lambda, delta, d] using hforward⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A point whose scaled distance is strictly inside an Rm-controlled flow
ball has its initial distance anchored by its later scaled distance. -/
theorem dist0_le_scaled
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real} (ht : 0 ≤ t)
    (hreg : Set.Ioc 0 t ⊆ D.regular)
    (htB : Set.Icc 0 t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_t : RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric 0) B.center x ≤
      ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * t)) *
        riemannianEDistOf (I := I) (S.base.metric t) B.center x :=
  dist0_le_core (I := I) hS B hB ht hreg htB hcomplete_t hx

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a short controlled ball interval, the endpoint distances are bounded
by the same exponential factor in both directions. -/
theorem distPair_scaled
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {s t : Real} (hst : s ≤ t)
    (hreg : Set.Ioc s t ⊆ D.regular)
    (hstB : Set.Icc s t ⊆
      Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hcomplete_s : RiemannianMetricComplete (I := I) (S.base.metric s))
    (hcomplete_t : RiemannianMetricComplete (I := I) (S.base.metric t))
    {x : M}
    (hx : ENNReal.ofReal (Real.exp
          (2 * ((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
        riemannianEDistOf (I := I) (S.base.metric s) B.center x <
          ENNReal.ofReal B.radius) :
    riemannianEDistOf (I := I) (S.base.metric s) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric t) B.center x ∧
      riemannianEDistOf (I := I) (S.base.metric t) B.center x ≤
        ENNReal.ofReal (Real.exp
          (((Module.finrank Real E : Real) ^ 2 / B.radius ^ 2) * (t - s))) *
          riemannianEDistOf (I := I) (S.base.metric s) B.center x :=
  distPair_core (I := I) hS B hB hst hreg hstB hcomplete_s hcomplete_t hx

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
