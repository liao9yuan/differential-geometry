import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.CurveEnergy

set_option autoImplicit false

/-!
# Moving-endpoint distance rate

This file bounds the first-order displacement of a locally `C¹` endpoint
curve when distance is measured by the backward-time metric of a smooth metric
family.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped ENNReal Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [I.Boundaryless] [IsManifold I 1 M] in
private theorem edist_le_arc
    (g : SmoothRiemannianMetric I M) {x : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b)) :
    riemannianEDistOf (I := I) g (x a) (x b) ≤
      ENNReal.ofReal (Variation.arcLength (I := I) g x a b) := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (x a) (x b) ≤ _
  apply Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
    (I := I) g hab hx
  intro t ht
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  congr 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [I.Boundaryless] in
/-- A `C¹` curve on a compact interval has a uniform fixed-metric intrinsic
distance bound linear in the parameter distance. -/
theorem edist_curve_lip
    (g : SmoothRiemannianMetric I M) {x : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b)) :
    ∃ C : NNReal, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (riemannianEDistOf (I := I) g (x s) (x t)).toReal ≤
        (C : Real) * |t - s| := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨(0 : NNReal), ?_⟩
    intro s hs t ht
    have hs' : s = a := le_antisymm hs.2 hs.1
    have ht' : t = a := le_antisymm ht.2 ht.1
    subst s
    subst t
    simp only [riemannianEDistOf_self, ENNReal.toReal_zero, sub_self,
      abs_zero, NNReal.coe_zero, zero_mul]
    exact le_rfl
  · have hUnique : UniqueMDiffOn 𝓘(Real, Real) (Icc a b) := by
      intro u hu
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact (uniqueDiffOn_Icc hab) u hu
    let v : (u : Real) → TangentSpace I (x u) := fun u ↦
      mfderivWithin 𝓘(Real, Real) I x (Icc a b) u (1 : Real)
    have hTan := hx.continuousOn_tangentMapWithin (le_refl 1) hUnique
    have hunit : Continuous (fun u : Real ↦
        (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
      exact (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hunitMaps : MapsTo
        (fun u : Real ↦ (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
        (Icc a b) (Bundle.TotalSpace.proj ⁻¹' Icc a b) := by
      intro u hu
      simpa using hu
    have hvel : ContinuousOn
        (fun u : Real ↦ TotalSpace.mk' E
          (E := fun y : M ↦ TangentSpace I y) (x u) (v u)) (Icc a b) := by
      exact (hTan.comp hunit.continuousOn hunitMaps).congr (fun _ _ ↦ rfl)
    letI cg : Bundle.ContinuousRiemannianMetric E
        (fun y : M ↦ TangentSpace I y) := g.toContinuousRiemannianMetric
    letI rb : Bundle.RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨cg.toRiemannianMetric⟩
    have hquad : ContinuousOn (fun u ↦ g.inner (x u) (v u) (v u))
        (Icc a b) := by
      have h := ContinuousOn.inner_bundle (F := E) (B := M)
        (E := fun y : M ↦ TangentSpace I y) (b := x) (v := v) (w := v)
        (s := Icc a b) hvel hvel
      exact h.congr (fun _ _ ↦ rfl)
    let speedW : Real → Real := fun u ↦ Real.sqrt (g.inner (x u) (v u) (v u))
    have hspeedW : ContinuousOn speedW (Icc a b) := by
      exact Real.continuous_sqrt.comp_continuousOn hquad
    obtain ⟨C0, hC0⟩ := isCompact_Icc.bddAbove_image hspeedW
    let C : NNReal := ⟨max C0 0, le_max_right _ _⟩
    have hboundW : ∀ u ∈ Icc a b, speedW u ≤ (C : Real) := by
      intro u hu
      exact (hC0 ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    refine ⟨C, ?_⟩
    have hforward : ∀ {s t : Real}, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
        (riemannianEDistOf (I := I) g (x s) (x t)).toReal ≤
          (C : Real) * |t - s| := by
      intro s t hs ht hst
      let speed : Real → Real := fun u ↦ Real.sqrt
        (g.inner (x u)
          (mfderiv 𝓘(Real, Real) I x u (1 : Real))
          (mfderiv 𝓘(Real, Real) I x u (1 : Real)))
      have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
      have hspeedWInt : IntervalIntegrable speedW volume s t :=
        (hspeedW.mono hsub).intervalIntegrable_of_Icc hst
      have heq : ∀ᵐ u ∂(volume.restrict (uIoc s t)), speedW u = speed u := by
        have hmem : ∀ᵐ u ∂(volume.restrict (uIoc s t)), u ∈ Ioo s t := by
          rw [uIoc_of_le hst, ← restrict_Ioo_eq_restrict_Ioc]
          exact ae_restrict_mem measurableSet_Ioo
        filter_upwards [hmem] with u hu
        have huab : u ∈ Ioo a b :=
          ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩
        have hv : v u = mfderiv 𝓘(Real, Real) I x u (1 : Real) := by
          dsimp only [v]
          exact congrArg (fun A ↦ A (1 : Real))
            (mfderivWithin_of_mem_nhds (I := 𝓘(Real, Real)) (I' := I)
              (f := x) (s := Icc a b)
              (Icc_mem_nhds huab.1 huab.2))
        simp only [speedW, speed, hv]
      have hspeedInt : IntervalIntegrable speed volume s t :=
        hspeedWInt.congr_ae heq
      have hpoint : ∀ u ∈ Ioo s t, speed u ≤ (C : Real) := by
        intro u hu
        have huab : u ∈ Ioo a b :=
          ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩
        have huIcc : u ∈ Icc a b := ⟨huab.1.le, huab.2.le⟩
        have hv : v u = mfderiv 𝓘(Real, Real) I x u (1 : Real) := by
          dsimp only [v]
          exact congrArg (fun A ↦ A (1 : Real))
            (mfderivWithin_of_mem_nhds (I := 𝓘(Real, Real)) (I' := I)
              (f := x) (s := Icc a b)
              (Icc_mem_nhds huab.1 huab.2))
        simpa only [speedW, speed, hv] using hboundW u huIcc
      have hlen : Variation.arcLength (I := I) g x s t ≤
          (C : Real) * (t - s) := by
        unfold Variation.arcLength
        have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hst
          hspeedInt intervalIntegrable_const hpoint
        simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          using hmono
      have hcurve : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc s t) :=
        hx.mono hsub
      have hed := edist_le_arc (I := I) g hst hcurve
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
      have hlen0 : 0 ≤ Variation.arcLength (I := I) g x s t := by
        unfold Variation.arcLength
        exact intervalIntegral.integral_nonneg hst
          (fun _ _ ↦ Real.sqrt_nonneg _)
      rw [ENNReal.toReal_ofReal hlen0] at hreal
      calc
        (riemannianEDistOf (I := I) g (x s) (x t)).toReal
            ≤ Variation.arcLength (I := I) g x s t := hreal
        _ ≤ (C : Real) * (t - s) := hlen
        _ = (C : Real) * |t - s| := by rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    intro s hs t ht
    by_cases hst : s ≤ t
    · exact hforward hs ht hst
    · rw [edistOf_comm (I := I) g (x s) (x t)]
      simpa only [abs_sub_comm] using hforward ht hs (le_of_not_ge hst)

omit [I.Boundaryless] in
/-- A locally `C¹` moving endpoint has, to first order, at most its base-time
speed in the backward-time Riemannian distance. -/
theorem edist_smooth_rate
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    {T tau : Real} (ht : T - tau ∈ D.regular)
    {x : Real → M}
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ s,
      tau < s → s < tau + delta →
        (riemannianEDistOf (I := I) (S.base.metric (T - s))
          (x tau) (x s)).toReal ≤
        (Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
            (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
            (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon) *
          (s - tau) := by
  classical
  intro epsilon hepsilon
  rcases (contMDiffAt_iff_contMDiffOn_nhds (n := (1 : WithTop ℕ∞))
      (by simp)).mp hx with ⟨U, hU, hxU⟩
  rcases mem_nhds_iff_exists_Ioo_subset.mp hU with
    ⟨a, b, htauab, habU⟩
  have hxab : ContMDiffOn 𝓘(Real, Real) I 1 x (Ioo a b) :=
    hxU.mono habU
  obtain ⟨alpha, beta, htIoo, hwin⟩ := D.exists_Icc_regular ht
  let v : (u : Real) → TangentSpace I (x u) :=
    fun u ↦ mfderivWithin 𝓘(Real, Real) I x (Ioo a b) u (1 : Real)
  let K : Set (Real × Real) :=
    {p | T - p.1 ∈ D.carrier ∧ p.2 ∈ Ioo a b}
  let p0 : K := ⟨(tau, tau), D.regular_subset ht, htauab⟩
  have hunit : Continuous (fun u : Real ↦
      (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hunitMaps : MapsTo
      (fun u : Real ↦ (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
      (Ioo a b) (Bundle.TotalSpace.proj ⁻¹' Ioo a b) := by
    intro u hu
    simpa using hu
  have hvelOn : ContinuousOn
      (fun u : Real ↦ tangentMapWithin 𝓘(Real, Real) I x (Ioo a b)
        (⟨u, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
      (Ioo a b) :=
    (hxab.continuousOn_tangentMapWithin (le_refl 1)
      isOpen_Ioo.uniqueMDiffOn).comp hunit.continuousOn hunitMaps
  have hparam : Continuous (fun p : K ↦ (p.1 : Real × Real).2) :=
    continuous_snd.comp continuous_subtype_val
  have hparam' : Continuous (fun p : K ↦
      (⟨(p.1 : Real × Real).2, p.2.2⟩ : {u : Real // u ∈ Ioo a b})) :=
    hparam.subtype_mk _
  have hbase : Continuous (fun p : K ↦ x (p.1 : Real × Real).2) := by
    exact (continuousOn_iff_continuous_restrict.mp hxab.continuousOn).comp hparam'
  have hvel : Continuous (fun p : K ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (x (p.1 : Real × Real).2) (v (p.1 : Real × Real).2)) := by
    have hrestrict := continuousOn_iff_continuous_restrict.mp hvelOn
    have hcomp := hrestrict.comp hparam'
    simpa only [v, tangentMapWithin] using hcomp
  let q : K → Real := fun p ↦
    (S.base.metric (T - (p.1 : Real × Real).1)).inner
      (x (p.1 : Real × Real).2) (v (p.1 : Real × Real).2)
      (v (p.1 : Real × Real).2)
  have hq : Continuous q := by
    have htime : Continuous (fun p : K ↦ T - (p.1 : Real × Real).1) :=
      continuous_const.sub (continuous_fst.comp continuous_subtype_val)
    have heval := hG.metricTensor_cont.eval_continuous
      (P := K)
      (τ := fun p ↦ T - (p.1 : Real × Real).1)
      (b := fun p ↦ x (p.1 : Real × Real).2)
      htime (fun p ↦ p.2.1) hbase
      (v := fun _ p ↦ v (p.1 : Real × Real).2)
      (fun _ ↦ hvel)
    refine heval.congr (fun p ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hv_tau : v tau = mfderiv 𝓘(Real, Real) I x tau (1 : Real) := by
    exact congrArg (fun A ↦ A (1 : Real))
      (mfderivWithin_of_isOpen (I := 𝓘(Real, Real)) (I' := I)
        (f := x) isOpen_Ioo htauab)
  let q0 : Real := (S.base.metric (T - tau)).inner (x tau)
    (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
    (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
  have hq0 : 0 ≤ q0 := by
    let w := mfderiv 𝓘(Real, Real) I x tau (1 : Real)
    rcases eq_or_ne w 0 with hw | hw
    · simp only [q0, w, hw, map_zero]
      exact le_rfl
    · exact ((S.base.metric (T - tau)).pos (x tau) w hw).le
  let C : Real := Real.sqrt q0 + epsilon
  have hC : 0 < C := by
    dsimp only [C]
    linarith [Real.sqrt_nonneg q0]
  have hq0C : q p0 < C ^ 2 := by
    have hsquare : (Real.sqrt q0) ^ 2 = q0 := Real.sq_sqrt hq0
    dsimp only [q, p0]
    rw [hv_tau]
    change q0 < C ^ 2
    dsimp only [C]
    nlinarith [Real.sqrt_nonneg q0]
  have hnear : {p : K | q p < C ^ 2} ∈ 𝓝 p0 :=
    (isOpen_lt hq continuous_const).mem_nhds hq0C
  rcases Metric.mem_nhds_iff.mp hnear with ⟨r, hr, hball⟩
  let delta := min (b - tau) (min (T - alpha - tau) r)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (sub_pos.mpr htauab.2)
      (lt_min (by linarith [htIoo.1]) hr)
  refine ⟨delta, hdelta, ?_⟩
  intro s htaus hsdelta
  have hsb : s < b := by
    have hdle : delta ≤ b - tau := min_le_left _ _
    linarith
  have htime : T - s ∈ D.carrier := by
    apply D.regular_subset
    apply hwin
    constructor
    · have hdle : delta ≤ T - alpha - tau :=
        (min_le_right _ _).trans (min_le_left _ _)
      linarith
    · linarith [htIoo.2]
  have hcurve : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc tau s) := by
    apply hxab.mono
    intro u hu
    exact ⟨htauab.1.trans_le hu.1, hu.2.trans_lt hsb⟩
  have hpoint : ∀ u ∈ Icc tau s,
      Real.sqrt ((S.base.metric (T - s)).inner (x u)
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))) ≤ C := by
    intro u hu
    have huab : u ∈ Ioo a b :=
      ⟨htauab.1.trans_le hu.1, hu.2.trans_lt hsb⟩
    let p : K := ⟨(s, u), htime, huab⟩
    have hpr : dist p p0 < r := by
      have hdr : delta ≤ r := (min_le_right _ _).trans (min_le_right _ _)
      rw [Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      constructor
      · rw [abs_of_pos (sub_pos.mpr htaus)]
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
        linarith [hu.2, hsdelta, hdr]
    have hpq : q p < C ^ 2 := hball (Metric.mem_ball.mpr hpr)
    have hv_u : v u = mfderiv 𝓘(Real, Real) I x u (1 : Real) :=
      congrArg (fun A ↦ A (1 : Real))
        (mfderivWithin_of_isOpen (I := 𝓘(Real, Real)) (I' := I)
          (f := x) isOpen_Ioo huab)
    apply le_of_lt
    rw [Real.sqrt_lt' hC]
    simpa only [q, p, hv_u] using hpq
  have hspeedCont : ContinuousOn
      (fun u ↦ Real.sqrt ((S.base.metric (T - s)).inner (x u)
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))))
      (Icc tau s) := by
    have hsub : Icc tau s ⊆ Ioo a b := by
      intro u hu
      exact ⟨htauab.1.trans_le hu.1, hu.2.trans_lt hsb⟩
    have hquadOn : ContinuousOn
        (fun u ↦ (S.base.metric (T - s)).inner (x u)
          (mfderiv 𝓘(Real, Real) I x u (1 : Real))
          (mfderiv 𝓘(Real, Real) I x u (1 : Real)))
        (Icc tau s) := by
      have hsmap : Continuous (fun u : {u : Real // u ∈ Icc tau s} ↦
          (⟨(s, (u : Real)), htime, hsub u.2⟩ : K)) := by
        apply Continuous.subtype_mk
        exact continuous_const.prodMk continuous_subtype_val
      have hcomp := hq.comp hsmap
      rw [continuousOn_iff_continuous_restrict]
      refine hcomp.congr (fun u ↦ ?_)
      have hv_u : v (u : Real) =
            mfderiv 𝓘(Real, Real) I x (u : Real) (1 : Real) :=
        congrArg (fun A ↦ A (1 : Real))
          (mfderivWithin_of_isOpen (I := 𝓘(Real, Real)) (I' := I)
            (f := x) isOpen_Ioo (hsub u.2))
      simp only [Function.comp_apply, Set.restrict_apply, q, hv_u]
    exact Real.continuous_sqrt.comp_continuousOn hquadOn
  have hspeedInt : IntervalIntegrable
      (fun u ↦ Real.sqrt ((S.base.metric (T - s)).inner (x u)
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))
        (mfderiv 𝓘(Real, Real) I x u (1 : Real))))
      volume tau s := by
    exact hspeedCont.intervalIntegrable_of_Icc htaus.le
  have hlen : Variation.arcLength (I := I) (S.base.metric (T - s)) x tau s ≤
      C * (s - tau) := by
    unfold Variation.arcLength
    have hmono := intervalIntegral.integral_mono_on htaus.le hspeedInt
      intervalIntegrable_const hpoint
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_mul,
      mul_comm] using hmono
  have hed := edist_le_arc (I := I) (S.base.metric (T - s)) htaus.le hcurve
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
  have hlen0 : 0 ≤ Variation.arcLength (I := I)
      (S.base.metric (T - s)) x tau s := by
    unfold Variation.arcLength
    exact intervalIntegral.integral_nonneg htaus.le
      (fun _ _ ↦ Real.sqrt_nonneg _)
  rw [ENNReal.toReal_ofReal hlen0] at hreal
  exact hreal.trans hlen

end DifferentialGeometry.PDE.RicciFlow
