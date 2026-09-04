import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SegmentCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ScalarCompact
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1AC
import DifferentialGeometry.Geometry.Metric.ChartLipschitz

set_option autoImplicit false

/-!
# Density of regular curves among finite-action L-segments

This file realizes square-root-time finite-action segments in the existing
finite-chart `timeH1` framework and compares their actions with smooth
fixed-endpoint approximants.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor.Tensor0SRiemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}

section Topological

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M] [ConnectedSpace M]

omit [I.Boundaryless] in
/-- Square-root backward time preserves absolute continuity of a finite-action
same-clock segment. -/
theorem lSeg_sq_ac
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma) :
    letI : PseudoMetricSpace M := lSegmentMetric S T
    AbsolutelyContinuousOnInterval (sqReparam gamma) a b := by
  letI : PseudoMetricSpace M := lSegmentMetric S T
  simpa only [sqReparam, Function.comp_def] using
    AbsolutelyContinuousOnInterval.comp_sq ha hab (hgamma.ac S T Set.univ)

omit [I.Boundaryless] in
/-- The regularized Lagrangian of a finite-action same-clock segment is
integrable after square-root backward-time reparameterization. -/
theorem lSeg_reg_int
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma) :
    IntervalIntegrable (lRegLag S T (sqReparam gamma)) volume a b := by
  have hChange :=
    intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (g := lDensity S T gamma) (f := fun s : Real ↦ s ^ 2)
      (f' := fun s : Real ↦ 2 * s) (a := a) (b := b)
      (continuous_id.pow 2).continuousOn
      (by
        intro s _
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        have hsa : a < s := by
          simpa only [min_eq_left hab] using hs.1
        exact mul_nonneg (by norm_num) (ha.trans hsa.le))
  have htrans : IntervalIntegrable
      (fun s ↦ (lDensity S T gamma ∘ fun r : Real ↦ r ^ 2) s * (2 * s))
      volume a b :=
    hChange.mpr hgamma.2.2.1
  refine htrans.congr_ae ?_
  filter_upwards
    [ae_restrict_mem measurableSet_uIoc,
      Measure.ae_ne (volume.restrict (uIoc a b)) (0 : Real)]
      with s hs hs0
  have hsIcc : s ∈ Icc a b := by
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
  have hsNonneg : 0 ≤ s := by
    exact ha.trans hsIcc.1
  have hsPos : 0 < s := lt_of_le_of_ne hsNonneg hs0.symm
  simpa only [Function.comp_apply, lRegDensity_eq] using
    lDensity_sq_pos (I := I) S T gamma s hsPos

omit [FiniteDimensional Real E] [I.Boundaryless] in
private theorem lChart_ac_cpt
    (S : SolutionOn (I := I) (M := M) D) (T A B : Real)
    (hAB : A ≤ B) (alpha : Real → M) (p : M) {Q : Set M}
    (hAC :
      letI : PseudoMetricSpace M := lSegmentMetric S T
      AbsolutelyContinuousOnInterval alpha A B)
    (hQc : IsCompact Q) (hQsrc : Q ⊆ (chartAt H p).source)
    (hαQ : MapsTo alpha (Icc A B) Q) :
    AbsolutelyContinuousOnInterval
      (fun r ↦ extChartAt I p (alpha (A + r))) 0 (B - A) := by
  let g := S.base.metric T
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let canonicalENorm : (x : M) → ENorm (TangentSpace I x) :=
    fun _ ↦ inferInstance
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI (x : M) : ENorm (TangentSpace I x) := canonicalENorm x
  letI (x : M) : NormedAddCommGroup (TangentSpace I x) :=
    Tensor0SBundle.tangentSpace_normedAddCommGroup x
  letI (x : M) : NormedSpace Real (TangentSpace I x) :=
    Tensor0SBundle.tangentSpace_normedSpace x
  letI : PseudoMetricSpace M := lSegmentMetric S T
  let L : Real := B - A
  let shift : Real → Real := fun r ↦ A + r
  have hL : 0 ≤ L := by
    simpa only [L] using sub_nonneg.mpr hAB
  have hshiftCD : ContDiff Real 1 shift := by
    simpa only [shift] using contDiff_const.add contDiff_id
  obtain ⟨K, hshiftLip⟩ :=
    hshiftCD.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_Icc (0 : Real) L) isCompact_Icc
  have hshiftAC : AbsolutelyContinuousOnInterval (alpha ∘ shift) 0 L := by
    apply AbsolutelyContinuousOnInterval.comp_mono_lip hAC
      (by simpa only [uIcc_of_le hL] using hshiftLip)
    · intro x hx y hy hxy
      simpa only [shift, add_le_add_iff_left] using hxy
    · intro r hr
      rw [uIcc_of_le hL] at hr
      rw [uIcc_of_le hAB]
      change r ∈ Icc (0 : Real) (B - A) at hr
      exact ⟨by dsimp only [shift]; linarith [hr.1],
        by dsimp only [shift]; linarith [hr.2]⟩
  obtain ⟨C, hchart⟩ :=
    DifferentialGeometry.Geometry.Riemannian.extChart_lip_cpt
      (I := I) p hQc (by simpa only [extChartAt_source] using hQsrc)
  have hmapQ : MapsTo (alpha ∘ shift) (uIcc (0 : Real) L) Q := by
    intro r hr
    apply hαQ
    rw [uIcc_of_le hL] at hr
    change r ∈ Icc (0 : Real) (B - A) at hr
    exact ⟨by dsimp only [shift]; linarith [hr.1],
      by dsimp only [shift]; linarith [hr.2]⟩
  have hac := AbsolutelyContinuousOnInterval.comp_lipschitzOn
    hchart hshiftAC hmapQ
  simpa only [L, shift, Function.comp_apply] using hac

omit [I.Boundaryless] [RegularSpace M] [ConnectedSpace M] in
private theorem lChart_mdiff_cpt
    (A B : Real) (hAB : A ≤ B) (alpha : Real → M) (p : M)
    (hsrc : MapsTo alpha (Icc A B) (chartAt H p).source)
    (hAC : AbsolutelyContinuousOnInterval
      (fun r ↦ extChartAt I p (alpha (A + r))) 0 (B - A)) :
    ∀ᵐ r ∂timeMeasure (B - A),
      MDifferentiableAt 𝓘(Real, Real) I alpha (A + r) := by
  let L : Real := B - A
  let f : Real → E := fun r ↦ extChartAt I p (alpha (A + r))
  have hL : 0 ≤ L := by
    simpa only [L] using sub_nonneg.mpr hAB
  have hmem : ∀ᵐ r ∂timeMeasure L, r ∈ Ioo (0 : Real) L := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdiffRaw : ∀ᵐ r ∂volume,
      r ∈ uIcc (0 : Real) L → DifferentiableAt Real f r := by
    simpa only [f, L] using
      hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hdiff : ∀ᵐ r ∂timeMeasure L, DifferentiableAt Real f r := by
    have hraw : ∀ᵐ r ∂volume.restrict (Icc (0 : Real) L),
        r ∈ uIcc (0 : Real) L → DifferentiableAt Real f r :=
      ae_mono Measure.restrict_le_self hdiffRaw
    filter_upwards [hraw, ae_restrict_mem measurableSet_Icc] with r hr hri
    exact hr (by simpa only [uIcc_of_le hL] using hri)
  filter_upwards [hdiff, hmem] with r hfr hr
  have hrIcc : r ∈ Icc (0 : Real) L := ⟨hr.1.le, hr.2.le⟩
  have hIcc : Icc (0 : Real) L ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hsrc_r : alpha (A + r) ∈ (chartAt H p).source := by
    apply hsrc
    exact ⟨le_add_of_nonneg_right hrIcc.1,
      by dsimp only [L] at hrIcc; linarith [hrIcc.2]⟩
  have htar : f r ∈ (extChartAt I p).target := by
    dsimp only [f]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc_r)
  have hfMD : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) f r := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hfr
  have hshift : MDifferentiableAt 𝓘(Real, Real) I
      (fun s ↦ alpha (A + s)) r := by
    have hpre : f ⁻¹' range I ∈ 𝓝 r :=
      Filter.mem_of_superset
        (Filter.mem_of_superset hIcc fun s hs ↦ by
          change f s ∈ (extChartAt I p).target
          dsimp only [f]
          exact (extChartAt I p).map_source (by
            rw [extChartAt_source]
            apply hsrc
            exact ⟨le_add_of_nonneg_right hs.1,
              by dsimp only [L] at hs; linarith [hs.2]⟩))
        fun _ hy ↦ extChartAt_target_subset_range p hy
    have hcomp : MDifferentiableAt 𝓘(Real, Real) I
        ((extChartAt I p).symm ∘ f) r :=
      mdifferentiableWithinAt_univ.mp
        (MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
          (x := r) (f := f) (s := Set.univ)
          (mdifferentiableWithinAt_extChartAt_symm htar)
          hfMD.mdifferentiableWithinAt (by simpa using hpre))
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hIcc] with s hs
    dsimp only [Function.comp_apply, f]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      apply hsrc
      exact ⟨le_add_of_nonneg_right hs.1,
        by dsimp only [L] at hs; linarith [hs.2]⟩)).symm
  have hsub : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (fun s : Real ↦ s - A) (A + r) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact ((hasDerivAt_id (A + r)).sub_const A).differentiableAt
  have hback : MDifferentiableAt 𝓘(Real, Real) I
      ((fun s ↦ alpha (A + s)) ∘ fun s : Real ↦ s - A) (A + r) :=
    MDifferentiableAt.comp_of_eq (x := A + r) (f := fun s : Real ↦ s - A)
      hshift hsub (by ring)
  apply hback.congr_of_eventuallyEq
  filter_upwards with s
  simp only [Function.comp_apply]
  congr 1
  ring

omit [I.Boundaryless] [RegularSpace M] [ConnectedSpace M] in
private theorem lChart_kin_ae
    (S : SolutionOn (I := I) (M := M) D) (T A B : Real)
    (hAB : A ≤ B) (alpha : Real → M) (p : M)
    (hsrc : MapsTo alpha (Icc A B) (chartAt H p).source)
    (hdiff : ∀ᵐ r ∂timeMeasure (B - A),
      MDifferentiableAt 𝓘(Real, Real) I alpha (A + r))
    (hfdiff : ∀ᵐ r ∂timeMeasure (B - A),
      DifferentiableAt Real
        (fun q ↦ extChartAt I p (alpha (A + q))) r) :
    (fun r ↦ (1 / 2 : Real) *
      (S.base.metric (T - (A + r) ^ 2)).inner (alpha (A + r))
        (lVelocity (I := I) alpha (A + r))
        (lVelocity (I := I) alpha (A + r))) =ᵐ[timeMeasure (B - A)]
      fun r ↦ inner Real
        (((1 / 2 : Real) • chartGramOp (I := I) S.family p
          (T - (A + r) ^ 2,
            extChartAt I p (alpha (A + r))))
          (deriv (fun q ↦ extChartAt I p (alpha (A + q))) r))
        (deriv (fun q ↦ extChartAt I p (alpha (A + q))) r) := by
  have hL : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hmem : ∀ᵐ r ∂timeMeasure (B - A),
      r ∈ Ioo (0 : Real) (B - A) := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hfdiff, hdiff, hmem] with r hfr hmdiff hr
  have hrcc : r ∈ Icc (0 : Real) (B - A) := ⟨hr.1.le, hr.2.le⟩
  have hcoord : HasDerivAt
      (fun q ↦ extChartAt I p (alpha (A + q)))
      (deriv (fun q ↦ extChartAt I p (alpha (A + q))) r) r :=
    hfr.hasDerivAt
  have hderiv :
      (fderiv Real ((extChartAt I p) ∘ alpha) (A + r) : Real →L[Real] E) 1 =
        deriv (fun q ↦ extChartAt I p (alpha (A + q))) r := by
    change deriv ((extChartAt I p) ∘ alpha) (A + r) = _
    rw [← deriv_comp_const_add]
    simp only [Function.comp_apply]
  have hrAB : A + r ∈ Icc A B := by
    exact ⟨le_add_of_nonneg_right hrcc.1, by linarith [hrcc.2]⟩
  have hars : alpha (A + r) ∈ (chartAt H p).source := hsrc hrAB
  have hraw :=
    raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
      (I := I) (M := M) hmdiff p hars
  rw [hderiv] at hraw
  have hinv :
      (extChartAt I p).symm (extChartAt I p (alpha (A + r))) =
        alpha (A + r) :=
    (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hars)
  rw [ContinuousLinearMap.smul_apply, real_inner_smul_left,
    chartGramOp_inner, hinv]
  have hinner := congrArg
    (fun v : TangentSpace I (alpha (A + r)) ↦
      (1 / 2 : Real) *
        (S.base.metric (T - (A + r) ^ 2)).inner (alpha (A + r)) v v)
    hraw
  simpa only [SolutionOn.family_metric] using hinner

end Topological

section Uniform

variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M] [ConnectedSpace M]

private theorem lChartH1_cpt
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T A B : Real) (hAB : A ≤ B) (alpha : Real → M) (p : M)
    {Q : Set M}
    (hAC :
      letI : PseudoMetricSpace M := lSegmentMetric S T
      AbsolutelyContinuousOnInterval alpha A B)
    (hQc : IsCompact Q)
    (hQsrc : Q ⊆ (chartAt H p).source)
    (hαQ : MapsTo alpha (Icc A B) Q)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume A B)
    (hreg : ∀ s ∈ Icc A B, T - s ^ 2 ∈ D.regular) :
    ∃ u : timeH1 E (B - A),
      EqOn u.toFun
        (fun r ↦ extChartAt I p (alpha (A + r)))
        (Icc (0 : Real) (B - A)) := by
  let L : Real := B - A
  let f : Real → E := fun r ↦ extChartAt I p (alpha (A + r))
  let τ : Real → Real := fun r ↦ T - (A + r) ^ 2
  have hL : 0 ≤ L := by
    simpa only [L] using sub_nonneg.mpr hAB
  have hsrc : MapsTo alpha (Icc A B) (chartAt H p).source :=
    fun s hs ↦ hQsrc (hαQ hs)
  have hfAC : AbsolutelyContinuousOnInterval f 0 L := by
    simpa only [f, L] using
      lChart_ac_cpt S T A B hAB alpha p hAC hQc hQsrc hαQ
  have hmdiff : ∀ᵐ r ∂timeMeasure L,
      MDifferentiableAt 𝓘(Real, Real) I alpha (A + r) := by
    simpa only [L] using
      lChart_mdiff_cpt A B hAB alpha p hsrc
        (by simpa only [f, L] using hfAC)
  have hfdiffRaw : ∀ᵐ r ∂volume,
      r ∈ uIcc (0 : Real) L → DifferentiableAt Real f r := by
    simpa only [f] using
      hfAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hfdiff : ∀ᵐ r ∂timeMeasure L, DifferentiableAt Real f r := by
    have hraw : ∀ᵐ r ∂volume.restrict (Icc (0 : Real) L),
        r ∈ uIcc (0 : Real) L → DifferentiableAt Real f r :=
      ae_mono Measure.restrict_le_self hfdiffRaw
    filter_upwards [hraw, ae_restrict_mem measurableSet_Icc] with r hr hri
    exact hr (by simpa only [uIcc_of_le hL] using hri)
  have hτc : ContinuousOn τ (Icc (0 : Real) L) := by
    exact continuousOn_const.sub
      ((continuousOn_const.add continuousOn_id).pow 2)
  have hfc : ContinuousOn f (Icc (0 : Real) L) := by
    simpa only [uIcc_of_le hL] using hfAC.continuousOn
  let J : Set Real := τ '' Icc (0 : Real) L
  let K : Set E := f '' Icc (0 : Real) L
  have hJc : IsCompact J :=
    isCompact_Icc.image_of_continuousOn hτc
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn hfc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    apply hreg (A + r)
    exact ⟨le_add_of_nonneg_right hr.1,
      by dsimp only [L] at hr; linarith [hr.2]⟩
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro z ⟨r, hr, rfl⟩
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    dsimp only [f]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      apply hsrc
      exact ⟨le_add_of_nonneg_right hr.1,
        by dsimp only [L] at hr; linarith [hr.2]⟩)
  obtain ⟨c, hc, hcLower⟩ :=
    chartGramOp_lower (I := I) hMet hJreg hJc p hKchart hKc
  have hkin :
      (fun r ↦ (1 / 2 : Real) *
        (S.base.metric (τ r)).inner (alpha (A + r))
          (lVelocity (I := I) alpha (A + r))
          (lVelocity (I := I) alpha (A + r))) =ᵐ[timeMeasure L]
        fun r ↦ (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) S.family p (τ r, f r) (deriv f r))
          (deriv f r) := by
    have hraw := lChart_kin_ae S T A B hAB alpha p hsrc
      (by simpa only [L] using hmdiff)
      (by simpa only [f, L] using hfdiff)
    simpa only [L, f, τ, ContinuousLinearMap.smul_apply,
      real_inner_smul_left] using hraw
  have hcarrier : ∀ s ∈ uIcc A B, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset
      (hreg s (by simpa only [uIcc_of_le hAB] using hs))
  obtain ⟨C, hC⟩ :=
    lScalar_lower_cpt (I := I) S hSc T A B hcarrier Q hQc
  have hLagShift : IntervalIntegrable
      (fun r ↦ lRegLag S T alpha (A + r)) volume 0 L := by
    simpa only [L, sub_self] using
      (IntervalIntegrable.comp_add_left_iff
        (f := lRegLag S T alpha) (a := A) (b := B) (c := A)).2 hLag
  have hLagInt : Integrable
      (fun r ↦ lRegLag S T alpha (A + r)) (timeMeasure L) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL] at hLagShift
    simpa only [timeMeasure] using hLagShift
  have hsqBound : ∀ᵐ r ∂timeMeasure L,
      ‖deriv f r‖ ^ 2 ≤
        (|lRegLag S T alpha (A + r)| + |C|) / (c / 2) := by
    filter_upwards [hkin, ae_restrict_mem measurableSet_Icc]
      with r hkinr hr
    have hrAB : A + r ∈ Icc A B := by
      exact ⟨le_add_of_nonneg_right hr.1,
        by dsimp only [L] at hr; linarith [hr.2]⟩
    have hgram := hcLower (τ r, f r)
      ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩ (deriv f r)
    have hpot := hC (A + r)
      (by simpa only [uIcc_of_le hAB] using hrAB)
      (alpha (A + r)) (hαQ hrAB)
    have hkinLower :
        (c / 2) * ‖deriv f r‖ ^ 2 ≤
          (1 / 2 : Real) *
            (S.base.metric (τ r)).inner (alpha (A + r))
              (lVelocity (I := I) alpha (A + r))
              (lVelocity (I := I) alpha (A + r)) := by
      calc
        (c / 2) * ‖deriv f r‖ ^ 2 =
            (1 / 2 : Real) * (c * ‖deriv f r‖ ^ 2) := by ring
        _ ≤ (1 / 2 : Real) *
            inner Real
              (chartGramOp (I := I) S.family p (τ r, f r) (deriv f r))
              (deriv f r) :=
          mul_le_mul_of_nonneg_left hgram (by norm_num)
        _ = _ := hkinr.symm
    have hco :
        (c / 2) * ‖deriv f r‖ ^ 2 ≤
          lRegLag S T alpha (A + r) - C := by
      apply hkinLower.trans
      dsimp only [lRegLag, τ]
      linarith
    apply (le_div_iff₀' (half_pos hc)).2
    exact hco.trans (by
      linarith [le_abs_self (lRegLag S T alpha (A + r)), neg_le_abs C])
  have hderMeas : AEStronglyMeasurable (deriv f) (timeMeasure L) :=
    aestronglyMeasurable_deriv f (timeMeasure L)
  have hsqMeas : AEStronglyMeasurable
      (fun r ↦ ‖deriv f r‖ ^ 2) (timeMeasure L) :=
    hderMeas.norm.pow 2
  have hdomInt : Integrable
      (fun r ↦ (|lRegLag S T alpha (A + r)| + |C|) / (c / 2))
      (timeMeasure L) :=
    (hLagInt.abs.add (integrable_const |C|)).div_const (c / 2)
  have hsqInt : Integrable
      (fun r ↦ ‖deriv f r‖ ^ 2) (timeMeasure L) :=
    hdomInt.mono_nonneg hsqMeas
      (Eventually.of_forall fun r ↦ sq_nonneg ‖deriv f r‖) hsqBound
  have hderLp : MemLp (deriv f) 2 (timeMeasure L) :=
    (memLp_two_iff_integrable_sq_norm hderMeas).2 hsqInt
  obtain ⟨u, hu, _hdu⟩ := timeH1.exists_ofAC hL f hfAC hderLp
  exact ⟨u, by simpa only [f, L] using hu⟩

end Uniform

section Metric

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RegularSpace M] [ConnectedSpace M]

omit [I.Boundaryless] in
private theorem lSeg_sq_cont
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma) :
    ContinuousOn (sqReparam gamma) (Icc a b) := by
  let alpha : Real → M := sqReparam gamma
  let topM : TopologicalSpace M := inferInstance
  letI : PseudoMetricSpace M := lSegmentMetric S T
  letI : TopologicalSpace M := topM
  have hbase : AbsolutelyContinuousOnInterval gamma (a ^ 2) (b ^ 2) :=
    hgamma.ac S T Set.univ
  have hAC : AbsolutelyContinuousOnInterval alpha a b := by
    simpa only [alpha, sqReparam, Function.comp_def] using
      AbsolutelyContinuousOnInterval.comp_sq ha hab hbase
  have hAC' := (absolutelyContinuousOnInterval_iff alpha a b).mp hAC
  have hmod (eps : Real) (heps : 0 < eps) :
      ∃ delta > 0, ∀ r ∈ Icc a b, ∀ s ∈ Icc a b,
        dist r s < delta → dist (alpha r) (alpha s) < eps := by
    obtain ⟨delta, hdelta, hacdelta⟩ := hAC' eps heps
    refine ⟨delta, hdelta, ?_⟩
    intro r hr s hs hrs
    let P : Nat → Real × Real := fun _ ↦ (r, s)
    have hP : (1, P) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
      constructor
      · intro i hi
        have hi0 : i = 0 := Nat.lt_one_iff.mp (Finset.mem_range.mp hi)
        subst i
        simpa only [uIcc_of_le hab, P] using And.intro hr hs
      · rw [Finset.range_one]
        simpa only [Finset.coe_singleton] using
          Set.pairwiseDisjoint_singleton 0
            (fun i ↦ uIoc (P i).1 (P i).2)
    have hlen :
        ∑ i ∈ Finset.range 1, dist (P i).1 (P i).2 < delta := by
      simpa only [Finset.range_one, Finset.sum_singleton, P] using hrs
    simpa only [Finset.range_one, Finset.sum_singleton, P] using
      hacdelta (1, P) hP hlen
  intro r hr
  rw [ContinuousWithinAt, Filter.tendsto_def]
  intro V hV
  obtain ⟨eps, heps, hepsub⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨delta, hdelta, hmoddelta⟩ := hmod eps heps
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨Metric.ball r delta, Metric.ball_mem_nhds r hdelta, ?_⟩
  intro s hs
  have hout := hmoddelta r hr s hs.2 (by
    simpa only [Metric.mem_ball, dist_comm] using hs.1)
  apply hepsub
  simpa only [Metric.mem_ball, dist_comm] using hout

omit [I.Boundaryless] in
private theorem lSeg_cpt_cover
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (ha : 0 ≤ a) (hab : a ≤ b) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma) :
    ∃ (m : Nat) (t : Fin (m + 1) → Real) (p : Fin m → M)
      (Q : Fin m → Set M),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i : Fin m, t i.castSucc ≤ t i.succ) ∧
      (∀ i : Fin m, Icc (t i.castSucc) (t i.succ) ⊆ Icc a b) ∧
      (∀ i : Fin m, IsCompact (Q i)) ∧
      (∀ i : Fin m, Q i ⊆ (chartAt H (p i)).source) ∧
      (∀ i : Fin m, MapsTo (sqReparam gamma)
        (Icc (t i.castSucc) (t i.succ)) (Q i)) := by
  classical
  letI : PseudoMetricSpace M := lSegmentMetric S T
  have hcont : ContinuousOn (sqReparam gamma) (Icc a b) :=
    lSeg_sq_cont (I := I) S T a b ha hab gamma hgamma
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ :=
    DifferentialGeometry.Geometry.exists_cpt_split (H := H) hab hcont
  let t : Fin (m + 1) → Real := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b :=
    congrArg Subtype.val (hqm m le_rfl)
  choose p Q hQc hQsrc hαInt using fun i : Fin m ↦ hpieces i
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hsub (i : Fin m) :
      Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    intro s hs
    exact ⟨(q i.castSucc).property.1.trans hs.1,
      hs.2.trans (q i.succ).property.2⟩
  have hmapInt (i : Fin m) : MapsTo (sqReparam gamma)
      (Icc (t i.castSucc) (t i.succ)) (interior (Q i)) := by
    simpa only [t] using hαInt i
  have hmapQ (i : Fin m) : MapsTo (sqReparam gamma)
      (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    fun s hs ↦ interior_subset (hmapInt i hs)
  exact ⟨m, t, p, Q, ht0, htmono, htlast, hseg, hsub, hQc, hQsrc,
    hmapQ⟩

/-- A finite-action same-clock segment has finitely many fixed-chart
`timeH1` representatives after square-root reparameterization. -/
theorem lSegChartH1_fin
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (m : Nat) (t : Fin (m + 1) → Real) (p : Fin m → M)
      (u : (i : Fin m) → timeH1 E (lSegLen t i)),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i, MapsTo (sqReparam gamma)
        (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      ∀ i, EqOn (u i).toFun
        (fun r ↦ extChartAt I (p i)
          (sqReparam gamma (t i.castSucc + r)))
        (Icc (0 : Real) (lSegLen t i)) := by
  classical
  let alpha : Real → M := sqReparam gamma
  have hLag : IntervalIntegrable (lRegLag S T alpha) volume a b := by
    simpa only [alpha] using lSeg_reg_int (I := I) S T a b ha hab gamma hgamma
  obtain ⟨m, t, p, Q, ht0, htmono, htlast, hseg, hsub, hQc, hQsrc,
      hmapQ⟩ :=
    lSeg_cpt_cover (I := I) S T a b ha hab gamma hgamma
  have hACi (i : Fin m) :
      letI : PseudoMetricSpace M := lSegmentMetric S T
      AbsolutelyContinuousOnInterval (sqReparam gamma)
        (t i.castSucc) (t i.succ) := by
    have hAC := lSeg_sq_ac (I := I) S T a b ha hab gamma hgamma
    letI : PseudoMetricSpace M := lSegmentMetric S T
    change AbsolutelyContinuousOnInterval (sqReparam gamma) a b at hAC
    exact hAC.mono (by
      simpa only [uIcc_of_le (hseg i), uIcc_of_le hab] using hsub i)
  have hLagi (i : Fin m) : IntervalIntegrable (lRegLag S T alpha) volume
      (t i.castSucc) (t i.succ) :=
    hLag.mono_set (by
      simpa only [uIcc_of_le (hseg i), uIcc_of_le hab] using hsub i)
  have hregi (i : Fin m) : ∀ s ∈ Icc (t i.castSucc) (t i.succ),
      T - s ^ 2 ∈ D.regular := fun s hs ↦ hreg s (hsub i hs)
  choose u hu using fun i : Fin m ↦
    lChartH1_cpt (I := I) S hMet hSc T
      (t i.castSucc) (t i.succ) (hseg i) alpha (p i)
      (by simpa only [alpha] using hACi i) (hQc i) (hQsrc i)
      (by simpa only [alpha] using hmapQ i) (hLagi i) (hregi i)
  refine ⟨m, t, p, fun i ↦ ?_, ht0, htmono, htlast, ?_, ?_⟩
  · simpa only [lSegLen] using u i
  · intro i
    exact fun s hs ↦ hQsrc i (hmapQ i hs)
  · intro i
    simpa only [lSegLen, alpha] using hu i

/-- On a regular nonnegative square-root-time slab, finite-action same-clock
segments and global `C¹` regularized competitors have the same infimum. -/
theorem lSegValue_eq_reg
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y =
      (lRegCostC1 S T a b x y : WithTop Real) := by
  let costs : Set Real := {r | ∃ alpha : Real → M,
    ContMDiff 𝓘(Real, Real) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r}
  have habSq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha (ha.trans hab)).2 hab
  have hbdd : BddBelow costs := by
    refine ⟨-(2 * K / 3) *
      (b ^ 2 * Real.sqrt (b ^ 2) - a ^ 2 * Real.sqrt (a ^ 2)), ?_⟩
    intro r hr
    rcases hr with ⟨alpha, halpha, _hxa, _hyb, rfl⟩
    have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab alpha
      halpha.contMDiffOn hreg
    have hseg := lSegCurve_sqrt (I := I) S T Set.univ a b ha hab alpha
      halpha hLag (by simp)
    have hlow := lLength_lower S T (a ^ 2) (b ^ 2) K
      (sq_nonneg a) habSq (sqrtReparam alpha)
      (fun tau htau ↦ hR tau htau (sqrtReparam alpha tau)) hseg.2.2.1
    rw [lLength_sqrt_Icc (I := I) S T alpha a b ha hab] at hlow
    exact hlow
  have hrev :
      (lRegCostC1 S T a b x y : WithTop Real) ≤
        lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y := by
    apply le_lSegValue (I := I) S T Set.univ (a ^ 2) (b ^ 2) x y
      (lRegCostC1 S T a b x y : WithTop Real)
    intro gamma hgamma hga hgb
    apply WithTop.coe_le_coe.2
    let alpha : Real → M := sqReparam gamma
    obtain ⟨m, t, p, u, ht0, htmono, htlast, hsrc, hrep⟩ :=
      lSegChartH1_fin (I := I) S hMet hSc T a b ha hab gamma hgamma hreg
    obtain ⟨beta, _v, hbeta, hbetaa, hbetab, _hsrcBeta, _hrepBeta,
        _hu, _hunif, hact⟩ :=
      lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p
        alpha u hsrc hrep hreg
    have hAlphaA : alpha a = x := by
      simpa only [alpha, sqReparam] using hga
    have hAlphaB : alpha b = y := by
      simpa only [alpha, sqReparam] using hgb
    have hcost :
        lRegCostC1 S T a b x y ≤ lRegAction S T alpha a b := by
      apply ge_of_tendsto hact
      exact Eventually.of_forall fun n ↦
        lRegCostC1_le_bdd (I := I) S T a b x y
          (by simpa only [costs] using hbdd) (beta n) (hbeta n)
          ((hbetaa n).trans hAlphaA) ((hbetab n).trans hAlphaB)
    have hlen :
        lLength S T gamma (a ^ 2) (b ^ 2) =
          lRegAction S T alpha a b := by
      simpa only [alpha, Real.sqrt_sq ha, Real.sqrt_sq (ha.trans hab)] using
        lLength_reg_ae (I := I) S T gamma (a ^ 2) (b ^ 2)
          (sq_nonneg a) (sq_nonneg b)
    exact hcost.trans_eq hlen.symm
  exact le_antisymm
    (lSegValue_le_reg (I := I) S hMet hSc T K a b ha hab hR hreg x y
      alpha0 halpha0 h0a h0b)
    hrev

/-- A single finite-action endpoint segment supplies the nonempty global `C¹`
competitor needed to identify the same-clock value with the regularized cost. -/
theorem lSegValue_eq_of_seg
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (gamma : Real → M)
    (hgamma : IsLSegCurve S T Set.univ (a ^ 2) (b ^ 2) gamma)
    (hga : gamma (a ^ 2) = x) (hgb : gamma (b ^ 2) = y) :
    lSegValue S T Set.univ (a ^ 2) (b ^ 2) x y =
      (lRegCostC1 S T a b x y : WithTop Real) := by
  let alpha : Real → M := sqReparam gamma
  obtain ⟨m, t, p, u, ht0, htmono, htlast, hsrc, hrep⟩ :=
    lSegChartH1_fin (I := I) S hMet hSc T a b ha hab gamma hgamma hreg
  obtain ⟨beta, _v, hbeta, hbetaa, hbetab, _hsrcBeta, _hrepBeta,
      _hu, _hunif, _hact⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p
      alpha u hsrc hrep hreg
  have hAlphaA : alpha a = x := by
    simpa only [alpha, sqReparam] using hga
  have hAlphaB : alpha b = y := by
    simpa only [alpha, sqReparam] using hgb
  exact lSegValue_eq_reg (I := I) S hMet hSc T K a b ha hab hR hreg x y
    (beta 0) (hbeta 0) ((hbetaa 0).trans hAlphaA) ((hbetab 0).trans hAlphaB)

end Metric

end DifferentialGeometry.PDE.RicciFlow.Perelman
