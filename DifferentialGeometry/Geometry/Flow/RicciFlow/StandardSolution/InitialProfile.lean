import DifferentialGeometry.Geometry.Flow.RicciFlow.StandardSolution.Defs
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Metric
open Bundle
open Filter
open scoped Manifold ContDiff

private def capCutoff : ContDiffBump (0 : Real) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- Radius profile of the round curvature-`1 / 4` cap. -/
def roundRadius (r : Real) : Real :=
  2 * Real.sin (r / 2)

/-- Radius profile of the round cylinder of radius two. -/
def cylRadius (_r : Real) : Real :=
  2

/-- A globally smooth radius-profile join which is exactly round near zero and
exactly cylindrical outside radius two.  Curvature inequalities for this
particular join are not asserted. -/
def capJoin (r : Real) : Real :=
  capCutoff r * roundRadius r + (1 - capCutoff r) * cylRadius r

/-- The cap-join profile is globally smooth. -/
theorem capJoin_smooth : ContDiff ℝ (⊤ : ℕ∞) capJoin := by
  unfold capJoin roundRadius cylRadius
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (capCutoff : ℝ → ℝ) :=
    capCutoff.contDiff
  have hround : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => 2 * Real.sin (r / 2)) := by
    fun_prop
  have hone : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have htwo : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (2 : ℝ)) := contDiff_const
  exact (hcut.mul hround).add ((hone.sub hcut).mul htwo)

/-- On the unit neighborhood of the tip, `capJoin` is the round profile. -/
theorem capJoin_round {r : Real} (hr : dist r 0 <= 1) :
    capJoin r = roundRadius r := by
  have hmem : r ∈ closedBall (0 : Real) capCutoff.rIn := by
    simpa [capCutoff] using hr
  have hcut : capCutoff r = 1 := capCutoff.one_of_mem_closedBall hmem
  simp [capJoin, hcut]

/-- Outside radius two, `capJoin` is the cylindrical profile. -/
theorem capJoin_cyl {r : Real} (hr : 2 <= dist r 0) :
    capJoin r = cylRadius r := by
  have hcut : capCutoff r = 0 := capCutoff.zero_of_le_dist (by
    simpa [capCutoff] using hr)
  simp [capJoin, hcut]

/-- The cap-join profile closes at the tip. -/
@[simp] theorem capJoin_zero : capJoin 0 = 0 := by
  rw [capJoin_round (by simp)]
  simp [roundRadius]

private def capWidth : Real := 2 * (Real.pi - 1)

private theorem capWidth_pos : 0 < capWidth := by
  unfold capWidth
  nlinarith [Real.pi_gt_three]

/-- Smooth nonincreasing slope used by the canonical standard-cap phase. -/
def capSlope (r : Real) : Real :=
  1 - Real.smoothTransition ((r - 1) / capWidth)

/-- The canonical cap slope is globally smooth. -/
theorem capSlope_smooth : ContDiff Real (⊤ : ℕ∞) capSlope := by
  unfold capSlope capWidth
  fun_prop

/-- The canonical cap slope is exactly one on the tip side. -/
theorem capSlope_one {r : Real} (hr : r ≤ 1) : capSlope r = 1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) capWidth_pos.le

/-- The canonical cap slope vanishes past its transition interval. -/
theorem capSlope_zero {r : Real} (hr : 2 * Real.pi - 1 ≤ r) : capSlope r = 0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ capWidth_pos]
    unfold capWidth
    linarith

/-- The canonical cap slope takes values in the unit interval. -/
theorem capSlope_mem (r : Real) : capSlope r ∈ Set.Icc (0 : Real) 1 := by
  constructor
  · unfold capSlope
    linarith [Real.smoothTransition.le_one ((r - 1) / capWidth)]
  · unfold capSlope
    linarith [Real.smoothTransition.nonneg ((r - 1) / capWidth)]

/-- The canonical cap slope is nonincreasing. -/
theorem capSlope_anti : Antitone capSlope := by
  intro a b hab
  unfold capSlope
  have harg : (a - 1) / capWidth ≤ (b - 1) / capWidth := by
    rw [div_le_div_iff_of_pos_right capWidth_pos]
    linarith
  linarith [Real.smoothTransition.monotone harg]

/-- Integrated phase of the canonical standard-cap profile. -/
def capPhase (r : Real) : Real :=
  ∫ s in (0 : Real)..r, capSlope s

/-- The derivative of the integrated cap phase is its prescribed slope. -/
theorem capPhase_deriv : deriv capPhase = capSlope := by
  funext r
  exact (intervalIntegral.integral_hasDerivAt_right
    (capSlope_smooth.continuous.intervalIntegrable 0 r)
    capSlope_smooth.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    capSlope_smooth.continuous.continuousAt).deriv

/-- The integrated cap phase is globally smooth. -/
theorem capPhase_smooth : ContDiff Real (⊤ : ℕ∞) capPhase := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · exact intervalIntegral.differentiable_integral_of_continuous capSlope_smooth.continuous
  · rw [capPhase_deriv]
    exact capSlope_smooth

/-- The integrated cap phase is globally concave. -/
theorem capPhase_concave : ConcaveOn Real Set.univ capPhase := by
  apply Antitone.concaveOn_univ_of_deriv (capPhase_smooth.differentiable (by simp))
  rw [capPhase_deriv]
  exact capSlope_anti

/-- The integrated cap phase agrees with radial distance near the tip. -/
theorem capPhase_id {r : Real} (hr : r ≤ 1) : capPhase r = r := by
  unfold capPhase
  calc
    (∫ x in (0 : Real)..r, capSlope x) = ∫ _x in (0 : Real)..r, (1 : Real) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply capSlope_one
      rcases Set.mem_uIcc.mp hx with hx | hx
      · exact hx.2.trans hr
      · exact hx.2.trans zero_le_one
    _ = r := by simp

/-- Canonical smooth radius obtained from the concave cap phase. -/
def stdRadius (r : Real) : Real :=
  2 * Real.sin (capPhase r / 2)

/-- The canonical standard radius is globally smooth. -/
theorem stdRadius_smooth : ContDiff Real (⊤ : ℕ∞) stdRadius := by
  unfold stdRadius
  have hhalf : ContDiff Real (⊤ : ℕ∞) (fun r : Real => capPhase r / 2) := by
    simpa only [div_eq_mul_inv] using
      capPhase_smooth.mul (contDiff_const :
        ContDiff Real (⊤ : ℕ∞) (fun _ : Real => (2 : Real)⁻¹))
  exact contDiff_const.mul (Real.contDiff_sin.comp hhalf)

/-- The canonical standard radius is exactly round near the tip. -/
theorem stdRadius_round {r : Real} (hr : r ≤ 1) : stdRadius r = roundRadius r := by
  simp only [stdRadius, roundRadius, capPhase_id hr]

private theorem smoothTrans_symm (x : Real) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    ne_of_gt (Real.smoothTransition.pos_denom x)
  rw [show 1 - (1 - x) = x by ring]
  calc
    expNegInvGlue (1 - x) / (expNegInvGlue (1 - x) + expNegInvGlue x) =
        expNegInvGlue (1 - x) / (expNegInvGlue x + expNegInvGlue (1 - x)) := by
      rw [add_comm]
    _ = 1 - expNegInvGlue x /
        (expNegInvGlue x + expNegInvGlue (1 - x)) := by
      field_simp [hden]
      ring

private theorem smoothTrans_half :
    (∫ x in (0 : Real)..1, Real.smoothTransition x) = 1 / 2 := by
  have hcont : IntervalIntegrable Real.smoothTransition MeasureTheory.volume 0 1 :=
    Real.smoothTransition.continuous.intervalIntegrable 0 1
  have hchange :
      (∫ x in (0 : Real)..1, Real.smoothTransition (1 - x)) =
        ∫ x in (0 : Real)..1, Real.smoothTransition x := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := Real.smoothTransition) (a := (0 : Real)) (b := 1) 1)
  have hsymm :
      (∫ x in (0 : Real)..1, Real.smoothTransition (1 - x)) =
        ∫ x in (0 : Real)..1, (1 - Real.smoothTransition x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact smoothTrans_symm x
  have heq :
      (∫ x in (0 : Real)..1, (1 - Real.smoothTransition x)) =
        ∫ x in (0 : Real)..1, Real.smoothTransition x :=
    hsymm.symm.trans hchange
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ : Real => (1 : Real))
      MeasureTheory.volume 0 1) hcont] at heq
  norm_num at heq ⊢
  linarith

/-- The radial coordinate at which the canonical phase becomes constant. -/
def capEnd : Real := 2 * Real.pi - 1

private theorem capEnd_pos : 0 < capEnd := by
  unfold capEnd
  nlinarith [Real.pi_gt_three]

/-- The canonical cap phase reaches exactly `π` at the end of the transition. -/
theorem capPhase_end : capPhase capEnd = Real.pi := by
  have hcont := capSlope_smooth.continuous
  have hfirst : (∫ x in (0 : Real)..1, capSlope x) = 1 := by
    calc
      (∫ x in (0 : Real)..1, capSlope x) =
          ∫ _x in (0 : Real)..1, (1 : Real) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply capSlope_one
        rcases Set.mem_uIcc.mp hx with hx | hx
        · exact hx.2
        · exact hx.2.trans zero_le_one
      _ = 1 := by norm_num
  have honeSub :
      (∫ x in (0 : Real)..1, (1 - Real.smoothTransition x)) = 1 / 2 := by
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : Real => (1 : Real))
        MeasureTheory.volume 0 1)
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)]
    rw [smoothTrans_half]
    norm_num
  have hend : capEnd - 1 = capWidth := by
    unfold capEnd capWidth
    ring
  have hsecond : (∫ x in (1 : Real)..capEnd, capSlope x) = Real.pi - 1 := by
    calc
      (∫ x in (1 : Real)..capEnd, capSlope x) =
          ∫ x in (1 : Real)..capEnd,
            (fun y : Real => 1 - Real.smoothTransition (y / capWidth)) (x - 1) := by
        rfl
      _ = ∫ y in (0 : Real)..(capEnd - 1),
            (1 - Real.smoothTransition (y / capWidth)) := by
        simpa using
          (intervalIntegral.integral_comp_sub_right
            (f := fun y : Real => 1 - Real.smoothTransition (y / capWidth))
            (a := (1 : Real)) (b := capEnd) 1)
      _ = capWidth * ∫ y in (0 : Real)..1,
            (1 - Real.smoothTransition y) := by
        rw [hend]
        simpa [smul_eq_mul, capWidth_pos.ne'] using
          (intervalIntegral.integral_comp_div
            (f := fun y : Real => 1 - Real.smoothTransition y)
            (a := (0 : Real)) (b := capWidth) capWidth_pos.ne')
      _ = Real.pi - 1 := by
        rw [honeSub]
        unfold capWidth
        ring
  unfold capPhase
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 capEnd)]
  rw [hfirst, hsecond]
  ring

/-- Past the transition, the canonical cap phase is exactly constant `π`. -/
theorem capPhase_const {r : Real} (hr : capEnd ≤ r) : capPhase r = Real.pi := by
  have hcont := capSlope_smooth.continuous
  have hzero : (∫ x in capEnd..r, capSlope x) = 0 := by
    calc
      (∫ x in capEnd..r, capSlope x) = ∫ _x in capEnd..r, (0 : Real) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply capSlope_zero
        rw [Set.uIcc_of_le hr] at hx
        exact hx.1
      _ = 0 := by simp
  unfold capPhase
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 capEnd) (hcont.intervalIntegrable capEnd r)]
  rw [show (∫ x in (0 : Real)..capEnd, capSlope x) = Real.pi from capPhase_end,
    hzero, add_zero]

/-- The canonical cap phase is nondecreasing. -/
theorem capPhase_mono : Monotone capPhase := by
  apply monotone_of_deriv_nonneg (capPhase_smooth.differentiable (by simp))
  intro r
  rw [capPhase_deriv]
  exact (capSlope_mem r).1

/-- On the nonnegative radial axis, the canonical phase lies in `[0, π]`. -/
theorem capPhase_mem {r : Real} (hr : 0 ≤ r) : capPhase r ∈ Set.Icc (0 : Real) Real.pi := by
  constructor
  · simpa [capPhase] using capPhase_mono hr
  · by_cases hre : r ≤ capEnd
    · simpa [capPhase_end] using capPhase_mono hre
    · rw [capPhase_const (le_of_not_ge hre)]

/-- The canonical standard radius is exactly cylindrical past the transition. -/
theorem stdRadius_cyl {r : Real} (hr : capEnd ≤ r) : stdRadius r = cylRadius r := by
  simp [stdRadius, cylRadius, capPhase_const hr]

/-- The cap phase has the prescribed slope at every radius. -/
theorem capPhase_hasDeriv (r : Real) : HasDerivAt capPhase (capSlope r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    (capSlope_smooth.continuous.intervalIntegrable 0 r)
    capSlope_smooth.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    capSlope_smooth.continuous.continuousAt

/-- Derivative formula for the canonical standard radius. -/
theorem stdRadius_hasDeriv (r : Real) :
    HasDerivAt stdRadius (Real.cos (capPhase r / 2) * capSlope r) r := by
  have hphase := (capPhase_hasDeriv r).div_const 2
  have hsin := hphase.sin.const_mul 2
  convert hsin using 1; ring

/-- Pointwise derivative formula for the canonical standard radius. -/
theorem stdRadius_deriv (r : Real) :
    deriv stdRadius r = Real.cos (capPhase r / 2) * capSlope r :=
  (stdRadius_hasDeriv r).deriv

/-- On the nonnegative axis, the standard-radius derivative lies in `[0, 1]`. -/
theorem stdRadius_dmem {r : Real} (hr : 0 ≤ r) :
    deriv stdRadius r ∈ Set.Icc (0 : Real) 1 := by
  rw [stdRadius_deriv]
  have hp := capPhase_mem hr
  have hcos0 : 0 ≤ Real.cos (capPhase r / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hp.1, Real.pi_pos], by nlinarith [hp.2]⟩
  have hcos1 : Real.cos (capPhase r / 2) ≤ 1 := Real.cos_le_one _
  have hs := capSlope_mem r
  constructor
  · exact mul_nonneg hcos0 hs.1
  · calc
      Real.cos (capPhase r / 2) * capSlope r ≤ 1 * capSlope r :=
        mul_le_mul_of_nonneg_right hcos1 hs.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hs.2 zero_le_one
      _ = 1 := mul_one 1

private theorem stdDeriv_anti :
    AntitoneOn (deriv stdRadius) (Set.Ici (0 : Real)) := by
  intro a ha b hb hab
  rw [stdRadius_deriv, stdRadius_deriv]
  have hpa := capPhase_mem ha
  have hpb := capPhase_mem hb
  have hphase : capPhase a / 2 ≤ capPhase b / 2 := by
    exact div_le_div_of_nonneg_right (capPhase_mono hab) (by norm_num)
  have hcos : Real.cos (capPhase b / 2) ≤ Real.cos (capPhase a / 2) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (by nlinarith [hpa.1]) (by nlinarith [hpb.2, Real.pi_pos]) hphase
  have hcos0 : 0 ≤ Real.cos (capPhase a / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hpa.1, Real.pi_pos], by nlinarith [hpa.2]⟩
  exact mul_le_mul hcos (capSlope_anti hab) (capSlope_mem b).1 hcos0

/-- The canonical standard radius is concave on the nonnegative radial axis. -/
theorem stdRadius_concave : ConcaveOn Real (Set.Ici (0 : Real)) stdRadius := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    stdRadius_smooth.continuous.continuousOn
    ((stdRadius_smooth.differentiable (by simp)).differentiableOn.mono interior_subset)
  exact stdDeriv_anti.mono interior_subset

/-- The canonical standard radius is positive away from the tip. -/
theorem stdRadius_pos {r : Real} (hr : 0 < r) : 0 < stdRadius r := by
  have hphase0 : 0 < capPhase r := by
    by_cases hr1 : r ≤ 1
    · rw [capPhase_id hr1]
      exact hr
    · have hmono := capPhase_mono (le_of_not_ge hr1)
      rw [capPhase_id le_rfl] at hmono
      linarith
  have hp := capPhase_mem hr.le
  have hsin : 0 < Real.sin (capPhase r / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith [hp.2, Real.pi_pos]⟩
  unfold stdRadius
  positivity

/-- Positive radial axis used by the punctured standard cap. -/
def posRay : TopologicalSpace.Opens Real :=
  ⟨Set.Ioi 0, isOpen_Ioi⟩

/-- Unit two-sphere used in the polar standard-cap model. -/
abbrev StdSphere := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1

/-- Positive-radius polar cylinder underlying the standard cap away from its tip. -/
abbrev StdCyl := posRay × StdSphere

private abbrev StdCylModel := 𝓘(Real, Real).prod (𝓡 2)

private local instance posRayLoc : LocallyCompactSpace posRay :=
  posRay.2.locallyCompactSpace

private local instance posRaySigma : SigmaCompactSpace posRay :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

private local instance sphereDim :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private local instance stdCylSigma : SigmaCompactSpace StdCyl := inferInstance

private noncomputable def realMetric :
    SmoothRiemannianMetric 𝓘(Real, Real) Real where
  inner := (riemannianMetricVectorSpace Real).inner
  symm := (riemannianMetricVectorSpace Real).symm
  pos := (riemannianMetricVectorSpace Real).pos
  isVonNBounded := (riemannianMetricVectorSpace Real).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace Real).contMDiff.of_le le_top

private noncomputable def rayMetric :
    SmoothRiemannianMetric 𝓘(Real, Real) posRay :=
  realMetric.restrictOpen posRay

private noncomputable def stdCylInner (x : StdCyl) :
    TangentSpace StdCylModel x →L[Real]
      TangentSpace StdCylModel x →L[Real] Real :=
  localPullInner (I := StdCylModel) (J := 𝓘(Real, Real)) rayMetric Prod.fst x +
    (stdRadius (x.1 : Real)) ^ 2 •
      localPullInner (I := StdCylModel) (J := 𝓡 2)
        (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) Prod.snd x

private theorem stdCylInner_symm (x : StdCyl)
    (v w : TangentSpace StdCylModel x) :
    stdCylInner x v w = stdCylInner x w v := by
  simp only [stdCylInner, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, localPullInner_apply,
    mfderiv_fst, mfderiv_snd]
  change rayMetric.inner x.1 v.1 w.1 +
      stdRadius (x.1 : Real) ^ 2 *
        (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x.2 v.2 w.2 =
    rayMetric.inner x.1 w.1 v.1 +
      stdRadius (x.1 : Real) ^ 2 *
        (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x.2 w.2 v.2
  rw [rayMetric.symm,
    (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm]

private theorem stdCylInner_pos (x : StdCyl)
    (v : TangentSpace StdCylModel x) (hv : v ≠ 0) :
    0 < stdCylInner x v v := by
  simp only [stdCylInner, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, localPullInner_apply,
    mfderiv_fst, mfderiv_snd]
  change 0 < rayMetric.inner x.1 v.1 v.1 +
    stdRadius (x.1 : Real) ^ 2 *
      (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x.2 v.2 v.2
  have hfac : 0 < stdRadius (x.1 : Real) ^ 2 :=
    sq_pos_of_pos (stdRadius_pos x.1.property)
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hv2
      apply hv
      exact Prod.ext hv1 hv2
    have hzero : rayMetric.inner x.1 v.1 v.1 = 0 := by
      rw [hv1]
      exact
        (rayMetric.inner x.1
          (0 : TangentSpace _ x.1)).map_zero
    rw [hzero, zero_add]
    exact mul_pos hfac
      ((Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).pos x.2 v.2 hv2)
  · have hang :
        0 ≤ stdRadius (x.1 : Real) ^ 2 *
          (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x.2 v.2 v.2 := by
      have hround :
          0 ≤ (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
            (n := 2)).inner x.2 v.2 v.2 := by
        by_cases hv2 : v.2 = 0
        · rw [hv2]
          exact le_of_eq
            (((Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
              (n := 2)).inner x.2
              (0 : TangentSpace (𝓡 2) x.2)).map_zero.symm)
        · exact ((Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
            (n := 2)).pos x.2 v.2 hv2).le
      exact mul_nonneg hfac.le hround
    exact add_pos_of_pos_of_nonneg (rayMetric.pos x.1 v.1 hv1) hang

private theorem stdFactor_smooth :
    ContMDiff StdCylModel 𝓘(Real, Real) ∞
      (fun x : StdCyl => stdRadius (x.1 : Real) ^ 2) := by
  have hval : ContMDiff StdCylModel 𝓘(Real, Real) ∞
      (fun x : StdCyl => (x.1 : Real)) :=
    (contMDiff_subtype_val (I := 𝓘(Real, Real)) (U := posRay)).comp contMDiff_fst
  exact (stdRadius_smooth.contMDiff.comp hval).pow 2

private theorem stdCylInner_smooth :
    ContMDiff StdCylModel
      (StdCylModel.prod 𝓘(Real,
        (Real × EuclideanSpace Real (Fin 2)) →L[Real]
          (Real × EuclideanSpace Real (Fin 2)) →L[Real] Real)) ∞
      (fun x : StdCyl =>
        TotalSpace.mk' ((Real × EuclideanSpace Real (Fin 2)) →L[Real]
          (Real × EuclideanSpace Real (Fin 2)) →L[Real] Real)
          x (stdCylInner x)) := by
  exact
    (localPull_smooth (I := StdCylModel) (J := 𝓘(Real, Real))
      rayMetric Prod.fst contMDiff_fst).add_section
      (I := StdCylModel)
      (F := (Real × EuclideanSpace Real (Fin 2)) →L[Real]
        (Real × EuclideanSpace Real (Fin 2)) →L[Real] Real)
      (V := fun x : StdCyl ↦
        TangentSpace StdCylModel x →L[Real]
          TangentSpace StdCylModel x →L[Real] Real)
      (stdFactor_smooth.smul_section
        (I := StdCylModel)
        (F := (Real × EuclideanSpace Real (Fin 2)) →L[Real]
          (Real × EuclideanSpace Real (Fin 2)) →L[Real] Real)
        (V := fun x : StdCyl ↦
          TangentSpace StdCylModel x →L[Real]
            TangentSpace StdCylModel x →L[Real] Real)
        (localPull_smooth (I := StdCylModel) (J := 𝓡 2)
          (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          Prod.snd contMDiff_snd))

/-- Smooth warped metric `dr² + stdRadius(r)² g_{S²}` away from the cap tip. -/
noncomputable def stdCylMetric : SmoothRiemannianMetric StdCylModel StdCyl where
  inner := stdCylInner
  symm := stdCylInner_symm
  pos := stdCylInner_pos
  isVonNBounded x := Geometry.posDef_isVonNBounded
    (E := Real × EuclideanSpace Real (Fin 2)) (stdCylInner x) (stdCylInner_pos x)
  contMDiff := stdCylInner_smooth

/-- Evaluation formula for the punctured standard-cap metric. -/
theorem stdCylMetric_inner (x : StdCyl) (v w : TangentSpace StdCylModel x) :
    stdCylMetric.inner x v w =
      rayMetric.inner x.1 v.1 w.1 + stdRadius (x.1 : Real) ^ 2 *
        (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
          (n := 2)).inner x.2 v.2 w.2 := by
  simp only [stdCylMetric, stdCylInner, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, localPullInner_apply,
    mfderiv_fst, mfderiv_snd]
  change rayMetric.inner x.1 v.1 w.1 + stdRadius (x.1 : Real) ^ 2 *
      (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
        (n := 2)).inner x.2 v.2 w.2 =
    rayMetric.inner x.1 v.1 w.1 + stdRadius (x.1 : Real) ^ 2 *
      (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
        (n := 2)).inner x.2 v.2 w.2
  rfl

/-- The exact round-cylinder product metric used on the outer end. -/
noncomputable def stdEndMetric : SmoothRiemannianMetric StdCylModel StdCyl :=
  prodMetric rayMetric
    (scaleMetric 4 (by norm_num)
      (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))

/-- Evaluation formula for the exact outer round-cylinder metric. -/
theorem stdEndMetric_inner (x : StdCyl) (v w : TangentSpace StdCylModel x) :
    stdEndMetric.inner x v w =
      rayMetric.inner x.1 v.1 w.1 + 4 *
        (Geometry.roundMetric (E := EuclideanSpace Real (Fin 3))
          (n := 2)).inner x.2 v.2 w.2 := by
  rw [stdEndMetric, prodMetric_inner, scaleMetric_inner]

/-- The punctured standard-cap metric is exactly cylindrical past `capEnd`. -/
theorem stdCyl_end {x : StdCyl} (hx : capEnd ≤ (x.1 : Real))
    (v w : TangentSpace StdCylModel x) :
    stdCylMetric.inner x v w = stdEndMetric.inner x v w := by
  rw [stdCylMetric_inner, stdEndMetric_inner, stdRadius_cyl hx]
  norm_num [cylRadius]

/-- Radial sectional-curvature coefficient predicted by the warped formula. -/
noncomputable def stdRadCurv (r : Real) : Real :=
  -deriv (deriv stdRadius) r / stdRadius r

/-- Tangential sectional-curvature coefficient predicted by the warped formula. -/
noncomputable def stdTanCurv (r : Real) : Real :=
  (1 - (deriv stdRadius r) ^ 2) / stdRadius r ^ 2

/-- The radial warped-curvature coefficient is nonnegative away from the tip. -/
theorem stdRadCurv_nonneg {r : Real} (hr : 0 < r) : 0 ≤ stdRadCurv r := by
  have hanti : AntitoneOn (deriv stdRadius) (Set.Ioi 0) :=
    stdDeriv_anti.mono (by
      intro x hx
      exact Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)
  have hsecond := hanti.derivWithin_nonpos (x := r)
  rw [derivWithin_of_mem_nhds (Ioi_mem_nhds hr)] at hsecond
  exact div_nonneg (neg_nonneg.mpr hsecond) (stdRadius_pos hr).le

/-- The tangential warped-curvature coefficient is nonnegative away from the tip. -/
theorem stdTanCurv_nonneg {r : Real} (hr : 0 < r) : 0 ≤ stdTanCurv r := by
  have hd := stdRadius_dmem hr.le
  have hsq : (deriv stdRadius r) ^ 2 ≤ 1 := by
    nlinarith [hd.1, hd.2]
  exact div_nonneg (sub_nonneg.mpr hsq) (sq_nonneg _)

/-- First derivative of the standard radius on the exact round-cap region. -/
theorem stdRadius_dround {r : Real} (hr : r ≤ 1) :
    deriv stdRadius r = Real.cos (r / 2) := by
  rw [stdRadius_deriv, capPhase_id hr, capSlope_one hr, mul_one]

/-- Second derivative of the standard radius inside the exact round-cap region. -/
theorem stdRadius_ddround {r : Real} (hr : r < 1) :
    deriv (deriv stdRadius) r = -Real.sin (r / 2) / 2 := by
  have heq :
      (fun x : Real => deriv stdRadius x) =ᶠ[nhds r]
        (fun x : Real => Real.cos (x / 2)) := by
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact stdRadius_dround hx.le
  rw [heq.deriv_eq]
  convert (Real.hasDerivAt_cos (r / 2)).comp r
    ((hasDerivAt_id r).div_const 2) |>.deriv using 1
  all_goals ring

/-- First derivative of the standard radius on the exact cylindrical region. -/
theorem stdRadius_dcyl {r : Real} (hr : capEnd ≤ r) :
    deriv stdRadius r = 0 := by
  rw [stdRadius_deriv, capSlope_zero (by simpa [capEnd] using hr), mul_zero]

/-- Second derivative of the standard radius inside the exact cylindrical region. -/
theorem stdRadius_ddcyl {r : Real} (hr : capEnd < r) :
    deriv (deriv stdRadius) r = 0 := by
  have heq : (fun x : Real => deriv stdRadius x) =ᶠ[nhds r] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact stdRadius_dcyl hx.le
  rw [heq.deriv_eq]
  simp

/-- The radial coefficient is `1 / 4` inside the exact round-cap region. -/
theorem stdRadCurv_round {r : Real} (hr : 0 < r) (hr1 : r < 1) :
    stdRadCurv r = (1 : Real) / 4 := by
  have hpos := stdRadius_pos hr
  rw [stdRadius_round hr1.le, roundRadius] at hpos
  have hsin : 0 < Real.sin (r / 2) := by nlinarith
  rw [stdRadCurv, stdRadius_ddround hr1, stdRadius_round hr1.le, roundRadius]
  field_simp [ne_of_gt hsin]
  ring

/-- The tangential coefficient is `1 / 4` inside the exact round-cap region. -/
theorem stdTanCurv_round {r : Real} (hr : 0 < r) (hr1 : r < 1) :
    stdTanCurv r = (1 : Real) / 4 := by
  have hpos := stdRadius_pos hr
  rw [stdRadius_round hr1.le, roundRadius] at hpos
  have hsin : 0 < Real.sin (r / 2) := by nlinarith
  have htrig := Real.sin_sq_add_cos_sq (r / 2)
  rw [stdTanCurv, stdRadius_dround hr1.le, stdRadius_round hr1.le, roundRadius]
  field_simp [ne_of_gt hsin]
  nlinarith

/-- The radial coefficient vanishes inside the exact cylindrical region. -/
theorem stdRadCurv_cyl {r : Real} (hr : capEnd < r) : stdRadCurv r = 0 := by
  rw [stdRadCurv, stdRadius_ddcyl hr, stdRadius_cyl hr.le, cylRadius]
  norm_num

/-- The tangential coefficient is `1 / 4` inside the exact cylindrical region. -/
theorem stdTanCurv_cyl {r : Real} (hr : capEnd < r) :
    stdTanCurv r = (1 : Real) / 4 := by
  rw [stdTanCurv, stdRadius_dcyl hr.le, stdRadius_cyl hr.le, cylRadius]
  norm_num

end DifferentialGeometry.PDE.RicciFlow
