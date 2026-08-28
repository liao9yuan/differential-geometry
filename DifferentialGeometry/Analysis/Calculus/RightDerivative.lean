import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval

namespace DifferentialGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F]

theorem hasDerivAt_of_right
    {f f' : Real -> F} {a b t : Real} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt f (f' x) (Ici x) x)
    (ht : t ∈ Ioo a b) :
    HasDerivAt f (f' t) t := by
  let g : Real -> F := fun x => f a + intervalIntegral f' a x volume
  have hint : IntervalIntegrable f' volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le hf'
  have hgderivIcc : ∀ x ∈ Icc a b,
      HasDerivWithinAt g (f' x) (Icc a b) x := by
    intro x hxIcc
    letI : Fact (x ∈ Icc a b) := ⟨hxIcc⟩
    have hxU : x ∈ uIcc a b := by
      simpa only [uIcc_of_le hab.le] using hxIcc
    have hprim : HasDerivWithinAt
        (fun y => intervalIntegral f' a y volume) (f' x) (Icc a b) x :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc hxU))
        (hf'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
        (hf' x hxIcc)
    simpa only [g] using hprim.const_add (f a)
  have hgderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    exact (hgderivIcc x (mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)
  have hgcont : ContinuousOn g (Icc a b) := by
    have hprim : ContinuousOn
        (fun x => intervalIntegral f' a x volume) (Icc a b) := by
      rw [← uIcc_of_le hab.le]
      exact intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff').mp hint)
    simpa only [g] using continuousOn_const.add hprim
  have hfg : ∀ x ∈ Icc a b, f x = g x := by
    apply eq_of_has_deriv_right_eq hderiv hgderiv hf hgcont
    simp only [g, intervalIntegral.integral_same, add_zero]
  have hfg_ev : f =ᶠ[nhds t] g := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
    exact hfg x hx
  have hgAt : HasDerivAt g (f' t) t := by
    have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    exact (hgderivIcc t htIcc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  exact hgAt.congr_of_eventuallyEq hfg_ev

theorem contDiffOn_of_right
    {v : F → F} {f : Real → F} {a b : Real} (hab : a < b)
    (hv : ContDiff Real ∞ v) (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt f (v (f t)) (Ici t) t) :
    ContDiffOn Real ∞ f (Ioo a b) := by
  have hvcomp : ContinuousOn (fun t ↦ v (f t)) (Icc a b) :=
    hv.continuous.comp_continuousOn hf
  have hfull : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t :=
    fun t ht ↦ hasDerivAt_of_right hab hf hvcomp hderiv ht
  intro t ht
  let c : Real := (a + t) / 2
  let d : Real := (t + b) / 2
  have hct : c < t := by dsimp only [c]; linarith [ht.1]
  have htd : t < d := by dsimp only [d]; linarith [ht.2]
  have hcd : c < d := hct.trans htd
  have hsub : Icc c d ⊆ Ioo a b := by
    intro r hr
    dsimp only [c, d] at hr
    constructor
    · linarith [hr.1, ht.1]
    · linarith [hr.2, ht.2]
  have hfield : ContDiffOn Real ∞
      (Function.uncurry (fun _ : Real ↦ v))
      ((Icc c d) ×ˢ (Set.univ : Set F)) := by
    have hglobal : ContDiff Real ∞
        (Function.uncurry (fun _ : Real ↦ v)) := by
      simpa only [Function.uncurry_apply_pair] using hv.comp contDiff_snd
    exact hglobal.contDiffOn
  have hlocal : ∀ r ∈ Icc c d, HasDerivWithinAt f
      ((fun _ : Real ↦ v) r (f r)) (Icc c d) r := by
    intro r hr
    exact (hfull r (hsub hr)).hasDerivWithinAt
  have hsmooth : ContDiffOn Real ∞ f (Icc c d) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield hlocal
      (fun _ _ ↦ Set.mem_univ _)
  have htcd : t ∈ Ioo c d := ⟨hct, htd⟩
  exact ((hsmooth t (Ioo_subset_Icc_self htcd)).contDiffAt
    (Icc_mem_nhds hct htd)).contDiffWithinAt

/-- A continuous real function cannot cross above a level if, whenever it is
strictly above that level, it has a differentiable upper support that is
strictly decreasing to first order from the right. -/
theorem le_of_upper_support
    {f : Real -> Real} {a b c : Real}
    (hf : ContinuousOn f (Icc a b)) (ha : f a <= c)
    (hsupport : ∀ t ∈ Ico a b, c < f t ->
      exists phi : Real -> Real, exists d : Real,
        phi t = f t ∧
        f ≤ᶠ[nhdsWithin t (Ioi t)] phi ∧
        HasDerivAt phi d t ∧ d < 0) :
    ∀ t ∈ Icc a b, f t <= c := by
  intro t ht
  refine le_of_forall_pos_le_add fun delta hdelta => ?_
  let s : Set Real := {r | f r <= c + delta}
  have hs_closed : IsClosed (s ∩ Icc a b) := by
    have hconst : ContinuousOn (fun _ : Real => c + delta) (Icc a b) :=
      continuousOn_const
    simpa only [s, inter_comm] using
      isClosed_Icc.isClosed_le hf hconst
  have ha_s : a ∈ s := by
    dsimp only [s]
    exact ha.trans (le_add_of_nonneg_right hdelta.le)
  have hs_all : Icc a b ⊆ s := by
    apply hs_closed.Icc_subset_of_forall_exists_gt ha_s
    rintro x ⟨hx_s, hx⟩ y hxy
    change f x <= c + delta at hx_s
    rcases hx_s.lt_or_eq with hx_lt | hx_eq
    · have hnear : ∀ᶠ z in nhdsWithin x (Icc a b), f z < c + delta :=
        hf x (Ico_subset_Icc_self hx) (Iio_mem_nhds hx_lt)
      have hright : ∀ᶠ z in nhdsWithin x (Ioi x), f z < c + delta :=
        nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hnear
      obtain ⟨z, hz_lt, hz_mem⟩ :=
        (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ s from hz_lt.le, hz_mem⟩⟩
    · have hcfx : c < f x := by
        rw [hx_eq]
        linarith
      obtain ⟨phi, d, hphi_eq, hupper, hphi_deriv, hd_neg⟩ :=
        hsupport x hx hcfx
      have hslope : ∀ᶠ z in nhdsWithin x (Ioi x), slope phi x z < 0 :=
        (hphi_deriv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).eventually_lt_const hd_neg
      have hphi_lt : ∀ᶠ z in nhdsWithin x (Ioi x), phi z < phi x := by
        filter_upwards [hslope, self_mem_nhdsWithin] with z hz_slope hxz
        rw [slope_def_field] at hz_slope
        have hdiff : phi z - phi x < 0 := by
          simpa only [zero_mul] using
            (div_lt_iff₀ (sub_pos.mpr hxz)).mp hz_slope
        exact sub_lt_zero.mp hdiff
      have hright : ∀ᶠ z in nhdsWithin x (Ioi x), f z < c + delta := by
        filter_upwards [hupper, hphi_lt] with z hle hlt
        calc
          f z <= phi z := hle
          _ < phi x := hlt
          _ = c + delta := hphi_eq.trans hx_eq
      obtain ⟨z, hz_lt, hz_mem⟩ :=
        (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ s from hz_lt.le, hz_mem⟩⟩
  exact hs_all ht

end DifferentialGeometry
