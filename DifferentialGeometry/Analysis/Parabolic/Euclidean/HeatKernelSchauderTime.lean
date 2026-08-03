import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSchauderHigher

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD2DtHolder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseD2DtMaj x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2DtHolder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseD2DtHolder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseD2DtMaj_nonneg x)

private theorem baseD2DtFirst_int :
    Integrable (fun x : V ↦ ‖x‖ * baseD2DtMaj x) := by
  let c : Real := ((Module.finrank Real V : Real) + 2) / 2
  have h5 := (gaussMoment_int (V := V) 5
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((16 : Real)⁻¹ * (baseHeatMass V)⁻¹)
  have h3 := (gaussMoment_int (V := V) 3
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((c * (4 : Real)⁻¹ + (3 / 8 : Real)) * (baseHeatMass V)⁻¹)
  have h1 := (gaussMoment_int (V := V) 1
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((c * (2 : Real)⁻¹) * (baseHeatMass V)⁻¹)
  have heq : (fun x : V ↦ ‖x‖ * baseD2DtMaj x) = fun x : V ↦
      ((16 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 5 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
        ((c * (4 : Real)⁻¹ + (3 / 8 : Real)) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 3 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
        ((c * (2 : Real)⁻¹) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 1 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2DtMaj baseD2Maj baseD3Maj baseHeat
    dsimp [c]
    ring
  rw [heq]
  exact (h5.add h3).add h1

theorem baseD2DtHolder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseD2DtHolder alpha : V → Real) := by
  have hmajor : Integrable (fun x : V ↦ (1 + ‖x‖) * baseD2DtMaj x) := by
    have h := (baseD2DtMaj_int (V := V)).add baseD2DtFirst_int
    have heq : (fun x : V ↦ (1 + ‖x‖) * baseD2DtMaj x) =
        fun x : V ↦ baseD2DtMaj x + ‖x‖ * baseD2DtMaj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
    have hmaj : Continuous (baseD2DtMaj : V → Real) := by
      unfold baseD2DtMaj baseD2Maj baseD3Maj baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hmaj).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD2DtHolder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseD2DtMaj_nonneg x)

def heatC2DtHolder (alpha : NNReal) : Real :=
  ∫ x : V, baseD2DtHolder alpha x

omit [Nontrivial V] in
theorem heatC2DtHolder_nonneg (alpha : NNReal) :
    0 ≤ heatC2DtHolder (V := V) alpha :=
  integral_nonneg (baseD2DtHolder_nonneg alpha)

def heatD2DtHolder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (t ^ 2)⁻¹ *
    (heatScale t) ^ (alpha : Real) *
      baseD2DtHolder alpha ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2DtHolder_nonneg (alpha : NNReal) {t : Real}
    (ht : 0 < t) (x : V) :
    0 ≤ heatD2DtHolder alpha t x := by
  unfold heatD2DtHolder
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (sq_nonneg t)))
      (Real.rpow_nonneg (heatScale_pos ht).le _))
    (baseD2DtHolder_nonneg alpha _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2DtHolder_eq (alpha : NNReal) {t : Real}
    (ht : 0 < t) (x : V) :
    heatD2DtHolder alpha t x =
      ‖x‖ ^ (alpha : Real) * heatD2DtMaj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hrpow : ‖x‖ ^ (alpha : Real) =
      (heatScale t) ^ (alpha : Real) *
        ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) := by
    calc
      ‖x‖ ^ (alpha : Real) =
          ‖heatScale t • ((heatScale t)⁻¹ • x)‖ ^ (alpha : Real) :=
        congrArg (fun z : V ↦ ‖z‖ ^ (alpha : Real)) hx
      _ = (heatScale t * ‖(heatScale t)⁻¹ • x‖) ^ (alpha : Real) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = (heatScale t) ^ (alpha : Real) *
          ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) :=
        Real.mul_rpow hr.le (norm_nonneg _)
  unfold heatD2DtHolder heatD2DtMaj baseD2DtHolder
  rw [hrpow]
  ring

theorem heatD2DtHolder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatD2DtHolder (V := V) alpha t) := by
  unfold heatD2DtHolder
  exact (baseD2DtHolder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatD2DtHolder (alpha : NNReal) {t : Real}
    (ht : 0 < t) :
    ∫ x : V, heatD2DtHolder alpha t x =
      (t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) *
        heatC2DtHolder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2DtHolder heatC2DtHolder
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure V) (baseD2DtHolder alpha) hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

def holderSecondTimeHeatScale (alpha : NNReal) (t : Real) : Real :=
  t ^ ((alpha : Real) / 2 - 2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem holderSecondTimeHeatScale_eq (alpha : NNReal) {t : Real}
    (ht : 0 < t) :
    (t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) =
      holderSecondTimeHeatScale alpha t := by
  unfold holderSecondTimeHeatScale heatScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
    ← Real.rpow_add ht]
  congr 1
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Dt_holder_bound (alpha : NNReal) {t : Real}
    (ht : 0 < t) (v w x : V) :
    ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
      ‖v‖ * ‖w‖ * heatD2DtHolder alpha t x := by
  rw [heatD2DtHolder_eq alpha ht]
  calc
    ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
        (‖v‖ * ‖w‖ * heatD2DtMaj t x) * ‖x‖ ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_right (heatD2Dt_bound ht v w x)
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = ‖v‖ * ‖w‖ *
        (‖x‖ ^ (alpha : Real) * heatD2DtMaj t x) := by ring

theorem integral_holderD2Dt {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
      ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
  have hmajor : Integrable
      (fun x : V ↦ (‖v‖ * ‖w‖) * heatD2DtHolder alpha t x) :=
    (heatD2DtHolder_int (V := V) halpha ht).const_mul _
  have hleft : Integrable
      (fun x : V ↦ ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
      have hd2dt : Continuous (fun x : V ↦ heatD2Dt t v w x) := by
        unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd2dt.norm.mul hpow
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact heatD2Dt_holder_bound alpha ht v w x
  calc
    (∫ x : V, ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
        ∫ x : V, (‖v‖ * ‖w‖) * heatD2DtHolder alpha t x :=
      integral_mono hleft hmajor
        (fun x ↦ heatD2Dt_holder_bound alpha ht v w x)
    _ = (‖v‖ * ‖w‖) *
        ((t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) *
          heatC2DtHolder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatD2DtHolder alpha ht]
    _ = ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
      rw [holderSecondTimeHeatScale_eq alpha ht]
      ring

theorem holderSecondTimeHeatScale_integral_le {alpha : NNReal}
    (halpha : alpha < 2) {d T : Real} (hd : 0 < d) (hT : d ≤ T) :
    ∫ t : Real in d..T, holderSecondTimeHeatScale alpha t ≤
      (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1) := by
  let q : Real := (alpha : Real) / 2 - 1
  have halpha_real : (alpha : Real) < 2 := by exact_mod_cast halpha
  have hT0 : 0 < T := hd.trans_le hT
  have hq : q < 0 := by
    dsimp [q]
    linarith
  have hqne : q ≠ 0 := hq.ne
  have hden : 2 - (alpha : Real) ≠ 0 := by linarith
  have hden' : (alpha : Real) - 2 ≠ 0 := by linarith
  have hpne : (alpha : Real) / 2 - 2 ≠ -1 := by
    intro heq
    linarith
  have hzero : 0 ∉ uIcc d T := by
    rw [uIcc_of_le hT]
    simp only [mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hd)
  unfold holderSecondTimeHeatScale
  rw [integral_rpow (Or.inr ⟨hpne, hzero⟩)]
  have hexp : (alpha : Real) / 2 - 2 + 1 = q := by
    dsimp [q]
    ring
  rw [hexp]
  have hrewrite : (T ^ q - d ^ q) / q =
      (2 / (2 - (alpha : Real))) * (d ^ q - T ^ q) := by
    dsimp [q] at hqne ⊢
    field_simp [hden, hden', hqne]
    ring
  rw [hrewrite]
  have hcoef : 0 ≤ 2 / (2 - (alpha : Real)) := by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr halpha_real.le)
  calc
    (2 / (2 - (alpha : Real))) * (d ^ q - T ^ q) ≤
        (2 / (2 - (alpha : Real))) * d ^ q := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg hT0.le q)) hcoef
    _ = (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1) := by
      rfl

theorem mul_holderSecondTimeHeatScale_integral_le {alpha : NNReal}
    (halpha : alpha < 2) {d T : Real} (hd : 0 < d) (hT : d ≤ T) :
    d * (∫ t : Real in d..T, holderSecondTimeHeatScale alpha t) ≤
      (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2) := by
  have h := mul_le_mul_of_nonneg_left
    (holderSecondTimeHeatScale_integral_le halpha hd hT) hd.le
  refine h.trans_eq ?_
  calc
    d * ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1)) =
        (2 / (2 - (alpha : Real))) *
          (d ^ (1 : Real) * d ^ ((alpha : Real) / 2 - 1)) := by
      rw [Real.rpow_one]
      ring_nf
    _ = (2 / (2 - (alpha : Real))) *
        d ^ (1 + ((alpha : Real) / 2 - 1)) := by
      rw [Real.rpow_add hd]
    _ = (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2) := by
      congr 1
      ring_nf

end DifferentialGeometry.Analysis.Parabolic.Euclidean
