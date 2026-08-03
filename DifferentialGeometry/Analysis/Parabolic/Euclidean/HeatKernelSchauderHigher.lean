import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelHigher

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD3Holder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseD3Maj x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD3Holder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseD3Holder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseD3Maj_nonneg x)

theorem baseD3Holder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseD3Holder alpha : V → Real) := by
  have hfirst : Integrable (fun x : V => ‖x‖ * baseD3Maj x) := by
    have h4 := (gaussMoment_int (V := V) 4
      (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
        ((8 : Real)⁻¹ * (baseHeatMass V)⁻¹)
    have h2 := (gaussMoment_int (V := V) 2
      (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
        ((3 / 4 : Real) * (baseHeatMass V)⁻¹)
    have heq : (fun x : V => ‖x‖ * baseD3Maj x) = fun x : V =>
        ((8 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
            (‖x‖ ^ 4 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
          ((3 / 4 : Real) * (baseHeatMass V)⁻¹) *
            (‖x‖ ^ 2 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) := by
      funext x
      unfold baseD3Maj baseHeat
      ring
    rw [heq]
    exact h4.add h2
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseD3Maj x) := by
    have h := (baseD3Maj_int (V := V)).add hfirst
    have heq : (fun x : V => (1 + ‖x‖) * baseD3Maj x) =
        fun x : V => baseD3Maj x + ‖x‖ * baseD3Maj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
    have hmaj : Continuous (baseD3Maj : V → Real) := by
      unfold baseD3Maj baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hmaj).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD3Holder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseD3Maj_nonneg x)

def heatC3Holder (alpha : NNReal) : Real :=
  ∫ x : V, baseD3Holder alpha x

omit [Nontrivial V] in
theorem heatC3Holder_nonneg (alpha : NNReal) : 0 ≤ heatC3Holder (V := V) alpha :=
  integral_nonneg (baseD3Holder_nonneg alpha)

def heatD3Holder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t) ^ (alpha : Real) *
        baseD3Holder alpha ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3Holder_nonneg (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    0 ≤ heatD3Holder alpha t x := by
  unfold heatD3Holder
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
            (inv_nonneg.mpr (heatScale_pos ht).le))
          (inv_nonneg.mpr (heatScale_pos ht).le))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (Real.rpow_nonneg (heatScale_pos ht).le _))
    (baseD3Holder_nonneg alpha _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3Holder_eq (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    heatD3Holder alpha t x = ‖x‖ ^ (alpha : Real) * heatD3Maj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hrpow : ‖x‖ ^ (alpha : Real) =
      (heatScale t) ^ (alpha : Real) *
        ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) := by
    calc
      ‖x‖ ^ (alpha : Real) =
          ‖heatScale t • ((heatScale t)⁻¹ • x)‖ ^ (alpha : Real) :=
        congrArg (fun z : V => ‖z‖ ^ (alpha : Real)) hx
      _ = (heatScale t * ‖(heatScale t)⁻¹ • x‖) ^ (alpha : Real) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = (heatScale t) ^ (alpha : Real) *
          ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) :=
        Real.mul_rpow hr.le (norm_nonneg _)
  unfold heatD3Holder heatD3Maj baseD3Holder
  rw [hrpow]
  ring

theorem heatD3Holder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatD3Holder (V := V) alpha t) := by
  unfold heatD3Holder
  exact (baseD3Holder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatD3Holder (alpha : NNReal) {t : Real} (ht : 0 < t) :
    ∫ x : V, heatD3Holder alpha t x =
      t⁻¹ * (heatScale t)⁻¹ * (heatScale t) ^ (alpha : Real) *
        heatC3Holder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsquare]
  unfold heatD3Holder heatC3Holder
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure V) (baseD3Holder alpha) hr.le]
  simp only [smul_eq_mul]
  calc
    (heatScale t ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          heatScale t ^ (alpha : Real) *
          (heatScale t ^ Module.finrank Real V *
            ∫ x : V, baseD3Holder alpha x) =
        ((heatScale t)⁻¹ * (heatScale t)⁻¹) * (heatScale t)⁻¹ *
          heatScale t ^ (alpha : Real) *
            ∫ x : V, baseD3Holder alpha x := by
      field_simp [hr.ne']
    _ = t⁻¹ * (heatScale t)⁻¹ * (heatScale t) ^ (alpha : Real) *
        ∫ x : V, baseD3Holder alpha x := by rw [hscale]

def holderThirdHeatScale (alpha : NNReal) (t : Real) : Real :=
  t ^ ((alpha : Real) / 2 - 3 / 2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem holderThirdHeatScale_eq (alpha : NNReal) {t : Real} (ht : 0 < t) :
    t⁻¹ * (heatScale t)⁻¹ * (heatScale t) ^ (alpha : Real) =
      holderThirdHeatScale alpha t := by
  unfold holderThirdHeatScale heatScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_neg_one, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
    ← Real.rpow_add ht, ← Real.rpow_add ht]
  congr 1
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3_holder_bound (alpha : NNReal) {t : Real} (ht : 0 < t)
    (u v w x : V) :
    ‖heatD3 t u v w x‖ * ‖x‖ ^ (alpha : Real) ≤
      ‖u‖ * ‖v‖ * ‖w‖ * heatD3Holder alpha t x := by
  rw [heatD3Holder_eq alpha ht]
  calc
    ‖heatD3 t u v w x‖ * ‖x‖ ^ (alpha : Real) ≤
        (‖u‖ * ‖v‖ * ‖w‖ * heatD3Maj t x) *
          ‖x‖ ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_right (heatD3_bound ht u v w x)
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = ‖u‖ * ‖v‖ * ‖w‖ *
        (‖x‖ ^ (alpha : Real) * heatD3Maj t x) := by ring

theorem integral_holderD3 {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u v w : V) :
    (∫ x : V, ‖heatD3 t u v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
      ‖u‖ * ‖v‖ * ‖w‖ * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
  have hmajor : Integrable
      (fun x : V => (‖u‖ * ‖v‖ * ‖w‖) * heatD3Holder alpha t x) :=
    (heatD3Holder_int (V := V) halpha ht).const_mul _
  have hleft : Integrable
      (fun x : V => ‖heatD3 t u v w x‖ * ‖x‖ ^ (alpha : Real)) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
      have hd3 : Continuous (fun x : V => heatD3 t u v w x) := by
        unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd3.norm.mul hpow
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact heatD3_holder_bound alpha ht u v w x
  calc
    (∫ x : V, ‖heatD3 t u v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
        ∫ x : V, (‖u‖ * ‖v‖ * ‖w‖) * heatD3Holder alpha t x :=
      integral_mono hleft hmajor
        (fun x => heatD3_holder_bound alpha ht u v w x)
    _ = (‖u‖ * ‖v‖ * ‖w‖) *
        (t⁻¹ * (heatScale t)⁻¹ * (heatScale t) ^ (alpha : Real) *
          heatC3Holder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatD3Holder alpha ht]
    _ = ‖u‖ * ‖v‖ * ‖w‖ * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
      rw [holderThirdHeatScale_eq alpha ht]
      ring

section Cancellation

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def heatD3Cancel (t : Real) (u v w : V) (f : V → F) (x : V) : F :=
  ∫ y : V, heatD3 t u v w y • (f (x - y) - f x)

omit [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedSpace Real F] [CompleteSpace F] in
private theorem holder_shift_bound_d3 {alpha K : NNReal} {f : V → F}
    (hf : HolderWith K alpha f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem d3_cancel_bound_of_holder {alpha K : NNReal}
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (u v w x y : V) :
    ‖heatD3 t u v w y • (f (x - y) - f x)‖ ≤
      (‖u‖ * ‖v‖ * ‖w‖ * (K : Real)) * heatD3Holder alpha t y := by
  calc
    ‖heatD3 t u v w y • (f (x - y) - f x)‖ =
        ‖heatD3 t u v w y‖ * ‖f (x - y) - f x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖heatD3 t u v w y‖ * ((K : Real) * ‖y‖ ^ (alpha : Real)) :=
      mul_le_mul_of_nonneg_left (holder_shift_bound_d3 hf x y) (norm_nonneg _)
    _ ≤ (‖u‖ * ‖v‖ * ‖w‖ * heatD3Maj t y) *
        ((K : Real) * ‖y‖ ^ (alpha : Real)) := by
      gcongr
      exact heatD3_bound ht u v w y
    _ = (‖u‖ * ‖v‖ * ‖w‖ * (K : Real)) * heatD3Holder alpha t y := by
      rw [heatD3Holder_eq alpha ht]
      ring

omit [CompleteSpace F] in
theorem heatD3Cancel_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (u v w x : V) :
    Integrable (fun y : V => heatD3 t u v w y • (f (x - y) - f x)) := by
  have hfcont : Continuous f := hf.continuous halpha0
  have hmajor : Integrable
      (fun y : V => (‖u‖ * ‖v‖ * ‖w‖ * (K : Real)) *
        heatD3Holder alpha t y) :=
    (heatD3Holder_int (V := V) halpha1 ht).const_mul _
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  filter_upwards with y
  exact d3_cancel_bound_of_holder ht hf u v w x y

omit [CompleteSpace F] in
theorem heatD3Cancel_norm_of_holder {alpha K : NNReal}
    (halpha : alpha ≤ 1) {t : Real} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K alpha f) (u v w x : V) :
    ‖heatD3Cancel t u v w f x‖ ≤
      ‖u‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
  unfold heatD3Cancel
  calc
    ‖∫ y : V, heatD3 t u v w y • (f (x - y) - f x)‖ ≤
        ∫ y : V, (‖u‖ * ‖v‖ * ‖w‖ * (K : Real)) *
          heatD3Holder alpha t y :=
      norm_integral_le_of_norm_le
        ((heatD3Holder_int (V := V) halpha ht).const_mul _)
        (Filter.Eventually.of_forall fun y =>
          d3_cancel_bound_of_holder ht hf u v w x y)
    _ = (‖u‖ * ‖v‖ * ‖w‖ * (K : Real)) *
        (t⁻¹ * (heatScale t)⁻¹ * (heatScale t) ^ (alpha : Real) *
          heatC3Holder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatD3Holder alpha ht]
    _ = ‖u‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
      rw [holderThirdHeatScale_eq alpha ht]
      ring

end Cancellation

end DifferentialGeometry.Analysis.Parabolic.Euclidean
