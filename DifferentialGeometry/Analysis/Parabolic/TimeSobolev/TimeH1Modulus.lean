import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The `√t` Hölder-`½` time modulus of `H¹([0,T]; X)`

For the vector-valued time-Sobolev carrier `timeH1 X T = H¹([0,T]; X)` this file
proves the sharp quantitative modulus of continuity at the initial time:

  `‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖`   for `t ∈ [0,T]`,

where `‖u.deriv‖` is the time-`L²([0,T]; X)` norm of the derivative field.  This
is the explicit Hölder-`½` (`√t`) modulus that quantifies the naked
`ContinuousWithinAt` of `u.toFun` at `t = 0`: unlike the uniform-in-time Sobolev
bound `timeH1.norm_toFun_le` (which carries the whole-horizon factor `√T`), the
increment vanishes as `t → 0` at the explicit rate `√t`.

## Main results

* `TimeSobolev.integral_norm_Icc_le` — the sharp-horizon Cauchy–Schwarz bound
  `∫ s in [0,t], ‖f s‖ ≤ √t · ‖f‖` for `f : L²([0,T]; X)` and `t ∈ [0,T]`.  It
  is the `√t` companion of `TimeSobolev.integral_norm_le` (whose factor is
  `√T`); the sharper factor comes from applying the `L¹ ⊆ L²` Hölder nesting on
  the *sub*-measure `timeMeasure t` and then monotonicity in the measure.
* `TimeSobolev.timeH1.norm_toFun_sub_init_le` — the `√t` trace modulus
  `‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖` on `[0,T]`.
* `TimeSobolev.timeH1.state_le_of_sqrt_floor` — the *state* form of the modulus
  for a zero-datum element: a horizon floor `√T · ‖u.deriv‖ ≤ B` bounds the
  state itself, `‖u.toFun t‖ ≤ B`, at every time of `[0,T]`.
* `TimeSobolev.timeH1.norm_le_of_ae_le` — the same conclusion from an a.e. state
  ball: on `0 < T` an a.e.-in-time bound `‖u.toFun t‖ ≤ R` holds at every time of
  the CLOSED interval `[0,T]`, endpoint included, by continuity of `u.toFun`.

The canonical home of `integral_norm_Icc_le` would be `BochnerL2.lean` next to
`integral_norm_le`; it is placed here to keep the change a single additive leaf.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

/-- **Sharp-horizon Cauchy–Schwarz bound for the interval integral.**  For an
element `f : L²([0,T]; X)` and `t ∈ [0,T]`,

  `∫ s in [0,t], ‖f s‖ ≤ √t · ‖f‖`.

This is the `√t` refinement of `TimeSobolev.integral_norm_le` (which bounds the
integral over the *whole* horizon `[0,T]` by `√T · ‖f‖`): the integral over the
sub-interval `[0,t]` is bounded by `√t` times the full `L²` norm.  The proof
applies the `L¹ ⊆ L²` Hölder-nesting estimate on the sub-measure `timeMeasure t`
(whose total mass is `t`) and then bounds the `L²`-norm-on-`[0,t]` by the
`L²`-norm-on-`[0,T]` via monotonicity of `eLpNorm` in the measure. -/
theorem integral_norm_Icc_le (f : timeL2 X T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in Set.Icc (0 : ℝ) t, ‖f s‖ ≤ Real.sqrt t * ‖f‖ := by
  have hle_meas : timeMeasure t ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl
  have haem : AEStronglyMeasurable (fun s => f s) (timeMeasure t) :=
    (Lp.aestronglyMeasurable f).mono_measure hle_meas
  have hmono2 : eLpNorm (fun s => f s) 2 (timeMeasure t)
      ≤ eLpNorm (fun s => f s) 2 (timeMeasure T) :=
    eLpNorm_mono_measure _ hle_meas
  have hne2 : eLpNorm (fun s => f s) 2 (timeMeasure t) ≠ ∞ :=
    (hmono2.trans_lt (Lp.eLpNorm_ne_top f).lt_top).ne
  have hint : ∫ s in Set.Icc (0 : ℝ) t, ‖f s‖
      = (eLpNorm (fun s => f s) 1 (timeMeasure t)).toReal := by
    rw [show (∫ s in Set.Icc (0 : ℝ) t, ‖f s‖) = ∫ s, ‖f s‖ ∂(timeMeasure t) from rfl,
      integral_norm_eq_lintegral_enorm haem, eLpNorm_one_eq_lintegral_enorm]
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := timeMeasure t) (p := 1) (q := 2) (by norm_num) haem
  have hfin : eLpNorm (fun s => f s) 2 (timeMeasure t)
      * timeMeasure t Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.mul_ne_top hne2 ?_
    rw [timeMeasure_univ]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  rw [hint]
  refine le_trans (ENNReal.toReal_mono hfin hholder) ?_
  rw [ENNReal.toReal_mul, timeMeasure_univ,
    show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
    toReal_ofReal_rpow_half, mul_comm (Real.sqrt t) ‖f‖]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg t)
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hmono2

namespace timeH1

/-- **The `√t` Hölder-`½` trace modulus of `H¹([0,T]; X)`.**  For `t ∈ [0,T]`,

  `‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖`.

The increment of the represented function away from its initial value is
controlled by `√t` times the `L²([0,T]; X)` norm of the time derivative.  This
is the explicit `½`-Hölder modulus of continuity at `t = 0`, quantifying the
qualitative `timeH1.continuousWithinAt_toFun` at the initial time: the increment
vanishes like `√t`.  Proof: the fundamental theorem of calculus
`toFun_sub_toFun` writes the increment as `∫ s in 0..t, u.deriv s`, and the
sharp-horizon Cauchy–Schwarz bound `integral_norm_Icc_le` supplies the `√t`
factor against the full `L²` norm. -/
theorem norm_toFun_sub_init_le (u : timeH1 X T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖u.toFun t - u.init‖ ≤ Real.sqrt t * ‖u.deriv‖ := by
  have h0t : (0 : ℝ) ≤ t := ht.1
  have hsub : u.toFun t - u.init = ∫ s in (0 : ℝ)..t, u.deriv s := by
    simp only [toFun_apply]; abel
  rw [hsub, intervalIntegral.integral_of_le h0t]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans ?_ (TimeSobolev.integral_norm_Icc_le u.deriv ht)
  have hintt : IntegrableOn (fun s => ‖u.deriv s‖) (Set.Icc (0 : ℝ) t) volume :=
    ((TimeSobolev.integrableOn u.deriv).mono_set (Icc_subset_Icc le_rfl ht.2)).norm
  refine setIntegral_mono_set hintt ?_ ?_
  · filter_upwards with s using norm_nonneg _
  · exact HasSubset.Subset.eventuallyLE Ioc_subset_Icc_self

/-- **State bound from a horizon floor on the derivative.**  For a zero-datum
element (`u.init = 0`), a floor `√T · ‖u.deriv‖ ≤ B` on the horizon bounds the
state itself at every time of `[0,T]`:

  `‖u.toFun t‖ ≤ B`   for `t ∈ [0,T]`.

This is the state form of `norm_toFun_sub_init_le`: the `√t` modulus measures
the increment away from the initial datum, so at datum `0` it measures the state,
and monotonicity of `√·` folds the time-dependent factor `√t` into the horizon
factor `√T`.  It converts a derivative-side smallness hypothesis into the
trajectory-side ball membership that fibre-operator smallness arguments consume. -/
theorem state_le_of_sqrt_floor (u : timeH1 X T) (hinit : u.init = 0) {B : ℝ}
    (hfloor : Real.sqrt T * ‖u.deriv‖ ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.toFun t‖ ≤ B := by
  intro t ht
  calc ‖u.toFun t‖
      = ‖u.toFun t - u.init‖ := by rw [hinit, sub_zero]
    _ ≤ Real.sqrt t * ‖u.deriv‖ := u.norm_toFun_sub_init_le ht
    _ ≤ Real.sqrt T * ‖u.deriv‖ :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (norm_nonneg _)
    _ ≤ B := hfloor

/-- **An almost-everywhere state ball holds everywhere on the closed interval.**
On a nondegenerate horizon (`0 < T`) an a.e. bound `‖u.toFun t‖ ≤ R` for the
carrier measure `timeMeasure T` upgrades to the bound at EVERY time of `[0,T]`,
the closed endpoint `t = T` included.

The upgrade is available because `u.toFun` is continuous on `[0,T]`
(`timeH1.continuousOn_toFun`) and `[0,T]` is the closure of its interior when
`0 ≠ T`: the truncation `min ‖u.toFun ·‖ R` agrees a.e. with `‖u.toFun ·‖`, both
are continuous on `[0,T]`, hence they agree there. -/
theorem norm_le_of_ae_le (u : timeH1 X T) (hT : 0 < T) {R : ℝ}
    (hae : ∀ᵐ t ∂timeMeasure T, ‖u.toFun t‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.toFun t‖ ≤ R := by
  intro t ht
  have hnorm_cont : ContinuousOn (fun s => ‖u.toFun s‖) (Set.Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn u.continuousOn_toFun
  have hmin_cont : ContinuousOn (fun s => min ‖u.toFun s‖ R) (Set.Icc (0 : ℝ) T) :=
    hnorm_cont.inf continuousOn_const
  have hmin : (fun s => min ‖u.toFun s‖ R)
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T)] fun s => ‖u.toFun s‖ := by
    filter_upwards [hae] with s hs using min_eq_left hs
  exact min_eq_left_iff.mp
    (MeasureTheory.Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) hT.ne hmin
      hmin_cont hnorm_cont ht)

end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
