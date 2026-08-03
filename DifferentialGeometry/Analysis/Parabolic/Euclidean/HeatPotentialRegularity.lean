import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelApprox
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelHigher
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution

noncomputable section

open MeasureTheory Real Set Filter
open scoped RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private def heatD1LocalMajor (t : Real) (x y : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
    (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
      ((1 + ‖(heatScale t)⁻¹ • (x - y)‖) *
        Real.exp (-(1 / 8 : Real) * ‖(heatScale t)⁻¹ • (x - y)‖ ^ 2))

private theorem heatD1LocalMajor_int {t : Real} (ht : 0 < t) (x : V) :
    Integrable (heatD1LocalMajor (V := V) t x) := by
  let g : V → Real := fun z =>
    (1 + ‖z‖) * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2)
  have h0 := gaussMoment_int (V := V) 0
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have h1 := gaussMoment_int (V := V) 1
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have hg : Integrable g := by
    have heq : g = fun z : V =>
        ‖z‖ ^ 0 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) +
          ‖z‖ ^ 1 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) := by
      funext z
      simp only [g, pow_zero, one_mul, pow_one]
      ring
    rw [heq]
    exact h0.add h1
  have hs := (hg.comp_smul (inv_ne_zero (heatScale_pos ht).ne')).comp_sub_left x
  simpa only [heatD1LocalMajor, g] using hs.const_mul
    (((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
      (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real))

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem heatD1Maj_le_localMajor {t : Real} (ht : 0 < t)
    (x₀ y : V) {x : V} (hx : x ∈ Metric.ball x₀ (heatScale t)) :
    heatD1Maj t (x - y) ≤ heatD1LocalMajor (V := V) t x₀ y := by
  let r : Real := (heatScale t)⁻¹
  let a : V := r • (x₀ - y)
  let b : V := r • (x - x₀)
  let z : V := r • (x - y)
  have hr : 0 < r := inv_pos.mpr (heatScale_pos ht)
  have hz : z = a + b := by
    unfold z a b
    rw [← smul_add]
    congr 1
    abel
  have hb : ‖b‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    change (heatScale t)⁻¹ * ‖x - x₀‖ < 1
    rw [inv_mul_lt_one₀ (heatScale_pos ht)]
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
  have hz_le : ‖z‖ ≤ ‖a‖ + 1 := by
    rw [hz]
    calc
      ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
      _ ≤ ‖a‖ + 1 := by gcongr
  have ha_le : ‖a‖ ≤ ‖z‖ + 1 := by
    have ha : a = z - b := by rw [hz]; abel
    rw [ha]
    calc
      ‖z - b‖ ≤ ‖z‖ + ‖b‖ := norm_sub_le z b
      _ ≤ ‖z‖ + 1 := by gcongr
  have ha_sq : ‖a‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 := by
    have hsq : ‖a‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
      exact sq_le_sq₀ (norm_nonneg a) (by positivity) |>.2 ha_le
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hexpArg : -(1 / 4 : Real) * ‖z‖ ^ 2 ≤
      1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2 := by
    nlinarith
  have hexp : Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
      Real.exp (1 / 4 : Real) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
    calc
      Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
          Real.exp (1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2) :=
        Real.exp_le_exp.mpr hexpArg
      _ = Real.exp (1 / 4 : Real) *
          Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hbase : baseD1Maj z ≤
      (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
        ((1 + ‖a‖) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
    have hmass : 0 ≤ (baseHeatMass V)⁻¹ :=
      inv_nonneg.mpr (baseHeatMass_pos (V := V)).le
    have hexpZ : 0 ≤ Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) :=
      (Real.exp_pos _).le
    have hleft : 0 ≤ (2 : Real)⁻¹ * (‖a‖ + 1) :=
      mul_nonneg (by positivity) (add_nonneg (norm_nonneg a) zero_le_one)
    let Q : Real := (baseHeatMass V)⁻¹ * (‖a‖ + 1) *
      (Real.exp (1 / 4 : Real) *
        Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))
    have hQ : 0 ≤ Q := by
      unfold Q
      positivity
    unfold baseD1Maj baseHeat
    calc
      (2 : Real)⁻¹ * ‖z‖ *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) ≤
        (2 : Real)⁻¹ * (‖a‖ + 1) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hz_le (by positivity))
          (mul_nonneg hmass hexpZ)
      _ ≤ (2 : Real)⁻¹ * (‖a‖ + 1) *
          ((baseHeatMass V)⁻¹ *
            (Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))) := by
        have hexp' : Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) ≤
            Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
          simpa only [one_div] using hexp
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp' hmass) hleft
      _ = (2 : Real)⁻¹ * Q := by unfold Q; ring
      _ ≤ 1 * Q := mul_le_mul_of_nonneg_right (by norm_num) hQ
      _ = (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
          ((1 + ‖a‖) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
        unfold Q
        ring
  have hfront : 0 ≤
      ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ :=
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le)
  unfold heatD1Maj heatD1LocalMajor
  change _ * baseD1Maj z ≤ _
  change _ ≤ _ * ((1 + ‖a‖) * _)
  simpa only [a, mul_assoc] using mul_le_mul_of_nonneg_left hbase hfront

def heatSupGradient (t : Real) (u : BoundedContinuousFunction V F) (x : V) :
    V →L[Real] F :=
  ∫ y : V, (heatD1Map t (x - y)).smulRight (u y)

omit [CompleteSpace F] in
theorem heatSup_hasFDerivAt {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    HasFDerivAt (fun z : V => heatSup t u z) (heatSupGradient t u x) x := by
  let G : V → V → F := fun z y => heatKernel t (z - y) • u y
  let DG : V → V → V →L[Real] F := fun z y =>
    (heatD1Map t (z - y)).smulRight (u y)
  let bound : V → Real := fun y => ‖u‖ * heatD1LocalMajor (V := V) t x y
  have hs : Metric.ball x (heatScale t) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (heatScale_pos ht)
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Continuous.aestronglyMeasurable
    unfold G heatKernel baseHeat baseHeatMass heatScale
    fun_prop
  have hGint : Integrable (G x) := by
    refine (((heatKernel_int (V := V) ht).norm.comp_sub_left x).mul_const ‖u‖).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold G heatKernel baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y)
      (norm_nonneg (heatKernel t (x - y)))
  have hDGmeas : AEStronglyMeasurable (DG x) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    unfold DG heatD1Map baseD1Map baseHeat baseHeatMass heatScale
    fun_prop
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      ‖DG z y‖ ≤ bound y := by
    apply Filter.Eventually.of_forall
    intro y z hz
    calc
      ‖DG z y‖ ≤ ‖heatD1Map t (z - y)‖ * ‖u y‖ := by
        unfold DG
        rw [ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ heatD1Maj t (z - y) * ‖u‖ := by
        exact mul_le_mul (heatD1Map_norm_le ht (z - y))
          (u.norm_coe_le_norm y) (norm_nonneg _) (heatD1Maj_nonneg ht _)
      _ ≤ ‖u‖ * heatD1LocalMajor (V := V) t x y := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (heatD1Maj_le_localMajor ht x y hz) (norm_nonneg u)
      _ = bound y := rfl
  have hboundInt : Integrable bound :=
    (heatD1LocalMajor_int (V := V) ht x).const_mul ‖u‖
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      HasFDerivAt (G · y) (DG z y) z := by
    apply Filter.Eventually.of_forall
    intro y z hz
    have hsub : HasFDerivAt (fun q : V => q - y)
        (ContinuousLinearMap.id Real V) z :=
      (hasFDerivAt_id z).sub_const y
    unfold G DG
    simpa using ((heatKernel_hasFDeriv ht (z - y)).comp z hsub).smul_const (u y)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) hs hGmeas hGint hDGmeas
      hbound hboundInt hdiff
  have hfun : (fun z : V => ∫ y : V, G z y) = fun z : V => heatSup t u z := by
    funext z
    unfold G heatSup supKernel
    rw [← MeasureTheory.convolution_lsmul_swap]
    rfl
  rw [hfun] at h
  simpa only [DG, heatSupGradient] using h

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
