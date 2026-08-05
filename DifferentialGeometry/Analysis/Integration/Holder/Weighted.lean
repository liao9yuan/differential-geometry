import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm


noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators MeasureTheory

namespace DifferentialGeometry.Integral

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

theorem holder_integral_prod_rpow_le_prod_integral_rpow
    (t : Finset ι) (f : ι → α → ℝ) (θ : ι → ℝ)
    (hf_int : ∀ i ∈ t, Integrable (f i) μ)
    (hf_nn : ∀ i ∈ t, 0 ≤ᵐ[μ] f i)
    (hθ : ∀ i ∈ t, 0 ≤ θ i) (hθ1 : ∑ i ∈ t, θ i = 1) :
    ∫ x, ∏ i ∈ t, f i x ^ θ i ∂μ ≤ ∏ i ∈ t, (∫ x, f i x ∂μ) ^ θ i := by
  classical
  have hae : ∀ᵐ x ∂μ, ∀ i ∈ t, 0 ≤ f i x :=
    (Filter.eventually_all_finset t).mpr fun i hi => hf_nn i hi
  have hmeas : ∀ i ∈ t, AEMeasurable (f i) μ := fun i hi => (hf_int i hi).aemeasurable
  have hF_meas : AEMeasurable (fun x => ∏ i ∈ t, f i x ^ θ i) μ :=
    Finset.aemeasurable_fun_prod t fun i hi => (hmeas i hi).pow_const (θ i)
  have hF_nn : 0 ≤ᵐ[μ] fun x => ∏ i ∈ t, f i x ^ θ i := by
    filter_upwards [hae] with x hx
    exact Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hx i hi) (θ i)
  rw [integral_eq_lintegral_of_nonneg_ae hF_nn hF_meas.aestronglyMeasurable]
  have hoR : ∀ i ∈ t, AEMeasurable (fun x => ENNReal.ofReal (f i x)) μ :=
    fun i hi => ENNReal.measurable_ofReal.comp_aemeasurable (hmeas i hi)
  have hlin := ENNReal.lintegral_prod_norm_pow_le t hoR hθ1 hθ
  have hcongr : (∫⁻ x, ENNReal.ofReal (∏ i ∈ t, f i x ^ θ i) ∂μ) =
      ∫⁻ x, ∏ i ∈ t, ENNReal.ofReal (f i x) ^ θ i ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [ENNReal.ofReal_prod_of_nonneg fun i hi => Real.rpow_nonneg (hx i hi) (θ i)]
    exact Finset.prod_congr rfl fun i hi =>
      (ENNReal.ofReal_rpow_of_nonneg (hx i hi) (hθ i hi)).symm
  have hfin : ∀ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ≠ ⊤ :=
    fun i hi => (hf_int i hi).lintegral_lt_top.ne
  have hRfin : (∏ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ^ θ i) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i hi =>
      ENNReal.rpow_lt_top_of_nonneg (hθ i hi) (hfin i hi)).ne
  calc
    (∫⁻ x, ENNReal.ofReal (∏ i ∈ t, f i x ^ θ i) ∂μ).toReal ≤
        (∏ i ∈ t, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ^ θ i).toReal := by
      refine ENNReal.toReal_mono hRfin ?_
      rw [hcongr]
      exact hlin
    _ = ∏ i ∈ t, (∫ x, f i x ∂μ) ^ θ i := by
      rw [ENNReal.toReal_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← ENNReal.toReal_rpow,
        integral_eq_lintegral_of_nonneg_ae (hf_nn i hi)
          (hf_int i hi).aestronglyMeasurable]

theorem holder_integral_mul_rpow_le
    {f g : α → ℝ} {theta : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_nn : 0 ≤ᵐ[μ] f) (hg_nn : 0 ≤ᵐ[μ] g)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1) :
    ∫ x, f x ^ theta * g x ^ (1 - theta) ∂μ ≤
      (∫ x, f x ∂μ) ^ theta * (∫ x, g x ∂μ) ^ (1 - theta) := by
  let F : Fin 2 → α → ℝ := ![f, g]
  let Theta : Fin 2 → ℝ := ![theta, 1 - theta]
  have h := holder_integral_prod_rpow_le_prod_integral_rpow
    (Finset.univ : Finset (Fin 2)) F Theta
    (by
      intro i _
      fin_cases i
      · simpa [F] using hf
      · simpa [F] using hg)
    (by
      intro i _
      fin_cases i
      · simpa [F] using hf_nn
      · simpa [F] using hg_nn)
    (by
      intro i _
      fin_cases i
      · simpa [Theta] using htheta
      · simpa [Theta] using sub_nonneg.mpr htheta_one)
    (by simp [Theta, Fin.sum_univ_two])
  simpa [F, Theta, Fin.prod_univ_two] using h

theorem integrable_rpow_of_integrable_rpow
    [IsFiniteMeasure μ] {f : α → ℝ} {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q)
    (hf : AEMeasurable f μ) (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hfq : Integrable (fun x => f x ^ q) μ) :
    Integrable (fun x => f x ^ p) μ := by
  apply (hfq.add (integrable_const (1 : ℝ))).mono'
    (hf.pow_const p).aestronglyMeasurable
  filter_upwards [hf_nonneg] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx p)]
  by_cases hfx : f x ≤ 1
  · exact (Real.rpow_le_one hx hfx hp).trans (le_add_of_nonneg_left (Real.rpow_nonneg hx q))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hfx) hpq).trans
      (le_add_of_nonneg_right zero_le_one)

theorem integral_rpow_le_integral_rpow_mul_measure
    [IsFiniteMeasure μ] {f : α → ℝ} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hfq : Integrable (fun x => f x ^ q) μ) :
    (∫ x, f x ^ p ∂μ) ≤
      (∫ x, f x ^ q ∂μ) ^ (p / q) *
        μ.real Set.univ ^ (1 - p / q) := by
  have htheta : 0 ≤ p / q := div_nonneg hp hq.le
  have htheta_one : p / q ≤ 1 := (div_le_one hq).2 hpq
  have hone : Integrable (fun _ : α => (1 : ℝ)) μ := integrable_const _
  have h := holder_integral_mul_rpow_le
    (f := fun x => f x ^ q) (g := fun _ : α => (1 : ℝ))
    hfq hone
    (hf_nonneg.mono fun x hx => Real.rpow_nonneg hx q)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    htheta htheta_one
  have hpoint : ∀ᵐ x ∂μ,
      (f x ^ q) ^ (p / q) * (1 : ℝ) ^ (1 - p / q) = f x ^ p := by
    filter_upwards [hf_nonneg] with x hx
    rw [Real.one_rpow, mul_one, ← Real.rpow_mul hx]
    congr 2
    field_simp [hq.ne']
  rw [integral_congr_ae hpoint] at h
  simpa only [integral_const, smul_eq_mul, mul_one] using h

private theorem critical_sobolev_rpow_factorization
    {d a : ℝ} (hd : 2 < d) :
    (a ^ 2) ^ (2 / d) *
        (|a| ^ (2 * d / (d - 2))) ^ (1 - 2 / d) =
      |a| ^ (2 + 4 / d) := by
  have ha : 0 ≤ |a| := abs_nonneg a
  have hdpos : 0 < d := by linarith
  have hd0 : d ≠ 0 := by linarith
  have hd2 : d - 2 ≠ 0 := by linarith
  have htwo_div : 0 ≤ (2 : ℝ) / d := div_nonneg (by norm_num) hdpos.le
  have htheta : 0 ≤ 1 - (2 : ℝ) / d :=
    sub_nonneg.mpr ((div_le_one hdpos).2 (by linarith))
  have hcritical : 0 ≤ (2 : ℝ) * d / (d - 2) :=
    div_nonneg (mul_nonneg (by norm_num) hdpos.le) (by linarith)
  rw [show a ^ 2 = |a| ^ 2 by exact (sq_abs a).symm]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul ha, ← Real.rpow_mul ha]
  norm_num
  rw [← Real.rpow_add_of_nonneg ha (mul_nonneg (by norm_num) htwo_div)
    (mul_nonneg hcritical htheta)]
  congr 1
  field_simp
  ring

theorem critical_sobolev_interpolation
    {u : α → ℝ} {d : ℝ} (hd : 2 < d)
    (hu_meas : AEStronglyMeasurable u μ)
    (h2 : Integrable (fun x => u x ^ 2) μ)
    (hq : Integrable (fun x => |u x| ^ (2 * d / (d - 2))) μ) :
    ∫ x, |u x| ^ (2 + 4 / d) ∂μ ≤
      (∫ x, u x ^ 2 ∂μ) ^ (2 / d) *
        lpNorm u (ENNReal.ofReal (2 * d / (d - 2))) μ ^ 2 := by
  have hdpos : 0 < d := by linarith
  have hd2pos : 0 < d - 2 := by linarith
  have htheta : 0 ≤ (2 : ℝ) / d := div_nonneg (by norm_num) hdpos.le
  have htheta_one : (2 : ℝ) / d ≤ 1 := (div_le_one hdpos).2 (by linarith)
  have hholder := holder_integral_mul_rpow_le
    h2 hq (ae_of_all μ fun x => sq_nonneg (u x))
    (ae_of_all μ fun x => Real.rpow_nonneg (abs_nonneg _) _)
    htheta htheta_one
  have hlhs :
      (∫ x, (u x ^ 2) ^ (2 / d) *
          (|u x| ^ (2 * d / (d - 2))) ^ (1 - 2 / d) ∂μ) =
        ∫ x, |u x| ^ (2 + 4 / d) ∂μ := by
    exact integral_congr_ae
      (ae_of_all μ fun x => critical_sobolev_rpow_factorization hd)
  rw [hlhs] at hholder
  have hqpos : 0 < 2 * d / (d - 2) :=
    div_pos (mul_pos (by norm_num) hdpos) hd2pos
  have hlp := lpNorm_eq_integral_norm_rpow_toReal
    (p := ENNReal.ofReal (2 * d / (d - 2)))
    (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
    ENNReal.ofReal_ne_top hu_meas
  rw [ENNReal.toReal_ofReal hqpos.le] at hlp
  have habs : (fun x => ‖u x‖ ^ (2 * d / (d - 2))) =
      (fun x => |u x| ^ (2 * d / (d - 2))) := by
    funext x
    rw [Real.norm_eq_abs]
  rw [habs] at hlp
  have hA : 0 ≤ ∫ x, |u x| ^ (2 * d / (d - 2)) ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hnorm : lpNorm u (ENNReal.ofReal (2 * d / (d - 2))) μ ^ 2 =
      (∫ x, |u x| ^ (2 * d / (d - 2)) ∂μ) ^ (1 - 2 / d) := by
    rw [hlp]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hA]
    congr 1
    norm_num
    field_simp
  rw [← hnorm] at hholder
  exact hholder

end DifferentialGeometry.Integral

end
