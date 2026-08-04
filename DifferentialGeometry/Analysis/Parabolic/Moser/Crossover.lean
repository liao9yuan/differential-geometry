import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.Moser

theorem exp_centered_log_eq_rpow
    {r : ℝ} (hr : 0 < r) (p c : ℝ) :
    Real.exp (p * (Real.log r - c)) =
      Real.exp (-p * c) * r ^ p := by
  rw [mul_sub, Real.exp_sub]
  have hrpow : Real.exp (p * Real.log r) = r ^ p := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    ring
  rw [hrpow, div_eq_mul_inv, ← Real.exp_neg]
  have harg : -(p * c) = -p * c := by ring
  rw [harg]
  ring

theorem exp_neg_centered_log_eq_rpow
    {r : ℝ} (hr : 0 < r) (p c : ℝ) :
    Real.exp (-p * (Real.log r - c)) =
      Real.exp (p * c) * r ^ (-p) := by
  simpa only [neg_mul, neg_neg] using exp_centered_log_eq_rpow hr (-p) c

variable {α : Type*} [MeasurableSpace α]

theorem integral_exp_centered_log_eq_rpow
    (μ : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) (p c : ℝ) :
    (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μ) =
      Real.exp (-p * c) * ∫ x, u x ^ p ∂μ := by
  calc
    (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μ) =
        ∫ x, Real.exp (-p * c) * u x ^ p ∂μ := by
          exact integral_congr_ae (ae_of_all μ fun x =>
            exp_centered_log_eq_rpow (hpos x) p c)
    _ = Real.exp (-p * c) * ∫ x, u x ^ p ∂μ := integral_const_mul _ _

theorem integral_exp_neg_centered_log_eq_rpow
    (μ : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) (p c : ℝ) :
    (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μ) =
      Real.exp (p * c) * ∫ x, u x ^ (-p) ∂μ := by
  calc
    (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μ) =
        ∫ x, Real.exp (p * c) * u x ^ (-p) ∂μ := by
          exact integral_congr_ae (ae_of_all μ fun x =>
            exp_neg_centered_log_eq_rpow (hpos x) p c)
    _ = Real.exp (p * c) * ∫ x, u x ^ (-p) ∂μ := integral_const_mul _ _

theorem crossover_of_centered_exponential_bounds
    (μplus μminus : Measure α) (u : α → ℝ)
    (hpos : ∀ x, 0 < u x) {p c Aplus Aminus : ℝ}
    (hAplus : 0 ≤ Aplus)
    (hplus : (∫ x, Real.exp (p * (Real.log (u x) - c)) ∂μplus) ≤ Aplus)
    (hminus : (∫ x, Real.exp (-p * (Real.log (u x) - c)) ∂μminus) ≤ Aminus) :
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) ≤
      Aplus * Aminus := by
  have hplus' :
      Real.exp (-p * c) * (∫ x, u x ^ p ∂μplus) ≤ Aplus := by
    rw [← integral_exp_centered_log_eq_rpow μplus u hpos p c]
    exact hplus
  have hminus' :
      Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus) ≤ Aminus := by
    rw [← integral_exp_neg_centered_log_eq_rpow μminus u hpos p c]
    exact hminus
  have hmoment_minus : 0 ≤ ∫ x, u x ^ (-p) ∂μminus :=
    integral_nonneg fun x => Real.rpow_nonneg (hpos x).le _
  have hleft_minus :
      0 ≤ Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus) :=
    mul_nonneg (Real.exp_pos _).le hmoment_minus
  have hmul := mul_le_mul hplus' hminus' hleft_minus hAplus
  have hexp : Real.exp (-p * c) * Real.exp (p * c) = 1 := by
    rw [← Real.exp_add]
    have : -p * c + p * c = 0 := by ring
    rw [this, Real.exp_zero]
  calc
    (∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus) =
        (Real.exp (-p * c) * Real.exp (p * c)) *
          ((∫ x, u x ^ p ∂μplus) * (∫ x, u x ^ (-p) ∂μminus)) := by
            rw [hexp, one_mul]
    _ = (Real.exp (-p * c) * (∫ x, u x ^ p ∂μplus)) *
          (Real.exp (p * c) * (∫ x, u x ^ (-p) ∂μminus)) := by ring
    _ ≤ Aplus * Aminus := hmul

theorem weak_harnack_power_of_crossover
    {u A D B C p : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hp : 0 < p)
    (hcrossover : A * D ≤ C)
    (hreciprocal : u⁻¹ ≤ B * D ^ (1 / p)) :
    A ≤ C * B ^ p * u ^ p := by
  have hDne : D ≠ 0 := by
    intro hzero
    subst D
    rw [Real.zero_rpow (div_pos one_pos hp).ne', mul_zero] at hreciprocal
    exact (not_le_of_gt (inv_pos.mpr hu)) hreciprocal
  have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr hu.le) hreciprocal hp.le
  have hrpow' : (u ^ p)⁻¹ ≤ B ^ p * D := by
    rw [Real.inv_rpow hu.le, Real.mul_rpow hB (Real.rpow_nonneg hD _)] at hrpow
    have hpinv : 1 / p = p⁻¹ := one_div p
    rw [hpinv, Real.rpow_inv_rpow hD hp.ne'] at hrpow
    exact hrpow
  have hup : 0 < u ^ p := Real.rpow_pos_of_pos hu p
  have hone : 1 ≤ B ^ p * D * u ^ p := by
    calc
      1 = (u ^ p)⁻¹ * u ^ p := (inv_mul_cancel₀ hup.ne').symm
      _ ≤ (B ^ p * D) * u ^ p :=
        mul_le_mul_of_nonneg_right hrpow' hup.le
      _ = B ^ p * D * u ^ p := rfl
  have hA_le : A ≤ A * (B ^ p * D * u ^ p) := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * (B ^ p * D * u ^ p) := mul_le_mul_of_nonneg_left hone hA
  have hfactor : 0 ≤ B ^ p * u ^ p :=
    mul_nonneg (Real.rpow_nonneg hB _) hup.le
  calc
    A ≤ A * (B ^ p * D * u ^ p) := hA_le
    _ = (A * D) * (B ^ p * u ^ p) := by ring
    _ ≤ C * (B ^ p * u ^ p) :=
      mul_le_mul_of_nonneg_right hcrossover hfactor
    _ = C * B ^ p * u ^ p := by ring

theorem weak_harnack_of_crossover
    {u A D B C p : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hp : 0 < p)
    (hcrossover : A * D ≤ C)
    (hreciprocal : u⁻¹ ≤ B * D ^ (1 / p)) :
    A ^ (1 / p) ≤ C ^ (1 / p) * B * u := by
  have hpower := weak_harnack_power_of_crossover
    hu hA hD hB hp hcrossover hreciprocal
  have hexponent : 0 ≤ 1 / p := (div_pos one_pos hp).le
  have hroot := Real.rpow_le_rpow hA hpower hexponent
  have hup : 0 ≤ u := hu.le
  have hright : 0 ≤ C * B ^ p :=
    mul_nonneg hC (Real.rpow_nonneg hB _)
  rw [show C * B ^ p * u ^ p = (C * B ^ p) * (u ^ p) by ring,
    Real.mul_rpow hright (Real.rpow_nonneg hup _),
    Real.mul_rpow hC (Real.rpow_nonneg hB _)] at hroot
  rw [← Real.rpow_mul hB, ← Real.rpow_mul hup] at hroot
  have hcancel : p * (1 / p) = 1 := by field_simp [hp.ne']
  rw [hcancel, Real.rpow_one, Real.rpow_one] at hroot
  simpa only [mul_assoc] using hroot

end DifferentialGeometry.Analysis.Parabolic.Moser

end
