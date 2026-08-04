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

end DifferentialGeometry.Analysis.Parabolic.Moser

end
