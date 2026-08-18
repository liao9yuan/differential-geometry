import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

theorem mul_three_le_mul_three {a b c A B C : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haA : a ≤ A) (hbB : b ≤ B) (hcC : c ≤ C) :
    a * b * c ≤ A * B * C :=
  mul_le_mul (mul_le_mul haA hbB hb hA) hcC hc (mul_nonneg hA hB)

theorem quadratic_product_bounds (Y Z P : ℝ) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hP : P = (1 + Y) ^ 2 * (1 + Z) ^ 2) :
    Z ≤ P ∧ Y ≤ P ∧ (1 + Y) * Z ≤ P ∧ (1 + Y) * Y ≤ P ∧
      (1 + Z) * Y ≤ P ∧ (1 + Y) * (1 + Y) * Z ≤ P ∧
      (1 + Y) * (1 + Z) * Y ≤ P ∧ (1 + Y) * (1 + Z) * Z ≤ P := by
  rw [hP]
  have m1 : (0 : ℝ) ≤ Y * Z := mul_nonneg hY hZ
  have m2 : (0 : ℝ) ≤ Y * Y := mul_nonneg hY hY
  have m3 : (0 : ℝ) ≤ Z * Z := mul_nonneg hZ hZ
  have m4 : (0 : ℝ) ≤ Y * Y * Z := mul_nonneg m2 hZ
  have m5 : (0 : ℝ) ≤ Y * Z * Z := mul_nonneg m1 hZ
  have m6 : (0 : ℝ) ≤ Y * Y * Z * Z := mul_nonneg m4 hZ
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end DifferentialGeometry.Analysis
