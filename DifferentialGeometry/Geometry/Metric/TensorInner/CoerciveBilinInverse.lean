import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false

/-!
# Quantitative inverse bound for a coercive bilinear form

An explicit quadratic coercivity constant bounds the inverse of the
Lax--Milgram equivalence.  This is the algebraic estimate used to turn a
uniform lower metric comparison into a uniform bound for the corresponding
sharp operator.
-/

noncomputable section

open RealInnerProductSpace

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E]

/-- If `B v v` dominates `c * ||v||^2`, then the inverse Lax--Milgram map has
pointwise norm at most `c^{-1}`. -/
theorem symm_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (xi : E) :
    ‖hco.continuousLinearEquivOfBilin.symm xi‖ ≤ c⁻¹ * ‖xi‖ := by
  let u := hco.continuousLinearEquivOfBilin.symm xi
  have heu : hco.continuousLinearEquivOfBilin u = xi :=
    hco.continuousLinearEquivOfBilin.apply_symm_apply xi
  change ‖u‖ ≤ c⁻¹ * ‖xi‖
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg xi)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖xi‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = inner Real (hco.continuousLinearEquivOfBilin u) u :=
          (hco.continuousLinearEquivOfBilin_apply u u).symm
        _ = inner Real xi u := by rw [heu]
        _ ≤ ‖xi‖ * ‖u‖ := real_inner_le_norm xi u
    calc
      ‖u‖ ≤ ‖xi‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖xi‖ := by rw [div_eq_mul_inv, mul_comm]

end IsCoercive
