import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false










noncomputable section

open RealInnerProductSpace

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E]



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



noncomputable def sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) : E :=
  hco.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual Real E).symm eta)



theorem sharp_eq_inverse {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    hco.sharp eta =
      Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B)
        ((InnerProductSpace.toDual Real E).symm eta) := by
  change hco.continuousLinearEquivOfBilin.symm _ =
    Ring.inverse
      (↑hco.continuousLinearEquivOfBilin.toUnit : E →L[Real] E) _
  rw [Ring.inverse_unit]
  rfl


@[simp] theorem apply_sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    B (hco.sharp eta) = eta := by
  apply ContinuousLinearMap.ext
  intro w
  rw [← hco.continuousLinearEquivOfBilin_apply]
  simp [sharp]


@[simp] theorem sharp_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (u : E) :
    hco.sharp (B u) = u := by
  apply hco.continuousLinearEquivOfBilin.injective
  apply ext_inner_right Real
  intro w
  rw [hco.continuousLinearEquivOfBilin_apply,
    hco.continuousLinearEquivOfBilin_apply]
  exact DFunLike.congr_fun (hco.apply_sharp (B u)) w


theorem sharp_sub {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta theta : E →L[Real] Real) :
    hco.sharp (eta - theta) = hco.sharp eta - hco.sharp theta := by
  simp [sharp]



theorem sharp_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (eta : E →L[Real] Real) :
    ‖hco.sharp eta‖ ≤ c⁻¹ * ‖eta‖ := by
  have h := hco.symm_norm_le hc hB ((InnerProductSpace.toDual Real E).symm eta)
  unfold sharp
  rw [← (InnerProductSpace.toDual Real E).symm.norm_map eta]
  exact h




theorem sharp_sub_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp eta‖ ≤
      cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
  have heq :
      hBco.sharp eta - hCco.sharp eta =
        hBco.sharp ((C - B) (hCco.sharp eta)) := by
    calc
      hBco.sharp eta - hCco.sharp eta =
          hBco.sharp (B (hBco.sharp eta - hCco.sharp eta)) :=
        (hBco.sharp_apply _).symm
      _ = hBco.sharp (B (hBco.sharp eta) - B (hCco.sharp eta)) := by
        rw [map_sub]
      _ = hBco.sharp (eta - B (hCco.sharp eta)) := by
        rw [hBco.apply_sharp]
      _ = hBco.sharp (C (hCco.sharp eta) - B (hCco.sharp eta)) := by
        rw [hCco.apply_sharp]
      _ = hBco.sharp ((C - B) (hCco.sharp eta)) := by
        rw [ContinuousLinearMap.sub_apply]
  rw [heq]
  calc
    ‖hBco.sharp ((C - B) (hCco.sharp eta))‖ ≤
        cB⁻¹ * ‖(C - B) (hCco.sharp eta)‖ :=
      hBco.sharp_norm_le hcB hB _
    _ ≤ cB⁻¹ * (‖C - B‖ * ‖hCco.sharp eta‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm (C - B) (hCco.sharp eta)
    _ ≤ cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
      gcongr
      exact hCco.sharp_norm_le hcC hC eta

end IsCoercive
