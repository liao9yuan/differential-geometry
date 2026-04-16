import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Time Derivative on Tensors

∂_t on (r,s) tensors, defined pointwise via `dt_apply`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor

-- ============================================================
-- ∂_t on (r,s)-tensors: pointwise definition
-- ============================================================

section DtTensor

variable {R V : Type*} {A Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]

/-- Time derivative of a time-dependent (r,s)-tensor. Defined pointwise:
    (dt_tensor t T)(vs)(αs) = dt_apply(s ↦ T(s)(vs)(αs)) at t.

    Multilinearity follows from T(s) being multilinear for each s,
    combined with dt_apply being additive and killing R-constants. -/
noncomputable def dt_tensor (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s) : TensorData R V r s where
  toFun vs :=
    { toFun := fun αs => td.dt_apply (fun s => T s vs αs) t
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        have h : (fun s => T s vs (Function.update αs idx (β₁ + β₂))) =
            (fun s => T s vs (Function.update αs idx β₁)) +
            (fun s => T s vs (Function.update αs idx β₂)) := by
          ext s; exact (T s vs).map_update_add αs idx β₁ β₂
        rw [h, td.dt_apply_add]
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have h : (fun s => T s vs (Function.update αs idx (c • β))) =
            (fun s => c * T s vs (Function.update αs idx β)) := by
          ext s
          change T s vs (Function.update αs idx (c • β)) = c * T s vs (Function.update αs idx β)
          have := (T s vs).map_update_smul αs idx c β; rwa [smul_eq_mul] at this
        rw [h]; exact td.dt_apply_const_mul c _ t }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    have h : (fun s => T s (Function.update vs idx (v₁ + v₂)) αs) =
        (fun s => T s (Function.update vs idx v₁) αs) +
        (fun s => T s (Function.update vs idx v₂) αs) := by
      ext s; exact congr_arg (· αs) ((T s).map_update_add vs idx v₁ v₂)
    rw [h, td.dt_apply_add]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    have h : (fun s => T s (Function.update vs idx (c • v)) αs) =
        (fun s => c * T s (Function.update vs idx v) αs) := by
      ext s; change T s (Function.update vs idx (c • v)) αs = c * T s (Function.update vs idx v) αs
      have := congr_arg (· αs) ((T s).map_update_smul vs idx c v)
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at this; exact this
    rw [h]; exact td.dt_apply_const_mul c _ t

-- ============================================================
-- Evaluation lemma and basic properties
-- ============================================================

/-- Evaluation: (dt_tensor t T)(vs)(αs) = dt_apply(s ↦ T(s)(vs)(αs)) at t. -/
theorem dt_tensor_eval (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s) (vs αs) :
    dt_tensor td t T vs αs = td.dt_apply (fun s => T s vs αs) t := by
  rfl

/-- ∂_t of a time-constant tensor is zero. -/
theorem dt_tensor_const (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : TensorData R V r s) :
    dt_tensor td t (fun _ => T) = 0 := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.zero_apply]
  exact td.dt_apply_const (T vs αs) t

/-- ∂_t is additive: ∂_t(T₁ + T₂) = ∂_t T₁ + ∂_t T₂. -/
theorem dt_tensor_add (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s) :
    dt_tensor td t (fun s => T₁ s + T₂ s) =
    dt_tensor td t T₁ + dt_tensor td t T₂ := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.add_apply]
  have h : (fun s => T₁ s vs αs + T₂ s vs αs) =
      (fun s => T₁ s vs αs) + (fun s => T₂ s vs αs) := rfl
  rw [h, td.dt_apply_add]

/-- ∂_t respects negation. -/
theorem dt_tensor_neg (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s) :
    dt_tensor td t (fun s => -T s) = -dt_tensor td t T := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.neg_apply]
  have h : (fun s => -(T s vs αs)) = -(fun s => T s vs αs) := rfl
  rw [h, td.dt_apply_neg]

/-- ∂_t respects subtraction. -/
theorem dt_tensor_sub (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s) :
    dt_tensor td t (fun s => T₁ s - T₂ s) =
    dt_tensor td t T₁ - dt_tensor td t T₂ := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.sub_apply]
  have h : (fun s => T₁ s vs αs - T₂ s vs αs) =
      (fun s => T₁ s vs αs) - (fun s => T₂ s vs αs) := rfl
  rw [h, td.dt_apply_sub]

/-- Leibniz rule for time-dependent scalar multiplication:
    ∂_t(f · T) = dt_apply(f) · T(t) + f(t) · ∂_t T. -/
theorem dt_tensor_smul (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (f : Time → R) (T : Time → TensorData R V r s) (vs αs) :
    dt_tensor td t (fun s => f s • T s) vs αs =
    td.dt_apply f t * (T t vs αs) + f t * dt_tensor td t T vs αs := by
  simp only [dt_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]
  rw [show (fun s => f s * T s vs αs) = f * (fun s => T s vs αs) from rfl]
  rw [td.dt_apply_mul]; ring

/-- ∂_t commutes with constant R-scalar multiplication:
    ∂_t(c · T) = c · ∂_t T for c ∈ R (not time-dependent). -/
theorem dt_tensor_smul_const (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (c : R) (T : Time → TensorData R V r s) :
    dt_tensor td t (fun s => c • T s) = c • dt_tensor td t T := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]
  have h : (fun s => c * T s vs αs) = (fun s => c * T s vs αs) := rfl
  exact td.dt_apply_const_mul c _ t

/-- Leibniz rule for tensor product:
    ∂_t(T₁ ⊗ T₂) = (∂_t T₁) ⊗ T₂(t) + T₁(t) ⊗ (∂_t T₂). -/
theorem dt_tensor_prod (td : TimeDerivativeData R A Time)
    (t : Time) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : Time → TensorData R V r₁ s₁) (T₂ : Time → TensorData R V r₂ s₂) :
    dt_tensor td t (fun s => tensor_prod (T₁ s) (T₂ s)) =
    tensor_prod (dt_tensor td t T₁) (T₂ t) +
    tensor_prod (T₁ t) (dt_tensor td t T₂) := by
  ext vs αs
  simp only [dt_tensor_eval, tensor_prod_eval, MultilinearMap.add_apply]
  set vs₁ := vs ∘ Fin.castAdd s₂; set vs₂ := vs ∘ Fin.natAdd s₁
  set ns₁ := αs ∘ Fin.castAdd r₂; set ns₂ := αs ∘ Fin.natAdd r₁
  rw [show (fun s => T₁ s vs₁ ns₁ * T₂ s vs₂ ns₂) =
      (fun s => T₁ s vs₁ ns₁) * (fun s => T₂ s vs₂ ns₂) from rfl]
  rw [td.dt_apply_mul]; ring

/-- ∂_t commutes with swap_covariant. -/
theorem dt_tensor_swap (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (i j : Fin s)
    (T : Time → TensorData R V r s) (vs αs) :
    dt_tensor td t (fun s => swap_covariant i j (T s)) vs αs =
    swap_covariant i j (dt_tensor td t T) vs αs := by
  simp only [dt_tensor_eval, swap_covariant_eval]

-- ============================================================
-- Trace interaction: dt commutes with tr (from TimeTrComm)
-- ============================================================

/-- ∂_t commutes with endomorphism trace.
    Direct corollary of the TimeTrComm hypothesis. -/
theorem dt_tr (td : TimeDerivativeData R A Time) (atr : AbstractTrace R V)
    (h_tt : TimeTrComm atr td)
    (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (h_char : ∀ (v : V) (α : V →ₗ[R] R),
      α (dL v) = td.dt_apply (fun s => α (L s v)) t) :
    td.dt_apply (fun s => atr.tr (L s)) t = atr.tr dL :=
  h_tt L dL t (fun v α => td.lift (fun s => α (L s v))) (td.lift (fun s => atr.tr (L s)))
    (fun v α s => td.eval_lift (fun s => α (L s v)) s)
    (fun s => td.eval_lift (fun s => atr.tr (L s)) s)
    h_char

end DtTensor
