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
    combined with dt_apply being additive and killing R-constants on smooth
    scalar families. The hypothesis `hT` asserts the scalar evaluation at every
    point is a smooth family — propagated to dt_apply's internal calls. -/
noncomputable def dt_tensor (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) : TensorData R V r s where
  toFun vs :=
    { toFun := fun αs => td.dt_apply (fun s => T s vs αs) t
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        have h : (fun s => T s vs (Function.update αs idx (β₁ + β₂))) =
            (fun s => T s vs (Function.update αs idx β₁)) +
            (fun s => T s vs (Function.update αs idx β₂)) := by
          ext s; exact (T s vs).map_update_add αs idx β₁ β₂
        rw [h, td.dt_apply_add _ _ _
          (hT vs (Function.update αs idx β₁))
          (hT vs (Function.update αs idx β₂))]
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have h : (fun s => T s vs (Function.update αs idx (c • β))) =
            (fun s => c * T s vs (Function.update αs idx β)) := by
          ext s
          change T s vs (Function.update αs idx (c • β)) = c * T s vs (Function.update αs idx β)
          have := (T s vs).map_update_smul αs idx c β; rwa [smul_eq_mul] at this
        rw [h]
        exact td.dt_apply_const_mul c _ t (hT vs (Function.update αs idx β)) }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    have h : (fun s => T s (Function.update vs idx (v₁ + v₂)) αs) =
        (fun s => T s (Function.update vs idx v₁) αs) +
        (fun s => T s (Function.update vs idx v₂) αs) := by
      ext s; exact congr_arg (· αs) ((T s).map_update_add vs idx v₁ v₂)
    rw [h, td.dt_apply_add _ _ _
      (hT (Function.update vs idx v₁) αs)
      (hT (Function.update vs idx v₂) αs)]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    have h : (fun s => T s (Function.update vs idx (c • v)) αs) =
        (fun s => c * T s (Function.update vs idx v) αs) := by
      ext s; change T s (Function.update vs idx (c • v)) αs = c * T s (Function.update vs idx v) αs
      have := congr_arg (· αs) ((T s).map_update_smul vs idx c v)
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at this; exact this
    rw [h]
    exact td.dt_apply_const_mul c _ t (hT (Function.update vs idx v) αs)

-- ============================================================
-- Evaluation lemma and basic properties
-- ============================================================

/-- Evaluation: (dt_tensor t T)(vs)(αs) = dt_apply(s ↦ T(s)(vs)(αs)) at t. -/
theorem dt_tensor_eval (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) (vs αs) :
    dt_tensor td t T hT vs αs = td.dt_apply (fun s => T s vs αs) t := by
  rfl

/-- ∂_t of a time-constant tensor is zero. -/
theorem dt_tensor_const (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : TensorData R V r s) :
    dt_tensor td t (fun _ => T)
      (fun vs αs => td.isSmoothFam_const (T vs αs)) = 0 := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.zero_apply]
  exact td.dt_apply_const (T vs αs) t

/-- ∂_t is additive: ∂_t(T₁ + T₂) = ∂_t T₁ + ∂_t T₂. -/
theorem dt_tensor_add (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs)) :
    dt_tensor td t (fun s => T₁ s + T₂ s)
      (fun vs αs => td.isSmoothFam_add _ _ (hT₁ vs αs) (hT₂ vs αs)) =
    dt_tensor td t T₁ hT₁ + dt_tensor td t T₂ hT₂ := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.add_apply]
  have h : (fun s => T₁ s vs αs + T₂ s vs αs) =
      (fun s => T₁ s vs αs) + (fun s => T₂ s vs αs) := rfl
  rw [h, td.dt_apply_add _ _ _ (hT₁ vs αs) (hT₂ vs αs)]

/-- ∂_t respects negation. -/
theorem dt_tensor_neg (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) :
    dt_tensor td t (fun s => -T s)
      (fun vs αs => td.isSmoothFam_neg _ (hT vs αs)) = -dt_tensor td t T hT := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.neg_apply]
  have h : (fun s => -(T s vs αs)) = -(fun s => T s vs αs) := rfl
  rw [h, td.dt_apply_neg _ _ (hT vs αs)]

/-- ∂_t respects subtraction. -/
theorem dt_tensor_sub (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs)) :
    dt_tensor td t (fun s => T₁ s - T₂ s)
      (fun vs αs => td.isSmoothFam_sub _ _ (hT₁ vs αs) (hT₂ vs αs)) =
    dt_tensor td t T₁ hT₁ - dt_tensor td t T₂ hT₂ := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.sub_apply]
  have h : (fun s => T₁ s vs αs - T₂ s vs αs) =
      (fun s => T₁ s vs αs) - (fun s => T₂ s vs αs) := rfl
  rw [h, td.dt_apply_sub _ _ _ (hT₁ vs αs) (hT₂ vs αs)]

/-- Leibniz rule for time-dependent scalar multiplication:
    ∂_t(f · T) = dt_apply(f) · T(t) + f(t) · ∂_t T. -/
theorem dt_tensor_smul (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (f : Time → R) (T : Time → TensorData R V r s)
    (hf : td.isSmoothFam f)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (vs αs) :
    dt_tensor td t (fun s => f s • T s)
      (fun vs αs => td.isSmoothFam_mul _ _ hf (hT vs αs)) vs αs =
    td.dt_apply f t * (T t vs αs) + f t * dt_tensor td t T hT vs αs := by
  simp only [dt_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]
  rw [show (fun s => f s * T s vs αs) = f * (fun s => T s vs αs) from rfl]
  rw [td.dt_apply_mul _ _ _ hf (hT vs αs)]; ring

/-- ∂_t commutes with constant R-scalar multiplication:
    ∂_t(c · T) = c · ∂_t T for c ∈ R (not time-dependent). -/
theorem dt_tensor_smul_const (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (c : R) (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) :
    dt_tensor td t (fun s => c • T s)
      (fun vs αs => td.isSmoothFam_const_mul c _ (hT vs αs)) =
    c • dt_tensor td t T hT := by
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]
  exact td.dt_apply_const_mul c _ t (hT vs αs)

/-- Leibniz rule for tensor product:
    ∂_t(T₁ ⊗ T₂) = (∂_t T₁) ⊗ T₂(t) + T₁(t) ⊗ (∂_t T₂). -/
theorem dt_tensor_prod (td : TimeDerivativeData R A Time)
    (t : Time) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : Time → TensorData R V r₁ s₁) (T₂ : Time → TensorData R V r₂ s₂)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs))
    (hT_prod : ∀ vs αs, td.isSmoothFam
      (fun τ => tensor_prod (T₁ τ) (T₂ τ) vs αs)) :
    dt_tensor td t (fun s => tensor_prod (T₁ s) (T₂ s)) hT_prod =
    tensor_prod (dt_tensor td t T₁ hT₁) (T₂ t) +
    tensor_prod (T₁ t) (dt_tensor td t T₂ hT₂) := by
  ext vs αs
  simp only [dt_tensor_eval, tensor_prod_eval, MultilinearMap.add_apply]
  set vs₁ := vs ∘ Fin.castAdd s₂; set vs₂ := vs ∘ Fin.natAdd s₁
  set ns₁ := αs ∘ Fin.castAdd r₂; set ns₂ := αs ∘ Fin.natAdd r₁
  rw [show (fun s => T₁ s vs₁ ns₁ * T₂ s vs₂ ns₂) =
      (fun s => T₁ s vs₁ ns₁) * (fun s => T₂ s vs₂ ns₂) from rfl]
  rw [td.dt_apply_mul _ _ _ (hT₁ vs₁ ns₁) (hT₂ vs₂ ns₂)]; ring

/-- ∂_t commutes with swap_covariant. -/
theorem dt_tensor_swap (td : TimeDerivativeData R A Time)
    (t : Time) {r s : ℕ} (i j : Fin s)
    (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hT_swap : ∀ vs αs, td.isSmoothFam (fun τ => swap_covariant i j (T τ) vs αs))
    (vs αs) :
    dt_tensor td t (fun s => swap_covariant i j (T s)) hT_swap vs αs =
    swap_covariant i j (dt_tensor td t T hT) vs αs := by
  simp only [dt_tensor_eval, swap_covariant_eval]

-- ============================================================
-- Trace interaction: dt commutes with tr (from TimeTrComm)
-- ============================================================

/-- ∂_t commutes with endomorphism trace.
    Direct corollary of the TimeTrComm hypothesis. Requires smoothness of
    the scalar-valued families `α (L s v)` and `tr (L s)` so that
    `eval_lift` applies. -/
theorem dt_tr (td : TimeDerivativeData R A Time) (atr : AbstractTrace R V)
    (h_tt : TimeTrComm atr td)
    (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (h_αLv_smooth : ∀ (v : V) (α : V →ₗ[R] R),
      td.isSmoothFam (fun s => α (L s v)))
    (h_trL_smooth : td.isSmoothFam (fun s => atr.tr (L s)))
    (h_char : ∀ (v : V) (α : V →ₗ[R] R),
      α (dL v) = td.dt_apply (fun s => α (L s v)) t) :
    td.dt_apply (fun s => atr.tr (L s)) t = atr.tr dL :=
  h_tt L dL t (fun v α => td.lift (fun s => α (L s v))) (td.lift (fun s => atr.tr (L s)))
    (fun v α s => td.eval_lift _ (h_αLv_smooth v α) s)
    (fun s => td.eval_lift _ h_trL_smooth s)
    h_char

end DtTensor
