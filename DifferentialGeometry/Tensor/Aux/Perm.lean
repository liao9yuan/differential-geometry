/-
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Aux.Fin
import Mathlib.LinearAlgebra.Alternating.DomCoprod

namespace Equiv.Perm

open Fin

variable {m n p : ℕ}

@[simps!]
def addAssocPerm : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p) ≃ Equiv.Perm (Fin m ⊕ Fin n ⊕ Fin p) :=
    Equiv.permCongr (Equiv.sumAssoc (Fin m) (Fin n) (Fin p))

@[simp]
lemma addAssocPerm_symm_addAssocPerm (σ₁ : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p)) :
    addAssocPerm.symm (addAssocPerm σ₁) = σ₁ := by
  exact Equiv.symm_apply_apply addAssocPerm σ₁

@[simp]
lemma sign_addAssocPerm (σ₁ : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p)) :
    Equiv.Perm.sign (addAssocPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [addAssocPerm, Equiv.Perm.sign_permCongr]


def addCongrPerm : Equiv.Perm (Fin (m + n)) ≃ Equiv.Perm (Fin (n + m)) :=
  Equiv.permCongr finAddCongr

def sumCongrPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr finSumCongr

@[simp]
lemma sumCongrPerm_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCongrPerm (sumCongrPerm σ₁) = σ₁ := by
  ext i
  simp [sumCongrPerm, finSumCongr]

open Equiv.Perm in
lemma sumCongrPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCongrPerm, Equiv.permCongr_def]
  rw [inv_def, Equiv.Perm.mul_def]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨ σ, τ, h ⟩
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ , σ
  ext (x | y)
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.symm_symm]
    apply_fun (fun f => f (Sum.inr x)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inr, inv_def, coe_mul, Function.comp_apply] at h
    rw [← Equiv.symm_apply_eq, finSumCongr_symm_inl_inr, finSumCongr_symm_inl_inr, h]
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.symm_symm]
    apply_fun (fun f => f (Sum.inl y)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inl, inv_def, coe_mul, Function.comp_apply] at h
    rw [← Equiv.symm_apply_eq, finSumCongr_symm_inr_inl, finSumCongr_symm_inr_inl, h]

@[simp]
lemma sign_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCongrPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCongrPerm, Equiv.Perm.sign_permCongr]

open Equiv.Perm in
@[simps!]
def finAddCongr_equiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ Perm.sumCongrPerm) Perm.sumCongrPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ Perm.sumCongrPerm) Perm.sumCongrPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, Perm.sumCongrPerm_sumCongrPerm]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, Perm.sumCongrPerm_sumCongrPerm]

-- UNUSED functionality
@[simps!]
def sumCommPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr (Equiv.sumComm (Fin m) (Fin n))

-- UNUSED functionality
@[simp]
lemma sumCommPerm_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCommPerm (sumCommPerm σ₁) = σ₁ := by
  ext i
  simp

-- UNUSED functionality
open Equiv.Perm in
lemma sumCommPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPerm, Equiv.permCongr_def]
  rw [inv_def, Equiv.Perm.mul_def]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨ σ, τ, h ⟩
  simp only [Equiv.sumComm_symm, MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ , σ
  ext (x | y)
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, Equiv.sumComm_apply,
    Sum.swap_inl, Equiv.symm_trans_apply, Equiv.sumComm_symm, Sum.swap_swap]
    apply_fun (fun f => f (Sum.inr x)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inr, inv_def, coe_mul, Function.comp_apply] at h
    rw[← h]
    rfl
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply, Equiv.sumComm_apply,
    Sum.swap_inr, Equiv.symm_trans_apply, Equiv.sumComm_symm, Sum.swap_swap]
    apply_fun (fun f => f (Sum.inl y)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inl, inv_def, coe_mul, Function.comp_apply] at  h
    rw[← h]
    rfl

-- UNUSED functionality
@[simp]
lemma sign_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCommPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCommPerm, Equiv.Perm.sign_permCongr]

-- UNUSED functionality
@[simps!]
def finAddFlip_equiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, sumCommPerm_sumCommPerm]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, sumCommPerm_sumCommPerm]

-- UNUSED functionality
@[simps!]
def sumCommPerm_eqFin : Equiv.Perm (Fin m ⊕ Fin m) ≃ Equiv.Perm (Fin m ⊕ Fin m) :=
  MulAut.conj (Equiv.sumComm (Fin m) (Fin m))

-- UNUSED functionality
@[simp]
lemma sumComm_inv : (Equiv.sumComm (Fin m) (Fin m))⁻¹ = (Equiv.sumComm (Fin m) (Fin m)) := by
  ext i
  simp [Equiv.Perm.inv_def]

-- UNUSED functionality
@[simp]
lemma sumCommPerm_eqFin_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    sumCommPerm_eqFin (sumCommPerm_eqFin σ₁) = σ₁ := by
  ext i
  simp

-- UNUSED functionality
lemma sumCommPerm_eqFin_spec (a b : Equiv.Perm (Fin m ⊕ Fin m))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin m)).range) a b) :
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPerm_eqFin) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPerm_eqFin) b
    := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPerm_eqFin, EquivLike.coe_coe, MulAut.conj_apply, sumComm_inv,
    mul_assoc, mul_inv_rev]
  have this (c) : Equiv.sumComm (Fin m) (Fin m) * (Equiv.sumComm (Fin m) (Fin m) * c) = c := by
    ext
    simp [mul_def]
  rw[this]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨σ, τ, h⟩
  rw[← mul_assoc _ b, ← h]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ, σ
  ext (x|y) <;> simp

-- UNUSED functionality
@[simp]
lemma sign_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    Equiv.Perm.sign (sumCommPerm_eqFin σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCommPerm_eqFin, EquivLike.coe_coe, MulAut.conj_apply, sumComm_inv,
    Equiv.Perm.sign_mul]
  rw[mul_comm, ← mul_assoc]
  simp

open Equiv.Perm in
@[simps]
def finAddFlip_equiv_eqFin : ModSumCongr (Fin m) (Fin m) ≃ ModSumCongr (Fin m) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPerm_eqFin) sumCommPerm_eqFin_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPerm_eqFin) sumCommPerm_eqFin_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, sumCommPerm_eqFin_sumCommPerm_eqFin]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    simp only [Function.comp_apply, sumCommPerm_eqFin_sumCommPerm_eqFin]
