/-
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Hom.PowersetCard

/-!
# Equivalences for `Fin n`
-/

namespace Fin

variable {m n o : ℕ}

def finAssoc {m n p : ℕ} : Fin (m + n + p) ≃ Fin (m + (n + p)) :=
  finCongr <| Nat.add_assoc m n p

def finAddFlipAssoc {m n p : ℕ} : Fin (m + p + n) ≃ Fin (m + (n + p)) := by
  refine finCongr ?eq
  rw [Nat.add_right_comm]
  exact Nat.add_assoc m n p

theorem finAddFlip_finSumFinEquiv {m n : ℕ} (a : Fin m ⊕ Fin n) :
    finAddFlip (finSumFinEquiv a) = finSumFinEquiv (Equiv.sumComm _ _ a)  := by
  refine Eq.symm (DFunLike.congr_arg finSumFinEquiv ?h₂)
  rw [Equiv.congr_arg rfl]
  refine (Equiv.apply_eq_iff_eq (Equiv.sumComm (Fin m) (Fin n))).mpr ?h₂.a
  rw [Equiv.symm_apply_apply]


def finAddCongr : Fin (m + n) ≃ Fin (n + m) := finCongr (add_comm m n)

@[simp]
lemma finAddCongr_finAddCongr (i : Fin (m + n)) :
    finAddCongr (finAddCongr i) = i :=
  rfl

@[simp]
lemma finAddCongr_symm_finAddCongr_symm (i : Fin (m + n)) :
    finAddCongr.symm (finAddCongr.symm i) = i :=
  rfl

def finSumCongr : Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m where
  toFun x := x.swap
  invFun x := x.swap
  left_inv := Sum.swap_swap
  right_inv := Sum.swap_swap

@[simp]
lemma finSumCongr_symm_inl_inr (x : Fin m) :
    finSumCongr.symm (Sum.inl x) = (Sum.inr x : Fin n ⊕ Fin m)
  := rfl

@[simp]
lemma finSumCongr_symm_inr_inl (x : Fin n) :
    finSumCongr.symm (Sum.inr x) = (Sum.inl x : Fin n ⊕ Fin m)
  := rfl

/-!
## Multi-index Kronecker delta
-/

/-- The generalized Kronecker delta for multi-indices `I J : Fin k → Fin n`.

This is the determinant of the `k × k` matrix whose `(i, j)` entry is `1` if `I i = J j`
and `0` otherwise.

When `I = J ∘ σ` for some permutation `σ : Equiv.Perm (Fin k)`, this equals `Equiv.Perm.sign σ`.
If no such permutation exists, it equals `0`. -/
noncomputable def multiKroneckerDelta {R : Type*} [CommRing R] {k n : ℕ}
    (I J : Fin k → Fin n) : R :=
  Matrix.det (fun i j : Fin k => if I i = J j then 1 else 0)

variable {R : Type*} [CommRing R] {k n : ℕ}

/-- If `J` is injective and `I = J ∘ σ` for a permutation `σ`, then the generalized
Kronecker delta equals the sign of `σ`. -/
theorem multiKroneckerDelta_comp_perm
    {J : Fin k → Fin n} (hJ : Function.Injective J)
    (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (J ∘ ⇑σ) J = (Equiv.Perm.sign σ : R) := by
  unfold multiKroneckerDelta
  simp only [Function.comp, hJ.eq_iff]
  rw [show (fun i j : Fin k => if σ i = j then (1 : R) else 0) =
    (1 : Matrix (Fin k) (Fin k) R).submatrix (⇑σ) id from by
    ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]]
  rw [Matrix.det_permute, Matrix.det_one, mul_one]

/-- If `I` is not injective (has a repeated index), the generalized
Kronecker delta is zero. -/
theorem multiKroneckerDelta_eq_zero_of_not_injective_left
    {I J : Fin k → Fin n} (hI : ¬Function.Injective I) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨i₁, i₂, heq, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (funext fun j => by rw [heq])

/-- If `J` is not injective (has a repeated index), the generalized
Kronecker delta is zero. -/
theorem multiKroneckerDelta_eq_zero_of_not_injective_right
    {I J : Fin k → Fin n} (hJ : ¬Function.Injective J) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨j₁, j₂, heq, hne⟩ := Function.not_injective_iff.mp hJ
  exact Matrix.det_zero_of_column_eq hne (fun r => by rw [heq])

/-- If no permutation `σ` satisfies `I = J ∘ σ`, then the generalized
Kronecker delta is zero. -/
theorem multiKroneckerDelta_eq_zero
    {I J : Fin k → Fin n}
    (h : ∀ σ : Equiv.Perm (Fin k), I ≠ J ∘ ⇑σ) :
    multiKroneckerDelta (R := R) I J = 0 := by
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · -- Both injective but no perm relates them; some row must be all zeros.
      have ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra hall
        push_neg at hall
        choose f hf using hall
        have hf_inj : Function.Injective f :=
          fun a b hab => hI (by rw [hf a, hf b, hab])
        exact h (Equiv.ofBijective f
          ((Fintype.bijective_iff_injective_and_card f).mpr
            ⟨hf_inj, rfl⟩)) (funext hf)
      unfold multiKroneckerDelta
      exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hi j))
    · exact multiKroneckerDelta_eq_zero_of_not_injective_right hJ
  · exact multiKroneckerDelta_eq_zero_of_not_injective_left hI

/-- The generalized Kronecker delta is symmetric:
`multiKroneckerDelta I J = multiKroneckerDelta J I`.
This follows from `det M = det Mᵀ`. -/
theorem multiKroneckerDelta_symm (I J : Fin k → Fin n) :
    multiKroneckerDelta (R := R) I J = multiKroneckerDelta J I := by
  unfold multiKroneckerDelta
  conv_lhs => rw [← Matrix.det_transpose]
  congr 1; ext i j
  simp [Matrix.transpose_apply, eq_comm]

/-!
## Order embedding lemmas
-/

/-- `Fin k ↪o Fin n` is a finite type, via the equivalence with
`Set.powersetCard (Fin n) k`. -/
noncomputable instance : Fintype (Fin k ↪o Fin n) :=
  Fintype.ofEquiv _
    (Set.powersetCard.ofFinEmbEquiv
      (I := Fin n) (n := k)).symm

/-- Two order embeddings `Fin k ↪o Fin n` with the same range
are equal. -/
theorem orderEmb_eq_of_range_eq
    {I J : Fin k ↪o Fin n}
    (h : Set.range (⇑I) = Set.range (⇑J)) : I = J :=
  DFunLike.ext'
    ((I.strictMono.range_inj J.strictMono).mp h)

/-- For order embeddings `I ≠ J`, no permutation `σ` satisfies
`↑I = ↑J ∘ σ`. -/
theorem orderEmb_ne_comp_perm
    {I J : Fin k ↪o Fin n} (hIJ : I ≠ J)
    (σ : Equiv.Perm (Fin k)) :
    (⇑I : Fin k → Fin n) ≠ ⇑J ∘ ⇑σ := by
  intro heq; apply hIJ; apply orderEmb_eq_of_range_eq
  rw [heq, Set.range_comp,
    Equiv.range_eq_univ, Set.image_univ]

end Fin
