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
## Interaction of `addCases` with `succAbove`

These lemmas describe what happens when you delete an element from a concatenated
multi-index `addCases f g`. Deleting from the left block gives `addCases (f ∘ succAbove i) g`;
deleting from the right block gives `addCases f (g ∘ succAbove j)` up to a `Fin.cast`.

These are the core index-juggling facts needed for the graded Leibniz rule
`ι_x(α ∧ β) = (ι_x α) ∧ β + (-1)^|α| α ∧ (ι_x β)` applied to elementary covectors.
-/

/-- Deleting an element from the left block of `addCases I J` (at position `castAdd`):
`(addCases I J) ∘ succAbove (castAdd (n+1) i) = (addCases (I ∘ succAbove i) J) ∘ cast _`.
The cast accounts for `(m + n + 1) ≠ (m + (n + 1))` definitionally. -/
theorem addCases_succAbove_castAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (i : Fin (m' + 1))
    (k : Fin (m' + n' + 1)) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.castAdd (n' + 1) i).succAbove
        (Fin.cast (show m' + n' + 1 = m' + 1 + n' from by omega) k)) =
    (Fin.addCases (f ∘ i.succAbove) g : Fin (m' + (n' + 1)) → α) k := by
  -- Work entirely at the Fin.val level. Both sides are `f _` or `g _` depending
  -- on whether the index falls in the left or right block.
  -- Key val facts (all definitional or one-step simp):
  set p := (Fin.castAdd (n' + 1) i) with hp_def
  set kc := Fin.cast (show m' + n' + 1 = m' + 1 + n' from by omega) k with hkc_def
  -- val equalities
  have hvp : p.val = i.val := Fin.val_castAdd _ _
  have hvkc : kc.val = k.val := rfl
  -- Case split on succAbove (which branch: castSucc or succ)
  simp only [Fin.succAbove]
  split <;> rename_i h_sa
  · -- succAbove gave castSucc: result has val = kc.val = k.val
    have hvsa : (p.succAbove kc).val = k.val := by
      simp [Fin.succAbove, h_sa, Fin.val_castSucc, hvkc]
    -- Now determine which addCases branch on both sides
    simp only [Fin.addCases, Function.comp]
    split <;> rename_i h_lhs <;> split <;> rename_i h_rhs
    · -- Both in left block: show f args match
      congr 1; ext
      simp only [Fin.val_castLT, hvsa, Fin.succAbove, Fin.val_castSucc, Fin.val_succ]
      split <;> rename_i h_inner <;>
        simp_all [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, hvkc] <;> omega
    · -- LHS left, RHS right: contradiction
      exfalso; simp_all [Fin.lt_def, hvsa]; omega
    · -- LHS right, RHS left: contradiction
      exfalso; simp_all [Fin.lt_def, hvsa]; omega
    · -- Both in right block: g ⟨kc.val - (m'+1), _⟩ = g ⟨k.val - m', _⟩
      -- Since kc.val = k.val and the succAbove gave castSucc (val unchanged),
      -- both sides have val = k.val - m'. Need k.val - (m'+1) = k.val - m' when
      -- addCases subtracts the left block size, which differs by 1 due to succAbove.
      -- Actually the LHS subtracts (m'+1) but the value is hvsa = k.val,
      -- and the RHS subtracts m' from k.val. These differ unless...
      -- The LHS addCases has blocks (m'+1) + (n'+1) and subtracts (m'+1).
      -- The RHS addCases has blocks m' + (n'+1) and subtracts m'.
      -- Both give k.val - (m'+1) vs k.val - m'. Not equal!
      -- But succAbove shifted: LHS value is k.val (castSucc), not k.val + 1.
      -- LHS: addCases f g at (castAdd i).succAbove(cast k) = addCases f g at val k.val
      -- In addCases with blocks (m'+1)+(n'+1), index k.val ≥ m'+1 gives g(subNat(m'+1,...))
      -- = g ⟨k.val - (m'+1), _⟩
      -- RHS: addCases (f∘succAbove) g at k, with blocks m'+(n'+1), index k.val ≥ m'
      -- gives g(subNat(m',...)) = g ⟨k.val - m', _⟩
      -- So we need k.val - (m'+1) = k.val - m', which requires m'+1 = m'. Contradiction!
      -- Actually this means the contradiction case should fire. Let me check h_sa.
      -- h_sa says castSucc(cast k) < castAdd i, i.e., k.val < i.val.
      -- h_lhs says ¬(castSucc(cast k).val < m'+1), i.e., k.val ≥ m'+1.
      -- But i.val < m'+1 (since i : Fin(m'+1)), so k.val < i.val < m'+1.
      -- Contradiction with k.val ≥ m'+1!
      exfalso; simp_all [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, hvkc, hvp]; omega
  · -- succAbove gave succ: result has val = kc.val + 1 = k.val + 1
    have hvsa : (p.succAbove kc).val = k.val + 1 := by
      simp [Fin.succAbove, h_sa, Fin.val_succ, hvkc]
    simp only [Fin.addCases, Function.comp]
    split <;> rename_i h_lhs <;> split <;> rename_i h_rhs
    · congr 1; ext
      simp only [Fin.val_castLT, hvsa, Fin.succAbove, Fin.val_castSucc, Fin.val_succ]
      split <;> rename_i h_inner <;>
        simp_all [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, hvkc] <;> omega
    · -- succ, both right: need ▸ g (subNat (m'+1) ...) = ▸ g (subNat m' ...)
      -- The ▸ casts are Eq.mpr from addCases. Both sides give g at val = k.val - m'.
      -- Since the ▸ casts only change the Fin bound proof, the values match.
      -- h_lhs: k.val + 1 < m' + 1, h_rhs: k.val ≥ m' → k.val + 1 ≤ m', contradiction
      exfalso; simp [Fin.val_succ, hvkc] at h_lhs; omega
    · -- succ, LHS right, RHS left: k.val+1 ≥ m'+1 but k.val < m', contradiction
      exfalso; simp [Fin.val_succ, hvkc] at h_lhs; omega
    · -- succ, both right: eliminate ▸ casts, then match g arguments by Fin.ext
      simp only [eqRec_eq_cast, cast_eq]
      congr 1; apply Fin.ext
      dsimp only [Fin.subNat, Fin.cast, Fin.succ]
      omega

/-- Deleting an element from the right block of `addCases I J` (at position `natAdd`):
`(addCases I J) ∘ succAbove (natAdd (m+1) j) = addCases I (J ∘ succAbove j)`. -/
theorem addCases_succAbove_natAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (j : Fin (n' + 1))
    (k : Fin (m' + 1 + n')) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.natAdd (m' + 1) j).succAbove k) =
    (Fin.addCases f (g ∘ j.succAbove) : Fin ((m' + 1) + n') → α) k := by
  set q := (Fin.natAdd (m' + 1) j) with hq_def
  have hvq : q.val = m' + 1 + j.val := Fin.val_natAdd _ _
  have hjv := j.isLt
  have hkv := k.isLt
  simp only [Fin.addCases, Fin.succAbove, Function.comp]
  -- Case split on succAbove (castSucc vs succ) and on k's block (left vs right)
  by_cases hk : k.val < m' + 1
  · -- k in left block on RHS: RHS = f (k.castLT ...)
    simp only [dif_pos hk]
    -- LHS: addCases f g at succAbove(natAdd j, k), and succAbove result has val < m'+1
    -- so LHS also gives f(...)
    split <;> rename_i h_sa
    · -- castSucc: val = k.val < m'+1
      simp only [dif_pos (show k.castSucc.val < m' + 1 by simp [Fin.val_castSucc]; omega)]
      congr 1
    · -- succ: val = k.val + 1. h_sa: ¬castSucc k < natAdd j, so k.val ≥ m'+1+j.val.
      -- But hk: k.val < m'+1. Since j.val ≥ 0, m'+1+j.val ≥ m'+1 > k.val. Contradiction.
      exfalso; simp [Fin.lt_def, Fin.val_castSucc] at h_sa; omega
  · -- k in right block on RHS: RHS = ▸ g (succAbove j (subNat ...))
    simp only [dif_neg hk]
    split <;> rename_i h_sa
    · -- castSucc: val = k.val ≥ m'+1, so LHS also right block
      simp only [dif_neg (show ¬ k.castSucc.val < m' + 1 by simp [Fin.val_castSucc]; omega)]
      -- Both sides apply g to Fin(n'+1) values with matching vals.
      -- The ▸ casts are along α = α, i.e., trivial. Eliminate with eqRec_eq_cast + cast_eq.
      simp only [eqRec_eq_cast, cast_eq]
      congr 1; apply Fin.ext
      simp only [Fin.subNat, Fin.val_castSucc, Fin.val_mk, Fin.succAbove]
      split <;> simp_all [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega
    · simp only [dif_neg (show ¬ k.succ.val < m' + 1 by simp [Fin.val_succ]; omega)]
      simp only [eqRec_eq_cast, cast_eq]
      congr 1; apply Fin.ext
      simp only [Fin.subNat, Fin.val_succ, Fin.val_mk, Fin.succAbove]
      split <;> simp_all [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- Substituting a `ℕ` equality lets us compare determinants of matrices indexed by `Fin a`
and `Fin b` once their pointwise values agree under the cast. -/
lemma det_subst_eq {R : Type*} [CommRing R] {a b : ℕ} (h : a = b)
    (f : Fin a → Fin a → R) (g : Fin b → Fin b → R)
    (hfg : ∀ i j, f (Fin.cast h.symm i) (Fin.cast h.symm j) = g i j) :
    Matrix.det f = Matrix.det g := by
  subst h; exact congr_arg _ (funext fun i => funext fun j => hfg i j)

end Fin
