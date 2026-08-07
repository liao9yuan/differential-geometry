import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Auxiliary.Perm
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

noncomputable section

open ContinuousAlternatingMap

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

def flipAddCongr (m n : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  Equiv.trans ((finSumFinEquiv (m := n) (n := m)).symm : Fin (n + m) ≃ Fin n ⊕ Fin m)
    (Equiv.trans (Fin.finSumCongr.symm : Fin n ⊕ Fin m ≃ Fin m ⊕ Fin n)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)))

private lemma flipAddCongr_finSumFinEquiv (m n : ℕ) (x : Fin n ⊕ Fin m) :
    flipAddCongr m n (finSumFinEquiv (m := n) (n := m) x) =
      finSumFinEquiv (Fin.finSumCongr x) := by
  cases x with
  | inl i => simp [flipAddCongr, Fin.finSumCongr]
  | inr i => simp [flipAddCongr, Fin.finSumCongr]

private lemma sumCongrPerm_inl (σ : Equiv.Perm (Fin m ⊕ Fin n)) (i : Fin n) :
    Equiv.Perm.sumCongrPerm σ (Sum.inl i) = Fin.finSumCongr (σ (Sum.inr i)) := by
  simp [Equiv.Perm.sumCongrPerm, Equiv.permCongr, Fin.finSumCongr]

private lemma sumCongrPerm_inr (σ : Equiv.Perm (Fin m ⊕ Fin n)) (i : Fin m) :
    Equiv.Perm.sumCongrPerm σ (Sum.inr i) = Fin.finSumCongr (σ (Sum.inl i)) := by
  simp [Equiv.Perm.sumCongrPerm, Equiv.permCongr, Fin.finSumCongr]

private lemma uncurrySum_summand_flip (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (n + m) → M)
    (σ : Equiv.Perm (Fin n ⊕ Fin m)) :
    uncurrySum.summand (f.flip.compContinuousAlternatingMap₂ h g) (Quotient.mk'' σ)
        (v ∘ finSumFinEquiv) =
      uncurrySum.summand (f.compContinuousAlternatingMap₂ g h)
        (Quotient.mk'' (Equiv.Perm.sumCongrPerm (m := n) (n := m) σ))
        ((v ∘ flipAddCongr n m) ∘ finSumFinEquiv) := by
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [Equiv.Perm.sign_sumCongrPerm]
  congr 2
  · apply congrArg f
    apply congrArg g
    funext i
    simp [sumCongrPerm_inl, flipAddCongr_finSumFinEquiv, Fin.finSumCongr, Sum.swap_swap]
  · apply congrArg h
    funext i
    simp [sumCongrPerm_inr, flipAddCongr_finSumFinEquiv, Fin.finSumCongr, Sum.swap_swap]

private lemma uncurrySum_summand_flip' (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (n + m) → M)
    (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) :
    uncurrySum.summand (f.flip.compContinuousAlternatingMap₂ h g) σ (v ∘ finSumFinEquiv) =
      uncurrySum.summand (f.compContinuousAlternatingMap₂ g h)
        (Equiv.Perm.finAddCongr_equiv (m := n) (n := m) σ)
        ((v ∘ flipAddCongr n m) ∘ finSumFinEquiv) := by
  refine Quotient.inductionOn' σ ?_
  intro σ'
  simpa using uncurrySum_summand_flip h g f v σ'

private def derivFinCast (m n : ℕ) : Fin (m + n + 1) ≃ Fin (n + m + 1) :=
  finCongr (by omega)

omit [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N''] in
private lemma removeNth_cast (m n : ℕ) (v : Fin (m + n + 1) → M) (k : Fin (m + n + 1)) :
    (derivFinCast m n k).removeNth (v ∘ (derivFinCast m n).symm) =
      (k.removeNth v) ∘ (Fin.finAddCongr (m := n) (n := m)) := by
  ext i
  rw [Fin.removeNth_apply, Function.comp_apply, Function.comp_apply, Fin.removeNth_apply]
  apply congrArg v
  apply Fin.ext
  have hk : ((derivFinCast m n k : Fin (n + m + 1)).val) = k.val := by
    simp [derivFinCast, Fin.val_cast]
  have hi : ((Fin.finAddCongr (m := n) (n := m) i : Fin (m + n)).val) = i.val := by
    simp [Fin.finAddCongr, Fin.val_cast]
  by_cases h : i.val < k.val
  · have hc1 : i.castSucc < (derivFinCast m n k : Fin (n + m + 1)) := by
      rw [Fin.lt_def]
      simp [Fin.val_castSucc, hk, h]
    have hc2 : (Fin.finAddCongr (m := n) (n := m) i).castSucc < k := by
      rw [Fin.lt_def]
      simp [Fin.finAddCongr, Fin.val_cast, Fin.val_castSucc, h]
    rw [Fin.succAbove_of_castSucc_lt _ _ hc1]
    rw [Fin.succAbove_of_castSucc_lt _ _ hc2]
    exact hi.symm
  · have hn1 : ¬ i.castSucc < (derivFinCast m n k : Fin (n + m + 1)) := by
      rw [Fin.lt_def]
      simp [Fin.val_castSucc, hk, h]
    have hn2 : ¬ (Fin.finAddCongr (m := n) (n := m) i).castSucc < k := by
      rw [Fin.lt_def]
      simp [Fin.finAddCongr, Fin.val_cast, Fin.val_castSucc, h]
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hn1)]
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hn2)]
    simpa [derivFinCast, Fin.val_cast, Fin.val_succ] using hi.symm

private lemma flipAddCongr_eq_addCasesSwapPerm (m n : ℕ) :
    (flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm =
      (finCongr (show m + n = n + m by omega)).permCongr (Equiv.Perm.addCasesSwapPerm m n) := by
  ext i
  simp only [Equiv.Perm.addCasesSwapPerm]
  cases hs : (finSumFinEquiv (m := n) (n := m)).symm i with
  | inl a =>
      have hi : i = finSumFinEquiv (m := n) (n := m) (Sum.inl a) := by
        rw [← hs]
        simp
      rw [hi]
      simp [flipAddCongr, Fin.finAddCongr, finSumFinEquiv_apply_left,
        finSumFinEquiv_symm_apply_castAdd, Fin.finSumCongr, Equiv.permCongr_def, finCongr,
        Fin.val_cast]
      omega
  | inr a =>
      have hi : i = finSumFinEquiv (m := n) (n := m) (Sum.inr a) := by
        rw [← hs]
        simp
      rw [hi]
      simp [flipAddCongr, Fin.finAddCongr, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_natAdd, Fin.finSumCongr, Equiv.permCongr_def, finCongr,
        Fin.val_cast]

theorem wedge_flip (h : M [⋀^Fin n]→L[𝕜] N') (g : M [⋀^Fin m]→L[𝕜] N)
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    wedge_product h g f.flip = (wedge_product g h f).domDomCongr (flipAddCongr n m) := by
  ext v
  rw [wedge_product_def]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [wedge_product_def]
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_bij
    (fun (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) _ =>
      Equiv.Perm.finAddCongr_equiv (m := n) (n := m) σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    exact Equiv.injective (Equiv.Perm.finAddCongr_equiv (m := n) (n := m)) h
  · intro τ hτ
    exact ⟨(Equiv.Perm.finAddCongr_equiv (m := n) (n := m)).symm τ, by simp,
      Equiv.apply_symm_apply _ τ⟩
  · intro σ hσ
    exact uncurrySum_summand_flip' h g f v σ

private lemma map_perm_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : M [⋀^ι]→L[𝕜] N'') (w : ι → M) (π : Equiv.Perm ι) :
    A (w ∘ π) = Equiv.Perm.sign π • A w := by
  exact A.toAlternatingMap.map_perm w π

private lemma uncurryFin_reindex (P : M →L[𝕜] (M [⋀^Fin (n + m)]→L[𝕜] N''))
    (v : Fin (m + n + 1) → M) :
    (∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
        P (v k) ((derivFinCast m n k).removeNth (v ∘ (derivFinCast m n).symm))) =
      uncurryFin P (v ∘ (derivFinCast m n).symm) := by
  rw [uncurryFin_apply]
  refine Finset.sum_bij (fun k _ => derivFinCast m n k) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro k₁ hk₁ k₂ hk₂ h
    exact (Equiv.injective (derivFinCast m n)) h
  · intro k' hk'
    exact ⟨(derivFinCast m n).symm k', by simp, by simp⟩
  · intro k hk
    have hk' : ((derivFinCast m n k : Fin (n + m + 1)).val) = k.val := by
      simp [derivFinCast, Fin.val_cast]
    simp [hk']

private lemma sign_flipAddCongr_composite (m n : ℕ) :
    Equiv.Perm.sign ((flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm) =
      (-1 : ℤˣ) ^ (m * n) := by
  rw [flipAddCongr_eq_addCasesSwapPerm, Equiv.Perm.sign_permCongr,
    Equiv.Perm.addCasesSwapPerm_sign]
  rfl

private lemma flipAddCongr_composite_eq_addCasesSwapPerm_apply (m n : ℕ) (x : Fin (m + n + 1)) :
    (derivFinCast m n).symm
        (Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)
          (flipAddCongr (n + 1) m
            (Fin.cast (show m + n + 1 = m + (n + 1) by omega) x))) =
      Fin.cast (show (n + 1) + m = m + n + 1 by omega)
        (Equiv.Perm.addCasesSwapPerm (n + 1) m
          (Fin.cast (show m + n + 1 = (n + 1) + m by omega) x)) := by
  apply Fin.ext
  simp only [Fin.val_cast, Equiv.Perm.addCasesSwapPerm]
  by_cases h : x.val < m
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.addCases, Sum.swap_inl]
    omega
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.val_castAdd, Fin.addCases, Sum.swap_inr]

private lemma flipAddCongr_composite_eq_addCasesSwapPerm_apply' (m n : ℕ)
    (x : Fin (m + (n + 1))) :
    (derivFinCast m n).symm (Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)
        (flipAddCongr (n + 1) m x)) =
      Fin.cast (show (n + 1) + m = m + n + 1 by omega)
        (Equiv.Perm.addCasesSwapPerm (n + 1) m
          (Fin.cast (show m + (n + 1) = (n + 1) + m by omega) x)) := by
  apply Fin.ext
  simp only [Fin.val_cast, Equiv.Perm.addCasesSwapPerm]
  by_cases h : x.val < m
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.addCases, Sum.swap_inl]
    omega
  · simp [h, flipAddCongr, finSumFinEquiv, Fin.finSumCongr, Fin.finAddFlipAssoc, derivFinCast,
      Fin.val_cast, Fin.val_castAdd, Fin.addCases, Sum.swap_inr]

private lemma addCasesSwapPerm_cast_sign (m n : ℕ) :
    Equiv.Perm.sign (Equiv.trans
        (Equiv.trans (finCongr (show m + n + 1 = (n + 1) + m by omega))
          (Equiv.Perm.addCasesSwapPerm (n + 1) m))
        (finCongr (show (n + 1) + m = m + n + 1 by omega))) =
      (-1 : ℤˣ) ^ ((n + 1) * m) := by
  let e : Fin (m + n + 1) ≃ Fin ((n + 1) + m) :=
    finCongr (show m + n + 1 = (n + 1) + m by omega)
  have h : Equiv.trans (Equiv.trans e (Equiv.Perm.addCasesSwapPerm (n + 1) m)) e.symm =
      e.symm.permCongr (Equiv.Perm.addCasesSwapPerm (n + 1) m) := by
    rw [Equiv.trans_assoc, Equiv.permCongr_def, Equiv.symm_symm]
    rfl
  change Equiv.Perm.sign (Equiv.trans
      (Equiv.trans e (Equiv.Perm.addCasesSwapPerm (n + 1) m)) e.symm) =
    (-1 : ℤˣ) ^ ((n + 1) * m)
  rw [h, Equiv.Perm.sign_permCongr, Equiv.Perm.addCasesSwapPerm_sign]
  rfl

private lemma units_neg_pow_smul (k₁ k₂ : ℕ) (x : N'') :
    ((-1 : ℤˣ) ^ k₁) • (((-1 : ℤˣ) ^ k₂) • x) = ((-1 : 𝕜) ^ (k₁ + k₂)) • x := by
  rw [smul_smul, ← neg_one_pow_add, Units.smul_def]
  rw [← Int.cast_smul_eq_zsmul (R := 𝕜)]
  rcases Nat.even_or_odd (k₁ + k₂) with h | h
  · have hz : ((-1 : ℤˣ) ^ (k₁ + k₂)) = 1 := h.neg_one_pow
    have hz𝕜 : (-1 : 𝕜) ^ (k₁ + k₂) = 1 := h.neg_one_pow
    simp [hz, hz𝕜]
  · have hz : ((-1 : ℤˣ) ^ (k₁ + k₂)) = -1 := h.neg_one_pow
    have hz𝕜 : (-1 : 𝕜) ^ (k₁ + k₂) = -1 := h.neg_one_pow
    simp [hz, hz𝕜]

theorem uncurryFin_precompR_eq (f : N →L[𝕜] N' →L[𝕜] N'')
    (a : M [⋀^Fin m]→L[𝕜] N) (L : M →L[𝕜] (M [⋀^Fin n]→L[𝕜] N')) :
    uncurryFin ((wedge_productL f).precompR M a L) =
      (-1 : 𝕜) ^ m • wedge_product a (uncurryFin L) f := by
  ext v
  let C : Fin (m + n + 1) ≃ Fin (n + m + 1) := derivFinCast m n
  let P : M →L[𝕜] (M [⋀^Fin (n + m)]→L[𝕜] N'') :=
    (wedge_productL f.flip).precompL M L a
  let π : Equiv.Perm (Fin (n + m)) :=
    (flipAddCongr m n).trans (Fin.finAddCongr (m := n) (n := m)).symm
  have hπ : Equiv.Perm.sign π = (-1 : ℤˣ) ^ (m * n) := sign_flipAddCongr_composite m n
  have hflip (k : Fin (m + n + 1)) :
      wedge_product a (L (v k)) f =
        (wedge_product (L (v k)) a f.flip).domDomCongr (flipAddCongr m n) := by
    exact wedge_flip (m := n) (n := m) (h := a) (g := L (v k)) (f := f.flip)
  have hbridge (k : Fin (m + n + 1)) :
      (k.removeNth v) ∘ (flipAddCongr m n) =
        ((C k).removeNth (v ∘ C.symm)) ∘ π := by
    rw [removeNth_cast m n v k]
    apply congrArg ((k.removeNth v) ∘ ·)
    ext x
    simp [π, flipAddCongr, Fin.finAddCongr, finCongr]
  calc
    uncurryFin ((wedge_productL f).precompR M a L) v
        = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedge_product a (L (v k)) f (k.removeNth v) := by
          rw [uncurryFin_apply]
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
            ContinuousLinearMap.comp_apply, wedge_productL_apply]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            (wedge_product (L (v k)) a f.flip).domDomCongr (flipAddCongr m n) (k.removeNth v) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hflip k]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedge_product (L (v k)) a f.flip ((k.removeNth v) ∘ (flipAddCongr m n)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedge_product (L (v k)) a f.flip (((C k).removeNth (v ∘ C.symm)) ∘ π) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hbridge k]
    _ = Equiv.Perm.sign π • ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedge_product (L (v k)) a f.flip ((C k).removeNth (v ∘ C.symm)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [smul_comm]
          congr 1
          exact map_perm_sign (wedge_product (L (v k)) a f.flip)
            ((C k).removeNth (v ∘ C.symm)) π
    _ = Equiv.Perm.sign π • uncurryFin P (v ∘ C.symm) := by
          congr 1
          simpa [P] using uncurryFin_reindex P v
    _ = Equiv.Perm.sign π •
          (domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin L) a f.flip)) (v ∘ C.symm) := by
          congr 1
          change (uncurryFin P) (v ∘ C.symm) =
            (domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin L) a f.flip)) (v ∘ C.symm)
          simpa [P] using DFunLike.congr_fun
            (uncurryFin_wedge_productL_precompL_eq_domDomCongr f.flip L a) (v ∘ C.symm)
    _ = Equiv.Perm.sign π •
          wedge_product (uncurryFin L) a f.flip ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc) := by
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = Equiv.Perm.sign π •
          (wedge_product a (uncurryFin L) f).domDomCongr (flipAddCongr (n + 1) m)
            ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc) := by
          congr 1
          simpa using DFunLike.congr_fun
            (wedge_flip (m := m) (n := n + 1) (h := uncurryFin L) (g := a) (f := f))
            ((v ∘ C.symm) ∘ Fin.finAddFlipAssoc (m := n) (p := 1) (n := m))
    _ = Equiv.Perm.sign π •
          wedge_product a (uncurryFin L) f
            (((v ∘ C.symm) ∘ Fin.finAddFlipAssoc (m := n) (p := 1) (n := m)) ∘
              (flipAddCongr (n + 1) m)) := by
          rw [ContinuousAlternatingMap.domDomCongr_apply]
    _ = Equiv.Perm.sign π •
          wedge_product a (uncurryFin L) f
            (v ∘ (((finCongr (show m + n + 1 = (n + 1) + m by omega)).trans
              (Equiv.Perm.addCasesSwapPerm (n + 1) m)).trans
              (finCongr (show (n + 1) + m = m + n + 1 by omega)))) := by
          congr 1
          congr 1
          funext i
          rw [Function.comp_apply, Function.comp_apply, Function.comp_apply]
          exact congrArg v (flipAddCongr_composite_eq_addCasesSwapPerm_apply' m n i)
    _ = (-1 : 𝕜) ^ m • wedge_product a (uncurryFin L) f v := by
          rw [map_perm_sign (wedge_product a (uncurryFin L) f) v
            (((finCongr (show m + n + 1 = (n + 1) + m by omega)).trans
              (Equiv.Perm.addCasesSwapPerm (n + 1) m)).trans
              (finCongr (show (n + 1) + m = m + n + 1 by omega)))]
          rw [hπ, addCasesSwapPerm_cast_sign]
          have hsum : m * n + (n + 1) * m = 2 * (m * n) + m := by nlinarith
          rw [show ((-1 : ℤˣ) ^ (m * n)) • (((-1 : ℤˣ) ^ ((n + 1) * m)) •
              (wedge_product a (uncurryFin L) f v)) = ((-1 : 𝕜) ^ m) •
              (wedge_product a (uncurryFin L) f v) from by
            rw [units_neg_pow_smul (𝕜 := 𝕜) (m * n) ((n + 1) * m)]
            rw [hsum, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]]

end ContinuousAlternatingMap

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n k l : ℕ} {x : E}

theorem extDeriv_eq_uncurryFin (ω : E → E [⋀^Fin n]→L[ℝ] F)
    (hω : DifferentiableAt ℝ ω x) :
    extDeriv ω x = ContinuousAlternatingMap.uncurryFin (fderiv ℝ ω x) := by
  ext v
  rw [extDeriv_apply hω, ContinuousAlternatingMap.uncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  congr 1
  let Eval : (E [⋀^Fin n]→L[ℝ] F) →L[ℝ] F :=
    { toFun := fun L => L (i.removeNth v)
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hEval : fderiv ℝ (fun L : E [⋀^Fin n]→L[ℝ] F => L (i.removeNth v)) (ω x) = Eval := by
    simpa [Eval] using (Eval.fderiv : fderiv ℝ (⇑Eval) (ω x) = Eval)
  have hcomp : HasFDerivAt (fun y : E => (ω y) (i.removeNth v))
      (Eval.comp (fderiv ℝ ω x)) x := by
    have hg : HasFDerivAt (fun L : E [⋀^Fin n]→L[ℝ] F => L (i.removeNth v)) Eval (ω x) := by
      simpa [Eval] using Eval.hasFDerivAt
    exact HasFDerivAt.comp x hg hω.hasFDerivAt
  have hmain : fderiv ℝ (fun y : E => (ω y) (i.removeNth v)) x = Eval.comp (fderiv ℝ ω x) := by
    simpa using hcomp.fderiv
  rw [hmain]
  rfl

theorem fderiv_wedge_apply (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (b : E → E [⋀^Fin l]→L[ℝ] ℝ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    fderiv ℝ (fun y : E => a y ∧[ℝ] b y) x =
      (wedge_productL (ContinuousLinearMap.mul ℝ ℝ)).precompR E (a x) (fderiv ℝ b x) +
        (wedge_productL (ContinuousLinearMap.mul ℝ ℝ)).precompL E (fderiv ℝ a x) (b x) := by
  let W : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) := wedge_productL (ContinuousLinearMap.mul ℝ ℝ)
  have hf : HasFDerivAt (fun y : E => (W (a y)) (b y))
      ((W (a x)).comp (fderiv ℝ b x) + (W.comp (fderiv ℝ a x)).flip (b x)) x := by
    have hc : HasFDerivAt (fun y : E => W (a y)) (W.comp (fderiv ℝ a x)) x := by
      simpa using (hasFDerivAt_const (x := x) (c := W)).clm_apply ha.hasFDerivAt
    simpa using hc.clm_apply hb.hasFDerivAt
  have hfderiv : fderiv ℝ (fun y : E => a y ∧[ℝ] b y) x =
      (W (a x)).comp (fderiv ℝ b x) + (W.comp (fderiv ℝ a x)).flip (b x) := by
    simpa [W, ContinuousLinearMap.mul_apply'] using hf.fderiv
  rw [hfderiv]
  ext h
  simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precompL_apply, W,
    ContinuousLinearMap.flip_apply]

theorem extDeriv_wedge (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (b : E → E [⋀^Fin l]→L[ℝ] ℝ)
    (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b) :
    extDeriv (fun x => a x ∧[ℝ] b x) =
      fun x => domDomCongr Fin.finAddFlipAssoc ((extDeriv a x) ∧[ℝ] (b x)) +
        (-1 : ℝ) ^ k • (a x ∧[ℝ] (extDeriv b x)) := by
  funext x
  let W : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin (k + l)]→L[ℝ] ℝ) := wedge_productL (ContinuousLinearMap.mul ℝ ℝ)
  have hda : DifferentiableAt ℝ a x := (ha.differentiable (by simp)).differentiableAt
  have hdb : DifferentiableAt ℝ b x := (hb.differentiable (by simp)).differentiableAt
  have hdab : DifferentiableAt ℝ (fun y : E => a y ∧[ℝ] b y) x := by
    exact ((W.contDiff.comp ha).clm_apply hb).differentiable (by simp) |>.differentiableAt
  rw [extDeriv_eq_uncurryFin (fun y : E => a y ∧[ℝ] b y) hdab]
  rw [fderiv_wedge_apply a b hda hdb]
  rw [ContinuousAlternatingMap.uncurryFin_add]
  rw [ContinuousAlternatingMap.uncurryFin_precompR_eq]
  rw [ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr]
  rw [← extDeriv_eq_uncurryFin a hda, ← extDeriv_eq_uncurryFin b hdb]
  exact add_comm _ _

end DifferentialForm

end
