import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Auxiliary.Perm

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

end ContinuousAlternatingMap

end
