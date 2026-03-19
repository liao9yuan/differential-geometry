/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Aux.Perm
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Alternating.Basis

/-
# Wedge Products
-/

noncomputable section

namespace ContinuousAlternatingMap

section wedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {M'' : Type*} [NormedAddCommGroup M''] [NormedSpace 𝕜 M'']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n p : ℕ}

/-- The wedge product of two continuous alternating maps `g` an `h` with respect to a
bilinear map `f`. -/
def wedge_product (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

-- TODO: change notation
notation g "∧["f"]" h => wedge_product g h f
notation g "∧["𝕜"]" h => wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M} :
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

open scoped TensorProduct

/-- The wedge product satisfies `m! * n! • (g ∧ h) v = Alt(g ⊗_f h) v`, proved via
`domCoprod_alternization_eq` from Mathlib. -/
theorem factorial_nsmul_wedge_product_eq_alternatization
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (m.factorial * n.factorial) • (g ∧[f] h) v =
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  -- Factor tensorProductMap.toMM through domCoprod + TensorProduct.lift
  let φ : N ⊗[𝕜] N' →ₗ[𝕜] N'' := TensorProduct.lift
    { toFun := fun n => (f n).toLinearMap
      map_add' := by intro x y; ext; simp [map_add]
      map_smul' := by intro c x; ext; simp [map_smul] }
  have hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b := fun _ _ => rfl
  have h_factor : (tensorProductMap g h f).toMultilinearMap =
      (φ.compMultilinearMap (MultilinearMap.domCoprod
        ↑g.toAlternatingMap ↑h.toAlternatingMap)).domDomCongr finSumFinEquiv := by
    ext x; simp [tensorProductMap, MultilinearMap.domDomCongr_apply,
      LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply, hφ]; rfl
  rw [h_factor, ContinuousAlternatingMap.alternatization_domDomCongr,
    LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternization_eq, Fintype.card_fin, Fintype.card_fin]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.smul_apply, map_nsmul]
  change _ = _ • φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv))
  rw [show φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv)) =
    (uncurrySum (f.compContinuousAlternatingMap₂ g h)) (v ∘ ⇑finSumFinEquiv) from
    congr_fun (congr_arg DFunLike.coe
      (lift_comp_domCoprod_eq_uncurrySum g h f φ hφ)) _]; rfl

/-- The wedge product agrees with the standard definition:
`g ∧ h = 1/(m! * n!) • Alt(g ⊗_f h)` where `Alt` is `MultilinearMap.alternatization`. -/
theorem wedge_product_eq_alternatization [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (g ∧[f] h) v = ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  have h_ne : (↑(m.factorial * n.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n)).ne'
  have h_eq := factorial_nsmul_wedge_product_eq_alternatization g h f v
  rw [← h_eq, ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ h_ne]

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x =
    uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] N}
    {x : Fin (m + n) → M} :
      (g ∧[ContinuousLinearMap.lsmul 𝕜 𝕜] h) x =
      uncurryFinAdd ((ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- Associativity of multiplication wedge product -/
theorem wedge_mul_assoc (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (v : Fin (m + n + p) → M) :
      ContinuousAlternatingMap.domDomCongr
        Fin.finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) v = ((g ∧[𝕜] h) ∧[𝕜] l) v := by
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply,
    domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, wedge_product_def,
    uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  rw[wedge_product, wedge_product]
  rw[uncurryFinAdd, uncurryFinAdd]
  sorry

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[← smul_add, add_apply, map_add, ContinuousLinearMap.add_apply, smul_add]

/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N)
    (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[add_apply, map_add, smul_add]

theorem smul_wedge (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = (c • g) ∧[𝕜] h := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply', ← smul_assoc, smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply',
    smul_apply, smul_eq_mul]

theorem wedge_smul (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) (c : 𝕜) :
    c • (g ∧[𝕜] h) = g ∧[𝕜] (c • h) := by
  ext x
  rw[smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  rw[wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply',
    ← smul_assoc, smul_comm]
  rw[smul_assoc, smul_eq_mul, ← mul_assoc]
  rw[uncurrySum.summand_mk]
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply',
    smul_apply, smul_eq_mul, ← mul_assoc, mul_comm]

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr Fin.finAddCongr := by
  ext x
  rw[domDomCongr_apply, smul_apply, wedge_product_mul, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply, wedge_product_mul,
    uncurryFinAdd, domDomCongr_apply, uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  conv_rhs => rw[← Equiv.sum_comp Equiv.Perm.finAddCongr_equiv]
  rw[Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  simp only [Function.comp_apply, Equiv.Perm.finAddCongr_equiv_apply]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  simp only [Equiv.Perm.sign_sumCommPerm, Equiv.Perm.sumCommPerm_apply_apply, Function.comp_apply]
  simp [Function.comp_def, finAddFlip]
  simp_rw[mul_comm]
  simp only [Equiv.Perm.sumCongrPerm, Fin.finSumCongr, Equiv.permCongr_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.trans_apply, Equiv.apply_symm_apply,
    Fin.finAddCongr_finAddCongr]
  sorry

/-- The graded Leibniz rule for the interior product (curryFin) and wedge product:
  ι_x(g ∧_f h) = (ι_x g) ∧_f h + (-1)^m • g ∧_f (ι_x h)
  where `finAddFlipAssoc` handles the index rearrangement needed to make
  the result well-typed. -/
theorem iprod_wedge_product
    (g : M [⋀^Fin (m+1)]→L[𝕜] N) (h : M [⋀^Fin (n+1)]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (x : M) :
    curryFin (domDomCongr Fin.finAddFlipAssoc (g ∧[f] h)) x =
      (curryFin g x ∧[f] h) +
      (-1 : 𝕜) ^ m • domDomCongr Fin.finAddFlipAssoc (g ∧[f] curryFin h x) := by
  sorry

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

open Fin

-- UNUSED functionality
lemma domDomCongr_finAddFlip_wedge_self (g : M [⋀^Fin m]→L[ℝ] ℝ) :
    domDomCongr finAddFlip (g∧[ℝ]g) = (g∧[ℝ]g) := by
  ext x
  rw[wedge_product_mul, uncurryFinAdd, domDomCongr_apply, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, wedge_product_mul, uncurryFinAdd, domDomCongr_apply,
    uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
  conv_rhs => rw[← Equiv.sum_comp Equiv.Perm.finAddFlip_equiv_eqFin]
  apply Finset.sum_congr rfl
  rintro σ -
  rcases σ with ⟨σ₁⟩
  simp only [Function.comp_apply, Equiv.Perm.finAddFlip_equiv_eqFin_apply]
  rw[uncurrySum.summand_mk]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply']
  simp [Function.comp_def, finAddFlip, mul_comm]

/- Corollary of `wedge_antisymm` saying that a wedge of g with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (g ∧[ℝ] g) = 0 := by
  let h := wedge_antisymm g g
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd)] at h
  suffices (g ∧[ℝ] g) = -(g ∧[ℝ] g) by
    rw[← sub_eq_zero, sub_neg_eq_add, DFunLike.ext_iff] at this
    ext x
    simpa using this x
  simp only [finAddCongr, finCongr_refl, neg_smul, one_smul, domDomCongr_refl] at h
  exact h

end wedge

section elementaryCovectorWedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d m' p : ℕ}

/-- The wedge product of two elementary covectors is the elementary
covector of the concatenated multi-index. This is the Cauchy–Binet
identity: the determinant of a matrix whose rows come from two
blocks equals the shuffle-sum of products of sub-determinants.

Given `g = elementaryCovector b I` and `h = elementaryCovector b J`,
`g ∧[𝕜] h = elementaryCovector b (Fin.addCases I J)`. -/
theorem elementaryCovector_wedge
    (b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜))
    (I : Fin m' → Fin d) (J : Fin p → Fin d) :
    ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) =
      (elementaryCovector b (Fin.addCases I J) :
        E [⋀^Fin (m' + p)]→L[𝕜] 𝕜) := by
  sorry

end elementaryCovectorWedge

end ContinuousAlternatingMap
