





import DifferentialGeometry.Tensor.Auxiliary.Perm
import DifferentialGeometry.Tensor.Auxiliary.MultiKroneckerDelta
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import DifferentialGeometry.Tensor.Alternating.Congr
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Alternating.Basis
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Derivative


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
  {m n p m' d : ℕ}

def wedge_product (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

notation g "∧["f"]" h => wedge_product g h f
notation g "∧["𝕜"]" h => wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)

noncomputable def covectorWedge (α : M →L[𝕜] 𝕜) (β : M [⋀^Fin n]→L[𝕜] 𝕜) :
    M [⋀^Fin (n + 1)]→L[𝕜] 𝕜 :=
  uncurryFin (α.smulRight β)

notation:70 α " ∧₁ " β => covectorWedge α β

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M} :
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

open scoped TensorProduct

theorem factorial_nsmul_wedge_product_eq_alternatization
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (m.factorial * n.factorial) • (g ∧[f] h) v =
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
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

theorem wedge_product_eq_alternatization [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (g ∧[f] h) v = ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  have h_ne : (↑(m.factorial * n.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n)).ne'
  have h_eq := factorial_nsmul_wedge_product_eq_alternatization g h f v
  rw [← h_eq, ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ h_ne]

theorem elementaryCovector_wedge [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin m' → Fin d) (J : Fin p → Fin d) :
    ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) =
      (elementaryCovector b (Fin.addCases I J) :
        M [⋀^Fin (m' + p)]→L[𝕜] 𝕜) := by
  obtain ⟨B, dual⟩ := exists_predual_basis b
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply B.ext_alternating
  intro v hv
  change ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) (B ∘ v) =
    elementaryCovector b (Fin.addCases I J) (B ∘ v)
  rw [elementaryCovector_basis_eval B b dual (Fin.addCases I J) v]
  have lhs_eq := wedge_product_eq_alternatization (elementaryCovector b I)
    (elementaryCovector b J) (ContinuousLinearMap.mul 𝕜 𝕜) (⇑B ∘ v)
  rw [lhs_eq, MultilinearMap.alternatization_apply]
  simp_rw [MultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.coe_coe,
    tensorProductMap_apply, ContinuousLinearMap.mul_apply']
  simp_rw [show ∀ (σ : Equiv.Perm (Fin (m' + p))),
    (fun i => (⇑B ∘ v) (σ i)) ∘ Fin.castAdd p = ⇑B ∘ (v ∘ σ ∘ Fin.castAdd p) from fun _ => rfl,
    show ∀ (σ : Equiv.Perm (Fin (m' + p))),
    (fun i => (⇑B ∘ v) (σ i)) ∘ Fin.natAdd m' = ⇑B ∘ (v ∘ σ ∘ Fin.natAdd m') from fun _ => rfl,
    elementaryCovector_basis_eval B b dual]
  exact Fin.multiKroneckerDelta_cauchyBinet I J v

theorem uncurryFin_smulRight_elementaryCovector
    (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (a : Fin d) (I : Fin m → Fin d) :
    uncurryFin ((b a).smulRight (elementaryCovector b I)) =
      (elementaryCovector b (Fin.cons a I) :
        M [⋀^Fin (m + 1)]→L[𝕜] 𝕜) := by
  ext v
  rw [uncurryFin_apply, elementaryCovector_apply, Matrix.det_succ_row_zero]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro j _
  let J : Fin (m + 1) → Fin d := Fin.cons a I
  have hdet : (elementaryCovector b I) (j.removeNth v) =
      (Matrix.submatrix (fun r c : Fin (m + 1) => (b (J r)) (v c))
        Fin.succ j.succAbove).det := by
    rw [elementaryCovector_apply]
    rfl
  rw [hdet]
  simp [J, zsmul_eq_mul, mul_assoc]

theorem formValuedLinearMap_eq_sum_smulRight_elementaryCovector
    [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜]
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] 𝕜)) :
    let d := Module.finrank 𝕜 M
    let B : Module.Basis (Fin d) 𝕜 M := Module.finBasis 𝕜 M
    let b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜) := B.cDualBasis
    let bm := elementaryCovectorBasis (k := m) B
    g' = ∑ I : Fin m ↪o Fin d,
      (((bm.coord I).comp g'.toLinearMap).toContinuousLinearMap).smulRight
        (elementaryCovector b (I : Fin m → Fin d)) := by
  dsimp
  ext x v
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  rw [ContinuousAlternatingMap.sum_apply]
  have hsum : g' x = ∑ I : Fin m ↪o Fin (Module.finrank 𝕜 M),
      (elementaryCovectorBasis (k := m) (Module.finBasis 𝕜 M)).repr (g' x) I •
        (elementaryCovectorBasis (k := m) (Module.finBasis 𝕜 M)) I :=
    ((elementaryCovectorBasis (k := m) (Module.finBasis 𝕜 M)).sum_repr (g' x)).symm
  rw [hsum]
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply]
  apply Finset.sum_congr rfl
  intro I _
  rw [elementaryCovectorBasis_apply]
  rfl

theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x =
    uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

theorem wedge_product_lsmul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] N}
    {x : Fin (m + n) → M} :
      (g ∧[ContinuousLinearMap.lsmul 𝕜 𝕜] h) x =
      uncurryFinAdd ((ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

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

theorem smul_wedge (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((c • g) ∧[f] h) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw [uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, f.map_smul, ContinuousLinearMap.smul_apply, smul_comm]

theorem wedge_smul (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (c • h)) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw [uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, ContinuousLinearMap.map_smul, smul_comm]

theorem norm_wedge_product_le (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ‖g ∧[f] h‖ ≤
      Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) v‖ ≤ _
  rw [uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
      ContinuousMultilinearMap.sum_apply]
  have key : ∀ q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
          (v ∘ ⇑finSumFinEquiv)‖ ≤ (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := by
    intro q
    induction q using Quotient.inductionOn' with | h σ =>
    rw [uncurrySum_summand_eval]
    have hsign : ∀ z : N'', ‖(Equiv.Perm.sign σ : ℤˣ) • z‖ = ‖z‖ := fun z => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [hsign]
    change ‖f (g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))))
            (h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))))‖ ≤ _
    calc ‖f (g _) (h _)‖
        ≤ ‖f‖ * ‖g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i)))‖ *
            ‖h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i)))‖ := f.le_opNorm₂ _ _
      _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
            (‖h‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by
          gcongr
          · exact g.le_opNorm _
          · exact h.le_opNorm _
      _ = ‖f‖ * ‖g‖ * ‖h‖ *
            ((∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
              ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by ring
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖ := by
          rw [← Fintype.prod_sum_type (fun k => ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) k‖ := by
          rw [Equiv.prod_comp σ (fun k => ‖(v ∘ ⇑finSumFinEquiv) k‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖v i‖ := by
          simp only [Function.comp_apply]
          rw [Equiv.prod_comp finSumFinEquiv (fun i => ‖v i‖)]
  calc ‖∑ q, uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖
      ≤ ∑ q, ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := Finset.sum_le_sum fun q _ => key q
    _ = (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) *
          ((‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) *
          ∏ i, ‖v i‖ := by ring

noncomputable def wedge_productL (f : N →L[𝕜] N' →L[𝕜] N'') :
    (M [⋀^Fin m]→L[𝕜] N) →L[𝕜] (M [⋀^Fin n]→L[𝕜] N') →L[𝕜]
        (M [⋀^Fin (m + n)]→L[𝕜] N'') :=
  LinearMap.mkContinuous₂
    { toFun := fun g =>
        { toFun := fun h => wedge_product g h f
          map_add' := fun h₁ h₂ => wedge_add g h₁ h₂ f
          map_smul' := fun c h => wedge_smul c g h f }
      map_add' := fun g₁ g₂ => by ext h : 1; exact add_wedge g₁ g₂ h f
      map_smul' := fun c g => by ext h : 1; exact smul_wedge c g h f }
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * ‖f‖ + 1) fun g h => by
      change ‖wedge_product g h f‖ ≤ _
      have hwedge := norm_wedge_product_le g h f
      nlinarith [hwedge, norm_nonneg g, norm_nonneg h, norm_nonneg f]

@[simp] theorem wedge_productL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') :
    wedge_productL f g h = wedge_product g h f := rfl

theorem uncurryFin_wedge_productL_precompL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    uncurryFin ((wedge_productL f).precompL M g' h) v =
      ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
        wedge_product (g' (v k)) h f (k.removeNth v) := by
  rw [uncurryFin_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.precompL_apply, wedge_productL_apply]

theorem wedge_product_uncurryFin_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin g') h f) v =
      (wedge_product (uncurryFin g') h f) (v ∘ ⇑Fin.finAddFlipAssoc) := by
  rw [ContinuousAlternatingMap.domDomCongr_apply]

private def uncurryFinLeftExpandedSummand
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (j : Fin (m + 1)) : N'' :=
  Equiv.Perm.sign τ •
    f (((-1 : ℤ) ^ j.val) •
        g' (w (τ (Sum.inl j)))
          (j.removeNth fun i : Fin (m + 1) => w (τ (Sum.inl i))))
      (h fun i : Fin n => w (τ (Sum.inr i)))

private theorem uncurrySum_summand_uncurryFin_left_expand_mk
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h)
        (Quotient.mk'' τ) w =
      ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ j := by
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [uncurryFin_apply]
  let L : N →L[𝕜] N'' :=
    (ContinuousLinearMap.apply 𝕜 N'' (h fun i : Fin n => w (τ (Sum.inr i)))).comp f
  change Equiv.Perm.sign τ •
      L (∑ k : Fin (m + 1),
        (-1 : ℤ) ^ k.val •
          g' (w (τ (Sum.inl k))) (k.removeNth fun i : Fin (m + 1) => w (τ (Sum.inl i)))) =
    ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ j
  rw [_root_.map_sum L]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [L, uncurryFinLeftExpandedSummand]

private theorem derivShuffleLeft_expanded_summand_eq
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M)
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    ((-1 : ℤ) ^ k.val) •
      (uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h)
        (Quotient.mk'' σ) ((k.removeNth v) ∘ ⇑finSumFinEquiv)) =
      uncurryFinLeftExpandedSummand f g' h
        ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
        (derivShuffleLeftFwdRanked k σ) (derivShuffleRank k σ) := by
  rw [uncurrySum_summand_eval]
  unfold uncurryFinLeftExpandedSummand
  rw [derivShuffleLeftFwdRanked_sign]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [derivShuffleLeftFwdRanked_inl_j]
  simp only [Function.comp_apply]
  have hleft :
      (fun i : Fin m =>
          ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
            (derivShuffleLeftFwdRanked k σ (Sum.inl ((derivShuffleRank k σ).succAbove i)))) =
        fun i : Fin m => ((k.removeNth v) ∘ ⇑finSumFinEquiv) (σ (Sum.inl i)) := by
    funext i
    rw [derivShuffleLeftFwdRanked_inl_succAbove]
    simp [Function.comp_apply, Fin.removeNth_apply, permFinOfSum,
      Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd]
  have hright :
      (fun i : Fin n =>
          ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
            (derivShuffleLeftFwdRanked k σ (Sum.inr i))) =
        fun i : Fin n => ((k.removeNth v) ∘ ⇑finSumFinEquiv) (σ (Sum.inr i)) := by
    funext i
    rw [derivShuffleLeftFwdRanked_inr]
    simp [Function.comp_apply, Fin.removeNth_apply, permFinOfSum,
      Equiv.permCongr_apply]
  have hleft_remove :
      (derivShuffleRank k σ).removeNth
          (fun i : Fin (m + 1) =>
            v (Fin.finAddFlipAssoc (finSumFinEquiv (derivShuffleLeftFwdRanked k σ (Sum.inl i))))) =
        fun i : Fin m => v (k.succAbove (finSumFinEquiv (σ (Sum.inl i)))) := by
    funext i
    simpa [Function.comp_apply, Fin.removeNth_apply] using congr_fun hleft i
  have hright_eval :
      (fun i : Fin n =>
          v (Fin.finAddFlipAssoc (finSumFinEquiv (derivShuffleLeftFwdRanked k σ (Sum.inr i))))) =
        fun i : Fin n => v (k.succAbove (finSumFinEquiv (σ (Sum.inr i)))) := by
    funext i
    simpa [Function.comp_apply, Fin.removeNth_apply] using congr_fun hright i
  have hk_eval :
      v (Fin.finAddFlipAssoc (finSumFinEquiv (finSuccSumEquiv.symm k))) = v k := by
    simp [finSuccSumEquiv]
  rw [hleft_remove, hright_eval, hk_eval]
  simp only [Fin.removeNth_apply]
  simp only [Units.smul_def, smul_smul, mul_assoc]
  simp only [Int.reduceNeg, Units.val_mul, map_zsmul, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_smul, mul_assoc]
  congr 1
  rcases Nat.even_or_odd k.val with hq | hq <;>
    rcases Nat.even_or_odd (derivShuffleRank k σ).val with hj | hj
  · have hqu : ((-1 : ℤˣ) ^ k.val) = 1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = 1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = 1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = 1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = 1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = 1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = -1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = -1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = -1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = -1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = 1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = 1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = -1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = -1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = -1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = -1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]

private theorem uncurryFinLeftExpandedSummand_sum_coset
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    {τ₁ τ₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)}
    (hcoset : (Quotient.mk'' τ₁ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' τ₂) :
    (∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₁ j) =
      ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₂ j := by
  rw [← uncurrySum_summand_uncurryFin_left_expand_mk f g' h w τ₁,
    ← uncurrySum_summand_uncurryFin_left_expand_mk f g' h w τ₂, hcoset]

private lemma card_filter_comp_perm_local {n : ℕ} (e : Equiv.Perm (Fin n))
    (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (P ∘ ⇑e)).card = (Finset.univ.filter P).card := by
  have : Finset.univ.filter (P ∘ ⇑e) = (Finset.univ.filter P).map e.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Function.comp_apply]
    exact ⟨fun h => ⟨e i, h, by simp⟩, fun ⟨j, hj, hji⟩ => by simpa [← hji]⟩
  rw [this, Finset.card_map]

private lemma derivShuffleRank_of_coset
    (k : Fin (m + n + 1)) (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (Quotient.mk'' (derivShuffleLeftFwd k σ₁) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' (derivShuffleLeftFwd k σ₂)) :
    derivShuffleRank k σ₁ = derivShuffleRank k σ₂ := by
  have hrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
      (derivShuffleLeftFwd k σ₁) (derivShuffleLeftFwd k σ₂) := by
    rwa [← Quotient.eq]
  have hσrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂ :=
    derivShuffleLeftFwd_coset_injective k σ₁ σ₂ hrel
  rw [QuotientGroup.leftRel_apply] at hσrel
  obtain ⟨⟨τl, τr⟩, hblock⟩ := hσrel
  have hσ₂ : σ₂ = σ₁ * Equiv.Perm.sumCongr τl τr := by
    simpa [Equiv.Perm.sumCongrHom_apply, mul_assoc, mul_left_cancel] using
      (inv_mul_eq_iff_eq_mul.mp hblock.symm)
  apply Fin.ext
  simp only [derivShuffleRank, permFinOfSum, Equiv.permCongr_apply,
    finSumFinEquiv_symm_apply_castAdd]
  have hmap : (fun i : Fin m => (finSumFinEquiv (σ₂ (Sum.inl i))).val < k.val) =
      (fun i : Fin m => (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val) ∘ τl := by
    funext i
    have hel : finSumFinEquiv (σ₂ (Sum.inl i)) = finSumFinEquiv (σ₁ (Sum.inl (τl i))) := by
      congr 1
      erw [hσ₂]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      congr 1
    rw [hel]
    rfl
  have hfilter : (Finset.univ.filter (fun i : Fin m =>
        (finSumFinEquiv (σ₂ (Sum.inl i))).val < k.val)) =
      Finset.univ.filter ((fun i : Fin m =>
        (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val) ∘ τl) := by
    ext i
    simp [hmap]
  rw [hfilter]
  exact (card_filter_comp_perm_local τl (fun i : Fin m =>
    (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val)).symm

private lemma preimage_k_injective (τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))
    (j₁ j₂ : Fin (m + 1))
    (h : (derivShuffleEquivLeft.symm (τ', j₁)).1 = (derivShuffleEquivLeft.symm (τ', j₂)).1) :
    j₁ = j₂ := by
  let k : Fin (m + n + 1) := (derivShuffleEquivLeft.symm (τ', j₁)).1
  let σ₁ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j₁)).2
  let σ₂ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j₂)).2
  have hk₂ : (derivShuffleEquivLeft.symm (τ', j₂)).1 = k := by
    simpa [k] using h.symm
  have hσ₁ : (derivShuffleEquivLeft.symm (τ', j₁)).2 = Quotient.mk'' σ₁ := by
    exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j₁)).2)).symm
  have hσ₂ : (derivShuffleEquivLeft.symm (τ', j₂)).2 = Quotient.mk'' σ₂ := by
    exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j₂)).2)).symm
  have hpre₁ : derivShuffleEquivLeft (k, Quotient.mk'' σ₁) = (τ', j₁) := by
    have h₁ := derivShuffleEquivLeft.apply_symm_apply (τ', j₁)
    convert h₁ using 1
    congr 1
    apply Prod.ext
    · rfl
    · exact hσ₁.symm
  have hpre₂ : derivShuffleEquivLeft (k, Quotient.mk'' σ₂) = (τ', j₂) := by
    have h₂ := derivShuffleEquivLeft.apply_symm_apply (τ', j₂)
    convert h₂ using 1
    congr 1
    apply Prod.ext
    · simp [k, hk₂]
    · exact hσ₂.symm
  have hrank₁ : derivShuffleRank k σ₁ = j₁ := by
    have h₁ := congrArg Prod.snd hpre₁
    simpa using h₁
  have hrank₂ : derivShuffleRank k σ₂ = j₂ := by
    have h₂ := congrArg Prod.snd hpre₂
    simpa using h₂
  have hcoset₁ : (Quotient.mk'' (derivShuffleLeftFwd k σ₁) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    have h₁ := congrArg Prod.fst hpre₁
    simpa using h₁
  have hcoset₂ : (Quotient.mk'' (derivShuffleLeftFwd k σ₂) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    have h₂ := congrArg Prod.fst hpre₂
    simpa using h₂
  have hrank : derivShuffleRank k σ₁ = derivShuffleRank k σ₂ :=
    derivShuffleRank_of_coset k σ₁ σ₂ (hcoset₁.trans hcoset₂.symm)
  rw [← hrank₁, hrank, hrank₂]


private lemma coset_mul_sumCongr (τ₀ ρ : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h : (Quotient.mk'' ρ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' τ₀) :
    ∃ τl : Equiv.Perm (Fin (m + 1)), ∃ τr : Equiv.Perm (Fin n),
      ρ = τ₀ * Equiv.Perm.sumCongr τl τr := by
  have hrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range ρ τ₀ := by
    rwa [← Quotient.eq]
  rw [QuotientGroup.leftRel_apply] at hrel
  obtain ⟨⟨τl, τr⟩, hblock⟩ := hrel
  refine ⟨τl⁻¹, τr⁻¹, ?_⟩
  have h₁ : ρ * Equiv.Perm.sumCongr τl τr = τ₀ :=
    (inv_mul_eq_iff_eq_mul.mp hblock.symm).symm
  calc
    ρ = ρ * Equiv.Perm.sumCongr τl τr * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ := by
      have hprod : Equiv.Perm.sumCongr τl τr * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ = 1 := by
        ext x
        cases x <;> simp
      rw [mul_assoc, hprod, mul_one]
    _ = τ₀ * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ := by
      rw [h₁]
private def removeHole {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p) : Fin m :=
  if h : x < p then
    ⟨x.val, by
      have hxmp : x.val < p.val := h
      have hpm : p.val ≤ m := Nat.lt_succ_iff.mp (by simpa using p.isLt)
      omega⟩
  else
    ⟨x.val - 1, by
      have hp : p.val < x.val := lt_of_le_of_ne (le_of_not_gt h) (by
        intro heq
        exact hx (Fin.ext heq.symm))
      have hxm : x.val ≤ m := Nat.lt_succ_iff.mp (by simpa using x.isLt)
      omega⟩

@[simp] private theorem succAbove_removeHole {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p) :
    p.succAbove (removeHole p x hx) = x := by
  by_cases h : x < p
  · let i : Fin m := ⟨x.val, by
        have hxmp : x.val < p.val := h
        have hpm : p.val ≤ m := Nat.lt_succ_iff.mp (by simpa using p.isLt)
        omega⟩
    have h1 : removeHole p x hx = i := by
      rw [removeHole]
      simp [h, i]
    rw [h1]
    have hcond : (Fin.castSucc i : Fin (m + 1)) < p := by
      simpa [i] using h
    rw [Fin.succAbove]
    rw [if_pos hcond]
    change i.castSucc = x
    apply Fin.ext
    simp [i]
  · have hp : p.val < x.val := lt_of_le_of_ne (le_of_not_gt h) (by
      intro heq
      exact hx (Fin.ext heq.symm))
    let i : Fin m := ⟨x.val - 1, by
        have hxm : x.val ≤ m := Nat.lt_succ_iff.mp (by simpa using x.isLt)
        omega⟩
    have h1 : removeHole p x hx = i := by
      rw [removeHole]
      simp [h, i]
    rw [h1]
    have hnot : ¬ (Fin.castSucc i : Fin (m + 1)) < p := by
      intro hc
      have hi : i.val = x.val - 1 := rfl
      have hcv : (Fin.castSucc i : Fin (m + 1)).val = x.val - 1 := rfl
      omega
    have hxsub : x.val - 1 + 1 = x.val := by omega
    rw [Fin.succAbove]
    rw [if_neg hnot]
    change i.succ = x
    apply Fin.ext
    simp [i, hxsub]

@[simp] private theorem removeHole_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    removeHole p (p.succAbove i) (Fin.succAbove_ne p i) = i := by
  apply Fin.ext
  by_cases h : (Fin.castSucc i : Fin (m + 1)) < p
  · have hcast : p.succAbove i = (Fin.castSucc i : Fin (m + 1)) := by
      rw [Fin.succAbove]
      rw [if_pos h]
    simp [removeHole, hcast, h]
  · have hsucc : p.succAbove i = (i.succ : Fin (m + 1)) := by
      rw [Fin.succAbove]
      rw [if_neg h]
    have hnot : ¬ (i.succ : Fin (m + 1)) < p := by
      intro hc
      have hcv : (Fin.castSucc i : Fin (m + 1)).val = i.val := rfl
      have hsv : (i.succ : Fin (m + 1)).val = i.val + 1 := rfl
      omega
    simp [removeHole, hsucc, hnot]

private def inducedPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) : Equiv.Perm (Fin m) where
  toFun i := removeHole (τl j) (τl (j.succAbove i)) (by
    intro h
    exact Fin.succAbove_ne j i (Equiv.injective τl h))
  invFun i := removeHole j (τl.symm ((τl j).succAbove i)) (by
    intro h
    have h' : (τl j).succAbove i = τl j := by
      simpa using congrArg τl h
    exact Fin.succAbove_ne (τl j) i h')
  left_inv i := by
    simp [removeHole_succAbove]
  right_inv i := by
    simp [removeHole_succAbove]

private theorem inducedPerm_succAbove {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) (i : Fin m) :
    (τl j).succAbove (inducedPerm τl j i) = τl (j.succAbove i) := by
  unfold inducedPerm
  exact succAbove_removeHole (τl j) (τl (j.succAbove i)) (by
    intro h
    exact Fin.succAbove_ne j i (Equiv.injective τl h))

private theorem inducedPerm_mul {m : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    inducedPerm (τ₁ * τ₂) j = inducedPerm τ₁ (τ₂ j) * inducedPerm τ₂ j := by
  ext i
  simp [inducedPerm]

private theorem inducedPerm_one {m : ℕ} (j : Fin (m + 1)) :
    inducedPerm (1 : Equiv.Perm (Fin (m + 1))) j = 1 := by
  ext i
  simp [inducedPerm]

private theorem succAbove_val_of_lt {m : ℕ} (j : Fin (m + 1)) (i : Fin m) (h : i.val < j.val) :
    (j.succAbove i).val = i.val := by
  rw [Fin.succAbove]
  rw [if_pos (by simpa using h)]
  rfl

private theorem succAbove_val_of_ge {m : ℕ} (j : Fin (m + 1)) (i : Fin m) (h : j.val ≤ i.val) :
    (j.succAbove i).val = i.val + 1 := by
  rw [Fin.succAbove]
  rw [if_neg]
  · rfl
  · intro hc
    have hcv : (Fin.castSucc i : Fin (m + 1)).val = i.val := rfl
    omega

private theorem removeHole_val_of_lt {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p)
    (h : x.val < p.val) : (removeHole p x hx).val = x.val := by
  rw [removeHole]
  by_cases hx' : x < p
  · simp [hx']
  · have hnp : ¬ x.val < p.val := by
      intro hc
      exact hx' hc
    omega

private theorem removeHole_val_of_ge {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p)
    (h : p.val < x.val) : (removeHole p x hx).val = x.val - 1 := by
  rw [removeHole]
  by_cases hx' : x < p
  · have hc : x.val < p.val := hx'
    omega
  · simp [hx']
private theorem inducedPerm_swap_left {m : ℕ} (j b : Fin (m + 1)) (hjb : j < b) :
    inducedPerm (Equiv.swap j b) j =
      Fin.cycleIcc (⟨j.val, by omega⟩ : Fin m) ⟨b.val - 1, by omega⟩ := by
  ext i
  dsimp [inducedPerm]
  by_cases hm : m = 0
  · subst hm
    exact Fin.elim0 i
  haveI : NeZero m := ⟨hm⟩
  have hbj1 : b.val - 1 < m := by omega
  have hjm : j.val < m := by omega
  by_cases h1 : i.val < j.val
  · have hsucc : (j.succAbove i).val = i.val := succAbove_val_of_lt j i h1
    have hne2 : j.succAbove i ≠ b := by
      intro hne
      have : i.val = b.val := by
        simpa [hsucc] using congrArg Fin.val hne
      omega
    have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val := by
      simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
    have hrm : (removeHole b (j.succAbove i) hne2).val = i.val := by
      have hx : (j.succAbove i).val < b.val := by
        rw [hsucc]
        omega
      rw [removeHole_val_of_lt b (j.succAbove i) hne2 hx]
      exact hsucc
    have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val := by
      have hlt : i < ⟨j.val, hjm⟩ := h1
      exact congrArg Fin.val (Fin.cycleIcc_of_lt hlt)
    have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
      simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
    simpa [hswapel, hrm] using hcyc.symm
  · have hge : j.val ≤ i.val := le_of_not_gt h1
    by_cases h2 : i.val < b.val - 1
    · have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
      have hne2 : j.succAbove i ≠ b := by
        intro hne
        have : i.val + 1 = b.val := by
          simpa [hsucc] using congrArg Fin.val hne
        omega
      have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val + 1 := by
        simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
      have hrm : (removeHole b (j.succAbove i) hne2).val = i.val + 1 := by
        have hx : (j.succAbove i).val < b.val := by
          rw [hsucc]
          omega
        rw [removeHole_val_of_lt b (j.succAbove i) hne2 hx]
        exact hsucc
      have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val + 1 := by
        have hle : (⟨j.val, hjm⟩ : Fin m) ≤ i := by
          exact hge
        have hlt2 : i < ⟨b.val - 1, hbj1⟩ := h2
        have hstep := congrArg Fin.val (Fin.cycleIcc_of_ge_of_lt hle hlt2)
        rw [hstep]
        exact Fin.val_add_one_of_lt' (by omega)
      have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
        simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
      simpa [hswapel, hrm] using hcyc.symm
    · have hge2 : b.val - 1 ≤ i.val := le_of_not_gt h2
      by_cases h3 : i.val = b.val - 1
      · have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
        have hb : j.succAbove i = b := by
          apply Fin.ext
          have hjvb : j.val < b.val := hjb
          have hbpos : 0 < b.val := lt_of_le_of_lt (Nat.zero_le j.val) hjvb
          simp [hsucc, h3]
          omega
        have hsa : Equiv.swap j b (j.succAbove i) = j := by
          rw [hb]
          simp
        have hrm' : (Equiv.swap j b (j.succAbove i)) ≠ (Equiv.swap j b) j := by
          intro hne
          have : j = b := by
            rw [hsa, Equiv.swap_apply_left] at hne
            exact hne
          exact hjb.ne this
        have hrm : (removeHole ((Equiv.swap j b) j) (Equiv.swap j b (j.succAbove i)) hrm').val = j.val := by
          have hx : (Equiv.swap j b (j.succAbove i)).val < (Equiv.swap j b j).val := by
            rw [hsa, Equiv.swap_apply_left]
            exact hjb
          exact (removeHole_val_of_lt (Equiv.swap j b j) (Equiv.swap j b (j.succAbove i)) hrm' hx).trans (congrArg Fin.val hsa)
        have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = j.val := by
          have hjvb : j.val < b.val := hjb
          have hbpos : 0 < b.val := lt_of_le_of_lt (Nat.zero_le j.val) hjvb
          have hle : (⟨j.val, hjm⟩ : Fin m) ≤ ⟨b.val - 1, hbj1⟩ := by
            exact (show j.val ≤ b.val - 1 from by omega)
          have hi : i = (⟨b.val - 1, hbj1⟩ : Fin m) := by
            apply Fin.ext
            exact h3
          have hlast : Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i = ⟨j.val, hjm⟩ := by
            rw [hi]
            exact Fin.cycleIcc_of_last hle
          exact congrArg Fin.val hlast
        exact hrm.trans hcyc.symm
      · have hge3 : b.val ≤ i.val := by omega
        have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
        have hne2 : j.succAbove i ≠ b := by
          intro hne
          have : i.val + 1 = b.val := by
            simpa [hsucc] using congrArg Fin.val hne
          omega
        have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val + 1 := by
          simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
        have hrm : (removeHole b (j.succAbove i) hne2).val = i.val := by
          have hx : b.val < (j.succAbove i).val := by
            rw [hsucc]
            omega
          rw [removeHole_val_of_ge b (j.succAbove i) hne2 hx]
          omega
        have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val := by
          have hgt : (⟨b.val - 1, hbj1⟩ : Fin m) < i := by
            exact (show b.val - 1 < i.val from by omega)
          exact congrArg Fin.val (Fin.cycleIcc_of_gt hgt)
        have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
          simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
        simpa [hswapel, hrm] using hcyc.symm


private theorem inducedPerm_revPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
      (Fin.rev j) =
      (Fin.revPerm : Equiv.Perm (Fin m)) * inducedPerm τl j * (Fin.revPerm : Equiv.Perm (Fin m))⁻¹ := by
  ext i
  have hconj : (Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹ =
      Fin.revPerm * τl * Fin.revPerm⁻¹ := rfl
  have hmain : ∀ x : Fin m, Fin.rev (inducedPerm τl j x) =
      (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j)) (Fin.rev x) := by
    intro x
    have hsa := inducedPerm_succAbove τl j x
    have hL : (Fin.rev (τl j)).succAbove (Fin.rev (inducedPerm τl j x)) =
        Fin.rev ((τl j).succAbove (inducedPerm τl j x)) := by
      simp [Fin.succAbove_rev_left]
    have hR : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) =
        Fin.rev (τl (j.succAbove x)) := by
      have hstep1 : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) =
          Fin.revPerm (τl (Fin.revPerm⁻¹ ((Fin.rev j).succAbove (Fin.rev x)))) := by
        rfl
      rw [hstep1]
      have hsj : Fin.rev (j.succAbove x) = (Fin.rev j).succAbove (Fin.rev x) := by
        simp [Fin.succAbove_rev_right, Fin.rev_rev]
      have hsj' : Fin.revPerm⁻¹ ((Fin.rev j).succAbove (Fin.rev x)) = j.succAbove x := by
        rw [← hsj]
        simp [Fin.rev_rev]
      rw [hsj']
      rfl
    have hleft : (Fin.rev (τl j)).succAbove (Fin.rev (inducedPerm τl j x)) =
        ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) := by
      rw [hL, hsa, hR]
    have hright : (Fin.rev (τl j)).succAbove
          ((inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j)) (Fin.rev x)) =
        ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) := by
      simpa [hconj, Fin.rev_rev, Function.comp_apply] using
        inducedPerm_succAbove ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j) (Fin.rev x)
    exact (Fin.succAbove_right_injective (p := Fin.rev (τl j))).eq_iff.mp (hleft.trans hright.symm)
  change (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j) i).val =
    (Fin.rev (inducedPerm τl j (Fin.rev i))).val
  have hsub := hmain (Fin.rev i)
  rw [hsub]
  congr 1
  simp [Fin.rev_rev]


private theorem sign_swap_ne {m : ℕ} (j b : Fin (m + 1)) (h : j ≠ b) :
    Equiv.Perm.sign (Equiv.swap j b) = (-1 : ℤˣ) := by
  simp [h]

private theorem neg_one_pow_ite (n : ℕ) : (-1 : ℤˣ) ^ n = if Even n then 1 else -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (-1 : ℤˣ) ^ n.succ = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) := by
      simpa using (pow_succ (a := (-1 : ℤˣ)) (n := n))
    rw [hstep, ih]
    by_cases hn : Even n
    · have hodd : ¬ Even (n + 1) := by
        rw [Nat.even_iff]
        have hn' : n % 2 = 0 := (Nat.even_iff.mp hn)
        omega
      simp [hn, hodd]
    · have hev : Even (n + 1) := by
        rw [Nat.even_iff]
        have hn' : n % 2 = 1 := by
          have hcases := Nat.mod_two_eq_zero_or_one n
          have hn0 : n % 2 ≠ 0 := by
            intro h0
            apply hn
            rw [Nat.even_iff]
            exact h0
          omega
        omega
      simp [hn, hev]

theorem neg_one_pow_add (n m : ℕ) : (-1 : ℤˣ) ^ (n + m) = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) ^ m := by
  rw [neg_one_pow_ite (n := n + m), neg_one_pow_ite (n := n), neg_one_pow_ite (n := m)]
  have hmod : (n + m) % 2 = (n % 2 + m % 2) % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    simp [Nat.even_iff, hn, hm, hmod]

private theorem inducedPerm_swap_sign_left {m : ℕ} (j b : Fin (m + 1)) (hjb : j < b) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  rw [inducedPerm_swap_left j b hjb]
  have hle : (⟨j.val, by omega⟩ : Fin m) ≤ ⟨b.val - 1, by omega⟩ := by
    exact (show j.val ≤ b.val - 1 from by omega)
  rw [Fin.sign_cycleIcc_of_le hle]
  rw [sign_swap_ne j b hjb.ne]
  have hcombine : (-1 : ℤˣ) * (-1 : ℤˣ) ^ (j.val + b.val) = (-1 : ℤˣ) ^ (1 + j.val + b.val) := by
    rw [mul_comm]
    have hstep : (-1 : ℤˣ) ^ (j.val + b.val).succ = (-1 : ℤˣ) ^ (j.val + b.val) * (-1 : ℤˣ) := by
      simpa using (pow_succ (a := (-1 : ℤˣ)) (n := j.val + b.val))
    rw [← hstep]
    rw [show (j.val + b.val).succ = 1 + j.val + b.val from by omega]
  rw [hcombine]
  have hpow_ite (n : ℕ) : (-1 : ℤˣ) ^ n = if Even n then 1 else -1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : (-1 : ℤˣ) ^ n.succ = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) := by
        simpa using (pow_succ (a := (-1 : ℤˣ)) (n := n))
      rw [hstep, ih]
      by_cases hn : Even n
      · have hodd : ¬ Even (n + 1) := by
          rw [Nat.even_iff]
          have hn' : n % 2 = 0 := (Nat.even_iff.mp hn)
          omega
        simp [hn, hodd]
      · have hev : Even (n + 1) := by
          rw [Nat.even_iff]
          have hn' : n % 2 = 1 := by
            have hcases := Nat.mod_two_eq_zero_or_one n
            have hn0 : n % 2 ≠ 0 := by
              intro h
              apply hn
              rw [Nat.even_iff]
              exact h
            omega
          omega
        simp [hn, hev]
  have hjvb : j.val < b.val := hjb
  have hmod : (b.val - 1 - j.val) % 2 = (1 + j.val + b.val) % 2 := by omega
  have hvals : (⟨b.val - 1, by omega⟩ : Fin m).val - (⟨j.val, by omega⟩ : Fin m).val = b.val - 1 - j.val := by
    rw [show (⟨b.val - 1, by omega⟩ : Fin m).val = b.val - 1 from rfl,
      show (⟨j.val, by omega⟩ : Fin m).val = j.val from rfl]
  rw [hvals]
  change (-1 : ℤˣ) ^ (b.val - 1 - j.val) = (-1 : ℤˣ) ^ (1 + j.val + b.val)
  simp [hpow_ite, Nat.even_iff, hmod]


private theorem inducedPerm_swap_sign_right {m : ℕ} (j b : Fin (m + 1)) (hbj : b < j) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  have hrev := inducedPerm_revPerm (τl := Equiv.swap j b) (j := j)
  have hconj : (Fin.revPerm : Equiv.Perm (Fin (m + 1))) * Equiv.swap j b * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹ =
      Equiv.swap (Fin.rev j) (Fin.rev b) := by
    ext x
    by_cases hx : x = Fin.rev j
    · subst hx
      simp [Fin.revPerm, Fin.rev_rev]
    · by_cases hx' : x = Fin.rev b
      · subst hx'
        simp [Fin.revPerm, Fin.rev_rev]
      · have hrnj : Fin.rev x ≠ j := by
          intro h
          apply hx
          rw [← h]
          simp [Fin.rev_rev]
        have hrnb : Fin.rev x ≠ b := by
          intro h
          apply hx'
          rw [← h]
          simp [Fin.rev_rev]
        simp [Equiv.swap_apply_def, hx, hx', hrnj, hrnb, Fin.rev_rev]
  have hjv : (Fin.rev j).val = m - j.val := by
    change (m + 1) - (j.val + 1) = m - j.val
    omega
  have hbv : (Fin.rev b).val = m - b.val := by
    change (m + 1) - (b.val + 1) = m - b.val
    omega
  have hrevlt : Fin.rev j < Fin.rev b := by
    change (Fin.rev j).val < (Fin.rev b).val
    rw [hjv, hbv]
    omega
  have hsig1 := inducedPerm_swap_sign_left (j := Fin.rev j) (b := Fin.rev b) hrevlt
  have hsign_conj : Equiv.Perm.sign (Equiv.swap (Fin.rev j) (Fin.rev b)) = Equiv.Perm.sign (Equiv.swap j b) := by
    rw [sign_swap_ne (Fin.rev j) (Fin.rev b) (ne_of_lt hrevlt), sign_swap_ne j b (ne_of_lt hbj).symm]
  have hsign_rev : Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin m)) * inducedPerm (Equiv.swap j b) j * (Fin.revPerm : Equiv.Perm (Fin m))⁻¹) =
      Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    have h1 : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) * (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) * Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j)) =
        Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
      rw [← mul_assoc]
      have hs : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) * Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) = 1 := by
        rw [← Equiv.Perm.sign_mul]
        have hsq : (Fin.revPerm : Equiv.Perm (Fin m)) * (Fin.revPerm : Equiv.Perm (Fin m)) = 1 := by
          ext x
          simp
        rw [hsq, Equiv.Perm.sign_one]
      rw [hs, one_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  have hmain : Equiv.Perm.sign (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * Equiv.swap j b * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j)) =
      Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
    rw [hrev]
    exact hsign_rev
  rw [← hmain]
  rw [hconj]
  rw [hsig1]
  rw [hsign_conj]
  change Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ ((Fin.rev j).val + (Fin.rev b).val) =
    Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val)
  congr 1
  have hmod : ((m - j.val) + (m - b.val)) % 2 = (j.val + b.val) % 2 := by omega
  change (-1 : ℤˣ) ^ ((Fin.rev j).val + (Fin.rev b).val) = (-1 : ℤˣ) ^ (j.val + b.val)
  simp [neg_one_pow_ite, Nat.even_iff, hmod]

private theorem inducedPerm_swap_sign {m : ℕ} (j b : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  by_cases h : j = b
  · subst h
    have h1 : inducedPerm (Equiv.swap j j) j = (1 : Equiv.Perm (Fin m)) := by
      simpa using inducedPerm_one j
    rw [h1]
    simp only [Equiv.Perm.sign_one, Equiv.swap_self, Equiv.Perm.sign_refl, one_mul]
    have hjj : Even (j.val + j.val) := by
      rw [Nat.even_iff]
      omega
    rw [show (-1 : ℤˣ) ^ (j.val + j.val) = 1 from by
      rw [neg_one_pow_ite (n := j.val + j.val)]
      simp [hjj]]
  · rcases lt_or_gt_of_ne h with hjb | hbj
    · exact inducedPerm_swap_sign_left j b hjb
    · exact inducedPerm_swap_sign_right j b hbj



private theorem removeHole_congr {m : ℕ} (p : Fin (m + 1)) {x y : Fin (m + 1)} (hxy : x = y)
    (hx : x ≠ p) (hy : y ≠ p) : removeHole p x hx = removeHole p y hy := by
  subst y
  apply Fin.ext
  by_cases hlt : x < p
  · rw [removeHole_val_of_lt p x hx hlt]
  · have hpne : p ≠ x := by
      intro h
      exact hx h.symm
    have hvne : p.val ≠ x.val := by
      intro h
      exact hpne (Fin.ext h)
    have hge : p.val < x.val := lt_of_le_of_ne (le_of_not_gt hlt) hvne
    rw [removeHole_val_of_ge p x hx hge]

private theorem inducedPerm_swap_away {m : ℕ} (a b j' : Fin (m + 1)) (haj : j' ≠ a) (hbj : j' ≠ b) :
    inducedPerm (Equiv.swap a b) j' =
      Equiv.swap (removeHole j' a (Ne.symm haj)) (removeHole j' b (Ne.symm hbj)) := by
  ext i
  dsimp [inducedPerm]
  by_cases hia : j'.succAbove i = a
  · have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
      rw [hia]
      intro h
      have hb : b = j' := by
        simpa [Equiv.swap_apply_def] using h
      exact (Ne.symm hbj) hb
    have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = (removeHole j' b (Ne.symm hbj)).val := by
      have harg : Equiv.swap a b (j'.succAbove i) = b := by
        rw [hia]
        simp
      exact congrArg Fin.val (removeHole_congr j' harg hne (Ne.symm hbj))
    have hi : i = removeHole j' a (Ne.symm haj) := by
      have hsa1 : j'.succAbove (removeHole j' a (Ne.symm haj)) = a := succAbove_removeHole j' a (Ne.symm haj)
      exact ((Fin.succAbove_right_injective (p := j')).eq_iff.mp (hsa1.trans hia.symm)).symm
    rw [hi]
    simp [Equiv.swap_apply_def, haj, hbj]
  · by_cases hib : j'.succAbove i = b
    · have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
        rw [hib]
        intro h
        have ha : a = j' := by
          simpa [Equiv.swap_apply_def] using h
        exact (Ne.symm haj) ha
      have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = (removeHole j' a (Ne.symm haj)).val := by
        have harg : Equiv.swap a b (j'.succAbove i) = a := by
          rw [hib]
          simp
        exact congrArg Fin.val (removeHole_congr j' harg hne (Ne.symm haj))
      have hi : i = removeHole j' b (Ne.symm hbj) := by
        have hsa1 : j'.succAbove (removeHole j' b (Ne.symm hbj)) = b := succAbove_removeHole j' b (Ne.symm hbj)
        exact ((Fin.succAbove_right_injective (p := j')).eq_iff.mp (hsa1.trans hib.symm)).symm
      rw [hi]
      simp [Equiv.swap_apply_def, haj, hbj]
    · have hfix : Equiv.swap a b (j'.succAbove i) = j'.succAbove i := by
        simp [Equiv.swap_apply_def, hia, hib]
      have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
        intro h
        exact Fin.succAbove_ne j' i (hfix.symm.trans h)
      have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = i.val := by
        have h1 : removeHole j' (Equiv.swap a b (j'.succAbove i)) hne = removeHole j' (j'.succAbove i) (Fin.succAbove_ne j' i) :=
          removeHole_congr j' hfix hne (Fin.succAbove_ne j' i)
        have h2 : (removeHole j' (j'.succAbove i) (Fin.succAbove_ne j' i)).val = i.val :=
          congrArg Fin.val (removeHole_succAbove j' i)
        exact (congrArg Fin.val h1).trans h2
      have hne_a : i ≠ removeHole j' a (Ne.symm haj) := by
        intro h
        have : j'.succAbove (removeHole j' a (Ne.symm haj)) = j'.succAbove i := by rw [h]
        have : j'.succAbove i = a := by
          rw [succAbove_removeHole] at this
          exact this.symm
        exact hia this
      have hne_b : i ≠ removeHole j' b (Ne.symm hbj) := by
        intro h
        have : j'.succAbove (removeHole j' b (Ne.symm hbj)) = j'.succAbove i := by rw [h]
        have : j'.succAbove i = b := by
          rw [succAbove_removeHole] at this
          exact this.symm
        exact hib this
      simp [Equiv.swap_apply_def, hne_a, hne_b, haj, hbj, hia, hib]

private theorem inducedPerm_swap_sign' {m : ℕ} (a b j' : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap a b) j') =
      Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ (j'.val + (Equiv.swap a b j').val) := by
  by_cases hab : a = b
  · rw [hab]
    simp only [Equiv.swap_self, Equiv.Perm.sign_refl, Equiv.refl_apply, one_mul]
    have hrefl : inducedPerm (Equiv.refl (Fin (m + 1))) j' = 1 := by
      simpa using inducedPerm_one j'
    rw [hrefl]
    simp only [Equiv.Perm.sign_one]
    have hjj : Even (j'.val + j'.val) := by
      rw [Nat.even_iff]
      omega
    rw [show (-1 : ℤˣ) ^ (j'.val + j'.val) = 1 from by
      rw [neg_one_pow_ite (n := j'.val + j'.val)]
      simp [hjj]]
  · by_cases haj : j' = a
    · rw [haj]
      simpa using inducedPerm_swap_sign a b
    · by_cases hbj : j' = b
      · rw [hbj]
        simpa [Equiv.swap_comm] using inducedPerm_swap_sign b a
      · rw [inducedPerm_swap_away a b j' haj hbj]
        have hsa : Equiv.swap a b j' = j' := by
          simp [Equiv.swap_apply_def, haj, hbj]
        rw [hsa]
        have hne : removeHole j' a (Ne.symm haj) ≠ removeHole j' b (Ne.symm hbj) := by
          intro h
          have h1 : j'.succAbove (removeHole j' a (Ne.symm haj)) = a := succAbove_removeHole j' a (Ne.symm haj)
          have h2 : j'.succAbove (removeHole j' b (Ne.symm hbj)) = b := succAbove_removeHole j' b (Ne.symm hbj)
          have hcong : j'.succAbove (removeHole j' a (Ne.symm haj)) = j'.succAbove (removeHole j' b (Ne.symm hbj)) := by
            exact congrArg (fun z => j'.succAbove z) h
          exact hab (h1.symm.trans (hcong.trans h2))
        have hsig1 : Equiv.Perm.sign (Equiv.swap (removeHole j' a (Ne.symm haj)) (removeHole j' b (Ne.symm hbj))) = (-1 : ℤˣ) := by
          simp [hne]
        rw [hsig1]
        simp only [hab, Equiv.Perm.sign_swap', one_mul, neg_mul, if_false]
        have hjj : Even (j'.val + j'.val) := by
          rw [Nat.even_iff]
          omega
        rw [show (-1 : ℤˣ) ^ (j'.val + j'.val) = 1 from by
          rw [neg_one_pow_ite (n := j'.val + j'.val)]
          simp [hjj]]


private theorem sign_inducedPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm τl j) =
      Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val + (τl j).val) := by
  refine Trunc.induction_on (Equiv.Perm.truncSwapFactors τl) ?_
  rintro ⟨l, hprod, hswap⟩
  have hP' : ∀ (l : List (Equiv.Perm (Fin (m + 1)))), (∀ g ∈ l, g.IsSwap) →
      Equiv.Perm.sign (inducedPerm l.prod j) =
        Equiv.Perm.sign l.prod * (-1 : ℤˣ) ^ (j.val + (l.prod j).val) := by
    intro l
    induction l with
    | nil =>
        intro hswap
        have hjj : Even (j.val + j.val) := by
          rw [Nat.even_iff]
          omega
        simp only [List.prod_nil, inducedPerm_one, Equiv.Perm.sign_one, Equiv.Perm.coe_one,
          id_eq, one_mul]
        rw [show (-1 : ℤˣ) ^ (j.val + j.val) = 1 from by
          rw [neg_one_pow_ite (n := j.val + j.val)]
          simp [hjj]]
    | cons s l' ih =>
        intro hswap
        rcases hswap s (by simp) with ⟨a, b, hab, rfl⟩
        have hsig_sub := ih (fun g hg => hswap g (by simp [hg]))
        have hsign_mul : Equiv.Perm.sign (inducedPerm (Equiv.swap a b * l'.prod) j) =
            Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val) *
              (Equiv.Perm.sign l'.prod * (-1 : ℤˣ) ^ (j.val + (l'.prod j).val)) := by
          rw [inducedPerm_mul]
          rw [Equiv.Perm.sign_mul]
          rw [inducedPerm_swap_sign' a b (l'.prod j)]
          rw [hsig_sub]
        have hpow : (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val + (l'.prod j).val)) =
            (-1 : ℤˣ) ^ (j.val + (Equiv.swap a b (l'.prod j)).val) := by
          rw [neg_one_pow_ite, neg_one_pow_ite]
          have hmod : ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val + (l'.prod j).val)) % 2 =
              (j.val + (Equiv.swap a b (l'.prod j)).val) % 2 := by omega
          simp [Nat.even_iff, hmod]
        calc
          Equiv.Perm.sign (inducedPerm (Equiv.swap a b * l'.prod) j)
              = Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val) *
                  (Equiv.Perm.sign l'.prod * (-1 : ℤˣ) ^ (j.val + (l'.prod j).val)) := hsign_mul
          _ = (Equiv.Perm.sign (Equiv.swap a b) * Equiv.Perm.sign l'.prod) *
                (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val + (l'.prod j).val)) := by
                rw [neg_one_pow_add ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val) (j.val + (l'.prod j).val)]
                ac_rfl
          _ = Equiv.Perm.sign (Equiv.swap a b * l'.prod) * (-1 : ℤˣ) ^ (j.val + (Equiv.swap a b (l'.prod j)).val) := by
                rw [← Equiv.Perm.sign_mul, hpow]
          _ = Equiv.Perm.sign (Equiv.swap a b * l'.prod) * (-1 : ℤˣ) ^ (j.val + ((Equiv.swap a b * l'.prod) j).val) := by
                congr 1
  have hP := hP' l hswap
  rw [← hprod]
  exact hP

section Transport

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

omit [NormedAddCommGroup M] in
private theorem removeNth_comp_perm' (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1))
    (a : Fin (m + 1) → M) :
    j.removeNth (a ∘ τl) = (τl j).removeNth a ∘ inducedPerm τl j := by
  ext i
  change a (τl (j.succAbove i)) = a ((τl j).succAbove (inducedPerm τl j i))
  rw [inducedPerm_succAbove]

private theorem uncurryFinLeftExpandedSummand_mul_sumCongr
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ₀ : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (τl : Equiv.Perm (Fin (m + 1))) (τr : Equiv.Perm (Fin n)) (j : Fin (m + 1)) :
    uncurryFinLeftExpandedSummand f g' h w (τ₀ * Equiv.Perm.sumCongr τl τr) j =
      uncurryFinLeftExpandedSummand f g' h w τ₀ (τl j) := by
  unfold uncurryFinLeftExpandedSummand
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr]
  have hh : h (fun i : Fin n => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inr i))) =
      Equiv.Perm.sign τr • h (fun i : Fin n => w (τ₀ (Sum.inr i))) := by
    have hcomp : (fun i : Fin n => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inr i))) =
        (fun i : Fin n => w (τ₀ (Sum.inr i))) ∘ τr := by
      funext i
      simp [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [hcomp]
    exact h.map_perm (fun i : Fin n => w (τ₀ (Sum.inr i))) τr
  have hg : g' (w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl j))) (j.removeNth (fun i : Fin (m + 1) => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl i)))) =
      Equiv.Perm.sign (inducedPerm τl j) • g' (w (τ₀ (Sum.inl (τl j)))) ((τl j).removeNth (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))) := by
    have hfirst : (τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
      simp [Equiv.Perm.coe_mul]
    rw [hfirst]
    have hcomp : (fun i : Fin (m + 1) => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl i))) =
        (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i))) ∘ τl := by
      funext i
      simp [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [hcomp]
    rw [removeNth_comp_perm' τl j (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))]
    exact (g' (w (τ₀ (Sum.inl (τl j))))).map_perm
      ((τl j).removeNth (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))) (inducedPerm τl j)
  rw [hh, hg]
  have hsig : Equiv.Perm.sign (inducedPerm τl j) = Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val + (τl j).val) :=
    sign_inducedPerm τl j
  have hsig : Equiv.Perm.sign (inducedPerm τl j) = Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val + (τl j).val) :=
    sign_inducedPerm τl j
  simp only [Units.smul_def, smul_smul]
  simp only [Int.reduceNeg, Units.val_mul, map_zsmul, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_smul, mul_assoc]
  rw [hsig]
  congr 1
  have hjj : Even (j.val + j.val) := by
    rw [Nat.even_iff]
    omega
  have hpow2 : (-1 : ℤ) ^ (j.val + j.val) = 1 := by
    rw [show j.val + j.val = 2 * j.val from by omega]
    rw [pow_mul]
    simp
  have hsgn (x : ℤˣ) : (x : ℤ) * (x : ℤ) = 1 := by
    rcases Int.units_eq_one_or x with rfl | rfl <;> simp
  have hunitpow (k : ℕ) : (↑((-1 : ℤˣ) ^ k) : ℤ) = (-1 : ℤ) ^ k := by
    exact map_pow (Units.coeHom ℤ) (-1 : ℤˣ) k
  have hpowj : (-1 : ℤ) ^ j.val * (-1 : ℤ) ^ (j.val + (τl j).val) = (-1 : ℤ) ^ (τl j).val := by
    rw [← pow_add (a := (-1 : ℤ)) (m := j.val) (n := j.val + (τl j).val)]
    rw [show j.val + (j.val + (τl j).val) = (j.val + j.val) + (τl j).val from by omega]
    rw [pow_add (a := (-1 : ℤ)) (m := j.val + j.val) (n := (τl j).val)]
    rw [hpow2]
    simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign τl) with hτl | hτl <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τr) with hτr | hτr <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ₀) with hτ₀ | hτ₀ <;>
        simp [hτl, hτr, hτ₀, hpowj, hunitpow]

end Transport

private theorem uncurryFin_wedge_productL_precompL_fiber
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) :
    (∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w
        (derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm (τ', j)).1
          (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) j) =
      ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := by
  let τ₀ : Equiv.Perm (Fin (m + 1) ⊕ Fin n) := Quot.out τ'
  let ρ : Fin (m + 1) → Equiv.Perm (Fin (m + 1) ⊕ Fin n) := fun j =>
    derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm (τ', j)).1
      (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)
  let k : Fin (m + 1) → Fin (m + n + 1) := fun j =>
    (derivShuffleEquivLeft.symm (τ', j)).1
  have hρ_coset : ∀ j : Fin (m + 1),
      (Quotient.mk'' (derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm (τ', j)).1
        (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) :
          Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    intro j
    have hpre : derivShuffleEquivLeft ((derivShuffleEquivLeft.symm (τ', j)).1,
        Quotient.mk'' (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) = (τ', j) := by
      have h₁ := derivShuffleEquivLeft.apply_symm_apply (τ', j)
      convert h₁ using 1
      congr 1
      apply Prod.ext
      · rfl
      · exact Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j)).2)
    have h₁ := congrArg Prod.fst (hpre.symm.trans (derivShuffleEquivLeft_apply_mk_ranked
      (derivShuffleEquivLeft.symm (τ', j)).1 (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)))
    simpa [ρ] using h₁.symm
  have hρ_inl : ∀ j : Fin (m + 1),
      ρ j (Sum.inl j) = finSuccSumEquiv.symm (k j) := by
    intro j
    have hrank : derivShuffleRank (k j) (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2) = j := by
      let σ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j)).2
      have hσ : (derivShuffleEquivLeft.symm (τ', j)).2 = Quotient.mk'' σ := by
        exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j)).2)).symm
      have hpre : derivShuffleEquivLeft (k j, Quotient.mk'' σ) = (τ', j) := by
        have h₁ := derivShuffleEquivLeft.apply_symm_apply (τ', j)
        convert h₁ using 1
        congr 1
        apply Prod.ext
        · rfl
        · exact hσ.symm
      have h₁ := congrArg Prod.snd hpre
      simpa [k, σ] using h₁
    have h₁ : ρ j (Sum.inl (derivShuffleRank (k j) (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2))) =
        finSuccSumEquiv.symm (k j) := by
      simp [ρ, k, derivShuffleLeftFwdRanked_inl_j]
    have hslot : (Sum.inl j : Fin (m + 1) ⊕ Fin n) = Sum.inl (derivShuffleRank (k j) (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) := by
      exact congrArg (Sum.inl : Fin (m + 1) → Fin (m + 1) ⊕ Fin n) hrank.symm
    rw [hslot]
    exact h₁
  let ψ : Fin (m + 1) → Fin (m + 1) := fun j =>
    match τ₀⁻¹ (finSuccSumEquiv.symm (k j)) with
    | Sum.inl ℓ => ℓ
    | Sum.inr _ => 0
  have hψ_val : ∀ j : Fin (m + 1),
      uncurryFinLeftExpandedSummand f g' h w (ρ j) j =
        uncurryFinLeftExpandedSummand f g' h w τ₀ (ψ j) := by
    intro j
    have hcoset : (Quotient.mk'' (ρ j) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
        Quotient.mk'' τ₀ := by
      exact (hρ_coset j).trans (Quot.out_eq (q := τ')).symm
    obtain ⟨τl, τr, hdecomp⟩ := coset_mul_sumCongr τ₀ (ρ j) hcoset
    have htrans : uncurryFinLeftExpandedSummand f g' h w (ρ j) j =
        uncurryFinLeftExpandedSummand f g' h w τ₀ (τl j) := by
      rw [hdecomp]
      exact uncurryFinLeftExpandedSummand_mul_sumCongr f g' h w τ₀ τl τr j
    have hψj : Sum.inl (τl j) = τ₀⁻¹ (finSuccSumEquiv.symm (k j)) := by
      have h₂ : ρ j (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
        rw [hdecomp]
        simp [Equiv.Perm.coe_mul]
      rw [← hρ_inl j]
      simp [h₂]
    have hψj' : τl j = ψ j := by
      unfold ψ
      rw [← hψj]
    rw [htrans, hψj']
  have hψ_inl : ∀ j : Fin (m + 1), ∃ τl_j : Fin (m + 1),
      τ₀⁻¹ (finSuccSumEquiv.symm (k j)) = Sum.inl τl_j := by
    intro j
    have hcoset : (Quotient.mk'' (ρ j) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
        Quotient.mk'' τ₀ := by
      exact (hρ_coset j).trans (Quot.out_eq (q := τ')).symm
    obtain ⟨τl, τr, hdecomp⟩ := coset_mul_sumCongr τ₀ (ρ j) hcoset
    have h₂ : ρ j (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
      rw [hdecomp]
      simp [Equiv.Perm.coe_mul]
    have h₃ : τ₀⁻¹ (finSuccSumEquiv.symm (k j)) = Sum.inl (τl j) := by
      rw [← hρ_inl j]
      rw [h₂]
      simp
    exact ⟨τl j, h₃⟩
  have hψ_inj : Function.Injective ψ := by
    intro j₁ j₂ h
    have hk : k j₁ = k j₂ := by
      obtain ⟨τl₁, h₁⟩ := hψ_inl j₁
      obtain ⟨τl₂, h₂⟩ := hψ_inl j₂
      have hψ₁ : ψ j₁ = τl₁ := by
        unfold ψ
        rw [h₁]
      have hψ₂ : ψ j₂ = τl₂ := by
        unfold ψ
        rw [h₂]
      have hτl : τl₁ = τl₂ := by
        rw [← hψ₁, ← hψ₂, h]
      have hpre : τ₀⁻¹ (finSuccSumEquiv.symm (k j₁)) = τ₀⁻¹ (finSuccSumEquiv.symm (k j₂)) := by
        rw [h₁, h₂, hτl]
      have hk' : finSuccSumEquiv.symm (k j₁) = finSuccSumEquiv.symm (k j₂) :=
        (Equiv.injective τ₀⁻¹) hpre
      exact Equiv.injective finSuccSumEquiv.symm hk'
    exact preimage_k_injective τ' j₁ j₂ hk
  have hψ_surj : Function.Surjective ψ := by
    intro ℓ
    exact (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψ_inj, by simp⟩ |>.2 ℓ
  calc
    (∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (ρ j) j)
        = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₀ (ψ j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hψ_val j
    _ = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₀ j := by
          refine Finset.sum_bij (fun j _ => ψ j) ?_ ?_ ?_ ?_
          · intro j hj
            simp
          · intro j₁ hj₁ j₂ hj₂ h
            exact hψ_inj h
          · intro ℓ hℓ
            obtain ⟨j, hj⟩ := hψ_surj ℓ
            exact ⟨j, by simp, hj⟩
          · intro j hj
            rfl
    _ = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := rfl


theorem uncurryFin_wedge_productL_precompL_eq_domDomCongr
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N') :
    uncurryFin ((wedge_productL f).precompL M g' h) =
      domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin g') h f) := by
  ext v
  let w : Fin (m + 1) ⊕ Fin n → M := (v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv
  calc
    uncurryFin ((wedge_productL f).precompL M g' h) v
        = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedge_product (g' (v k)) h f (k.removeNth v) := by
          exact uncurryFin_wedge_productL_precompL_apply f g' h v
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            uncurrySum (f.compContinuousAlternatingMap₂ (g' (v k)) h) ((k.removeNth v) ∘ ⇑finSumFinEquiv) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [wedge_product_def]
          simp [uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply]
    _ = ∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
            (-1 : ℤ) ^ k.val •
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) σ ((k.removeNth v) ∘ ⇑finSumFinEquiv) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [uncurrySum_apply]
          simp [Finset.smul_sum]
    _ = ∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked k (Quot.out σ))
              (derivShuffleRank k (Quot.out σ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          have hstep := derivShuffleLeft_expanded_summand_eq f g' h v k (Quot.out σ)
          have hcong :
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) σ
                  ((k.removeNth v) ∘ ⇑finSumFinEquiv) =
                uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h)
                  (Quotient.mk'' (Quot.out σ)) ((k.removeNth v) ∘ ⇑finSumFinEquiv) :=
            congrArg (fun q : Equiv.Perm.ModSumCongr (Fin m) (Fin n) =>
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) q
                ((k.removeNth v) ∘ ⇑finSumFinEquiv)) (Quot.out_eq (q := σ)).symm
          rw [hcong]
          exact hstep
    _ = ∑ q : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm q).1
              (Quot.out (derivShuffleEquivLeft.symm q).2)) q.2 := by
          have hconv : (∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked k (Quot.out σ))
                  (derivShuffleRank k (Quot.out σ))) =
              ∑ p : (Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)),
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked p.1 (Quot.out p.2))
                  (derivShuffleRank p.1 (Quot.out p.2)) := by
            simpa [Finset.univ_product_univ] using
              (Finset.sum_product (s := (Finset.univ : Finset (Fin (m + n + 1))))
                (t := (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin m) (Fin n))))
                (f := fun p : (Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) =>
                  uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked p.1 (Quot.out p.2))
                    (derivShuffleRank p.1 (Quot.out p.2)))).symm
          rw [hconv]
          refine Finset.sum_bij (fun p _ => derivShuffleEquivLeft p) ?_ ?_ ?_ ?_
          · intro p hp
            simp
          · intro p₁ hp₁ p₂ hp₂ h
            exact Equiv.injective derivShuffleEquivLeft h
          · intro q hq
            exact ⟨derivShuffleEquivLeft.symm q, by simp, by simp⟩
          · intro p hp
            rw [show (derivShuffleEquivLeft.symm (derivShuffleEquivLeft p)).1 = p.1 from by simp,
              show (derivShuffleEquivLeft.symm (derivShuffleEquivLeft p)).2 = p.2 from by simp]
            have hpair : p = (p.1, Quotient.mk'' (Quot.out p.2)) := by
              apply Prod.ext
              · rfl
              · exact (Quot.out_eq (q := p.2)).symm
            have h2 : (derivShuffleEquivLeft p).2 = derivShuffleRank p.1 (Quot.out p.2) := by
              have h := derivShuffleEquivLeft_apply_mk_ranked p.1 (Quot.out p.2)
              conv_lhs =>
                rw [hpair]
              rw [h]
            rw [h2]
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n), ∑ j : Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm (τ', j)).1
              (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) j := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product (s := (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))))
              (t := (Finset.univ : Finset (Fin (m + 1))))
              (f := fun p : (Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1)) =>
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftFwdRanked (derivShuffleEquivLeft.symm p).1
                  (Quot.out (derivShuffleEquivLeft.symm p).2)) p.2))
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n), ∑ j : Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := by
          refine Finset.sum_congr rfl ?_
          intro τ' hτ'
          exact uncurryFin_wedge_productL_precompL_fiber f g' h w τ'
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n),
            uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h) τ' w := by
          refine Finset.sum_congr rfl ?_
          intro τ' hτ'
          exact (uncurrySum_summand_uncurryFin_left_expand_mk f g' h w (Quot.out τ')).symm.trans
            (congrArg (fun q : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) =>
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h) q w)
              (Quot.out_eq (q := τ')))
    _ = uncurrySum (f.compContinuousAlternatingMap₂ (uncurryFin g') h) w := by
          rw [uncurrySum_apply, ContinuousMultilinearMap.sum_apply]
    _ = (wedge_product (uncurryFin g') h f) (v ∘ ⇑Fin.finAddFlipAssoc) := by
          rw [wedge_product_def, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply]
    _ = domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin g') h f) v := by
          rw [wedge_product_uncurryFin_apply]

private theorem zero_wedge' (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (0 : M [⋀^Fin m]→L[𝕜] 𝕜) h (ContinuousLinearMap.mul 𝕜 𝕜) = 0 := by
  have := add_wedge (0 : M [⋀^Fin m]→L[𝕜] 𝕜) 0 h (ContinuousLinearMap.mul 𝕜 𝕜)
  simpa using this

private theorem wedge_zero' (g : M [⋀^Fin m]→L[𝕜] 𝕜) :
    wedge_product g (0 : M [⋀^Fin n]→L[𝕜] 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜) = 0 := by
  have := wedge_add g (0 : M [⋀^Fin n]→L[𝕜] 𝕜) 0 (ContinuousLinearMap.mul 𝕜 𝕜)
  simpa using this

private theorem sum_wedge_left {ι : Type*} (s : Finset ι)
    (g : ι → M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (∑ i ∈ s, g i) h (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, wedge_product (g i) h (ContinuousLinearMap.mul 𝕜 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_wedge']
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, add_wedge, ih, Finset.sum_insert hni]

private theorem sum_wedge_right {ι : Type*} (s : Finset ι)
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : ι → M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product g (∑ i ∈ s, h i) (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, wedge_product g (h i) (ContinuousLinearMap.mul 𝕜 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wedge_zero']
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, wedge_add, ih, Finset.sum_insert hni]

private theorem sum_smul_wedge_left {ι : Type*} (s : Finset ι)
    (c : ι → 𝕜) (g : ι → M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (∑ i ∈ s, c i • g i) h (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, c i • wedge_product (g i) h (ContinuousLinearMap.mul 𝕜 𝕜) := by
  rw [sum_wedge_left]; congr 1; ext i; rw [← smul_wedge]

private theorem sum_smul_wedge_right {ι : Type*} (s : Finset ι)
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (c : ι → 𝕜) (h : ι → M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product g (∑ i ∈ s, c i • h i) (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, c i • wedge_product g (h i) (ContinuousLinearMap.mul 𝕜 𝕜) := by
  rw [sum_wedge_right]; congr 1; ext i; rw [← wedge_smul]

private theorem domDomCongr_sum_smul {ι : Type*} {m' n' : ℕ}
    (e : Fin m' ≃ Fin n') (s : Finset ι) (c : ι → 𝕜) (f : ι → M [⋀^Fin m']→L[𝕜] 𝕜) :
    domDomCongr e (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • domDomCongr e (f i) := by
  rw [domDomCongr_sum]; congr 1

private def tensorMulML {m n : ℕ} (A : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (B : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) :
    MultilinearMap 𝕜 (fun _ : Fin (m + n) => M) 𝕜 :=
  ((LinearMap.mul' 𝕜 𝕜).compMultilinearMap (A.domCoprod B)).domDomCongr finSumFinEquiv

private theorem tensorMulML_apply {m n : ℕ} (A : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (B : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) (v : Fin (m + n) → M) :
    tensorMulML A B v = A (v ∘ Fin.castAdd n) * B (v ∘ Fin.natAdd m) := by
  simp [tensorMulML, LinearMap.mul'_apply]
  rfl

private theorem tensorMulML_smul_right {m n : ℕ} (c : 𝕜)
    (A : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (B : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) :
    tensorMulML A (c • B) = c • tensorMulML A B := by
  ext v
  simp [tensorMulML_apply]
  ring

private theorem tensorMulML_smul_left {m n : ℕ} (c : 𝕜)
    (A : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (B : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) :
    tensorMulML (c • A) B = c • tensorMulML A B := by
  ext v
  simp [tensorMulML_apply]
  ring

private theorem tensorMulML_eq_tensorProductMap {m n : ℕ}
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      tensorMulML g.toAlternatingMap h.toAlternatingMap := by
  ext v
  simp [tensorMulML_apply, tensorProductMap_apply]

private theorem nsmul_eq_smul_cast {A : Type*} [AddCommMonoid A] [Module 𝕜 A] (k : ℕ) (x : A) :
    k • x = (k : 𝕜) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih]
    rw [Nat.cast_succ, add_smul, one_smul]

private theorem tensorMulML_alt_alt {m n : ℕ} (a : M [⋀^Fin m]→L[𝕜] 𝕜)
    (F : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) :
    MultilinearMap.alternatization (tensorMulML a.toAlternatingMap
        ↑(MultilinearMap.alternatization F)) =
      (n.factorial : 𝕜) • MultilinearMap.alternatization
        (tensorMulML (a.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜) F) := by
  unfold tensorMulML
  rw [ContinuousAlternatingMap.alternatization_domDomCongr]
  rw [LinearMap.compMultilinearMap_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [AlternatingMap.coe_alternatization]
  rw [AlternatingMap.coe_alternatization]
  rw [show (Fintype.card (Fin m)).factorial = m.factorial from by rw [Fintype.card_fin]]
  rw [show (Fintype.card (Fin n)).factorial = n.factorial from by rw [Fintype.card_fin]]
  rw [show m.factorial • a.toAlternatingMap = (m.factorial : 𝕜) • a.toAlternatingMap from
    nsmul_eq_smul_cast m.factorial a.toAlternatingMap]
  rw [show n.factorial • MultilinearMap.alternatization F =
      (n.factorial : 𝕜) • MultilinearMap.alternatization F from
    nsmul_eq_smul_cast n.factorial (MultilinearMap.alternatization F)]
  have hdom : ∀ (c₁ c₂ : 𝕜), (c₁ • a.toAlternatingMap).domCoprod
        (c₂ • MultilinearMap.alternatization F) =
      (c₁ * c₂) •
        (a.toAlternatingMap.domCoprod (MultilinearMap.alternatization F)) := by
    intro c₁ c₂
    change AlternatingMap.domCoprod' ((c₁ • a.toAlternatingMap) ⊗ₜ[𝕜]
        (c₂ • MultilinearMap.alternatization F)) =
      (c₁ * c₂) •
        (AlternatingMap.domCoprod' (a.toAlternatingMap ⊗ₜ[𝕜] MultilinearMap.alternatization F))
    rw [TensorProduct.smul_tmul_smul]
    exact map_smul (f := AlternatingMap.domCoprod' (R' := 𝕜) (Mᵢ := M) (N₁ := 𝕜) (N₂ := 𝕜)
      (ιa := Fin m) (ιb := Fin n)) (c₁ * c₂)
      (a.toAlternatingMap ⊗ₜ[𝕜] MultilinearMap.alternatization F)
  have hsmul : (LinearMap.mul' 𝕜 𝕜).compAlternatingMap
      (((m.factorial : 𝕜) • a.toAlternatingMap).domCoprod
        ((n.factorial : 𝕜) • MultilinearMap.alternatization F)) =
      ((m.factorial * n.factorial : ℕ) : 𝕜) •
        (LinearMap.mul' 𝕜 𝕜).compAlternatingMap
          (a.toAlternatingMap.domCoprod (MultilinearMap.alternatization F)) := by
    rw [hdom (m.factorial : 𝕜) (n.factorial : 𝕜)]
    norm_cast
    ext v
    simp [LinearMap.compAlternatingMap_apply]
  rw [hsmul]
  rw [AlternatingMap.domDomCongr_smul]
  rw [ContinuousAlternatingMap.alternatization_domDomCongr]
  rw [LinearMap.compMultilinearMap_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [AlternatingMap.coe_alternatization]
  rw [show (Fintype.card (Fin m)).factorial = m.factorial from by rw [Fintype.card_fin]]
  rw [show m.factorial • a.toAlternatingMap = (m.factorial : 𝕜) • a.toAlternatingMap from
    nsmul_eq_smul_cast m.factorial a.toAlternatingMap]
  rw [show ((m.factorial : 𝕜) • a.toAlternatingMap).domCoprod
        (MultilinearMap.alternatization F) =
      (m.factorial : 𝕜) • (a.toAlternatingMap.domCoprod (MultilinearMap.alternatization F)) from by
    simpa [one_smul] using hdom (m.factorial : 𝕜) 1]
  rw [LinearMap.compAlternatingMap_smul]
  rw [AlternatingMap.domDomCongr_smul]
  ext v
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [Nat.cast_mul]
  ring

private theorem tensorMulML_alt_alt_left {m n : ℕ} (F : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (b : M [⋀^Fin n]→L[𝕜] 𝕜) :
    MultilinearMap.alternatization (tensorMulML ↑(MultilinearMap.alternatization F)
        b.toAlternatingMap) =
      (m.factorial : 𝕜) • MultilinearMap.alternatization
        (tensorMulML F (b.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜)) := by
  unfold tensorMulML
  rw [ContinuousAlternatingMap.alternatization_domDomCongr]
  rw [LinearMap.compMultilinearMap_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [AlternatingMap.coe_alternatization]
  rw [AlternatingMap.coe_alternatization]
  rw [show (Fintype.card (Fin m)).factorial = m.factorial from by rw [Fintype.card_fin]]
  rw [show (Fintype.card (Fin n)).factorial = n.factorial from by rw [Fintype.card_fin]]
  rw [show m.factorial • MultilinearMap.alternatization F =
      (m.factorial : 𝕜) • MultilinearMap.alternatization F from
    nsmul_eq_smul_cast m.factorial (MultilinearMap.alternatization F)]
  rw [show n.factorial • b.toAlternatingMap = (n.factorial : 𝕜) • b.toAlternatingMap from
    nsmul_eq_smul_cast n.factorial b.toAlternatingMap]
  have hdom : ∀ (c₁ c₂ : 𝕜), (c₁ • MultilinearMap.alternatization F).domCoprod
        (c₂ • b.toAlternatingMap) =
      (c₁ * c₂) •
        ((MultilinearMap.alternatization F).domCoprod b.toAlternatingMap) := by
    intro c₁ c₂
    change AlternatingMap.domCoprod' ((c₁ • MultilinearMap.alternatization F) ⊗ₜ[𝕜]
        (c₂ • b.toAlternatingMap)) =
      (c₁ * c₂) •
        (AlternatingMap.domCoprod' (MultilinearMap.alternatization F ⊗ₜ[𝕜] b.toAlternatingMap))
    rw [TensorProduct.smul_tmul_smul]
    exact map_smul (f := AlternatingMap.domCoprod' (R' := 𝕜) (Mᵢ := M) (N₁ := 𝕜) (N₂ := 𝕜)
      (ιa := Fin m) (ιb := Fin n)) (c₁ * c₂)
      (MultilinearMap.alternatization F ⊗ₜ[𝕜] b.toAlternatingMap)
  have hsmul : (LinearMap.mul' 𝕜 𝕜).compAlternatingMap
      (((m.factorial : 𝕜) • MultilinearMap.alternatization F).domCoprod
        ((n.factorial : 𝕜) • b.toAlternatingMap)) =
      ((m.factorial * n.factorial : ℕ) : 𝕜) •
        (LinearMap.mul' 𝕜 𝕜).compAlternatingMap
          ((MultilinearMap.alternatization F).domCoprod b.toAlternatingMap) := by
    rw [hdom (m.factorial : 𝕜) (n.factorial : 𝕜)]
    norm_cast
    ext v
    simp [LinearMap.compAlternatingMap_apply]
  rw [hsmul]
  rw [AlternatingMap.domDomCongr_smul]
  rw [ContinuousAlternatingMap.alternatization_domDomCongr]
  rw [LinearMap.compMultilinearMap_alternatization]
  rw [MultilinearMap.domCoprod_alternization]
  rw [AlternatingMap.coe_alternatization]
  rw [show (Fintype.card (Fin n)).factorial = n.factorial from by rw [Fintype.card_fin]]
  rw [show n.factorial • b.toAlternatingMap = (n.factorial : 𝕜) • b.toAlternatingMap from
    nsmul_eq_smul_cast n.factorial b.toAlternatingMap]
  rw [show (MultilinearMap.alternatization F).domCoprod ((n.factorial : 𝕜) • b.toAlternatingMap) =
      (n.factorial : 𝕜) • ((MultilinearMap.alternatization F).domCoprod b.toAlternatingMap) from by
    simpa [one_smul] using hdom 1 (n.factorial : 𝕜)]
  rw [LinearMap.compAlternatingMap_smul]
  rw [AlternatingMap.domDomCongr_smul]
  ext v
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [Nat.cast_mul]
  ring

private theorem tensorMulML_assoc {m n p : ℕ} (A : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
    (B : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜) (C : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜) :
    (tensorMulML (tensorMulML A B) C).domDomCongr Fin.finAssoc =
      tensorMulML A (tensorMulML B C) := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, tensorMulML_apply]
  have hA : ((fun i => v (Fin.finAssoc i)) ∘ Fin.castAdd p) ∘ Fin.castAdd n =
      v ∘ Fin.castAdd (n + p) := by
    funext i
    change v (Fin.finAssoc (Fin.castAdd p (Fin.castAdd n i))) = v (Fin.castAdd (n + p) i)
    congr 1
  have hB : ((fun i => v (Fin.finAssoc i)) ∘ Fin.castAdd p) ∘ Fin.natAdd m =
      (v ∘ Fin.natAdd m) ∘ Fin.castAdd p := by
    funext j
    change v (Fin.finAssoc (Fin.castAdd p (Fin.natAdd m j))) = v (Fin.natAdd m (Fin.castAdd p j))
    congr 1
  have hC : (fun i => v (Fin.finAssoc i)) ∘ Fin.natAdd (m + n) =
      (v ∘ Fin.natAdd m) ∘ Fin.natAdd n := by
    funext k
    change v (Fin.finAssoc (Fin.natAdd (m + n) k)) = v (Fin.natAdd m (Fin.natAdd n k))
    congr 1
    simp [Fin.finAssoc, Fin.ext_iff]
    omega
  rw [hA, hB, hC]
  simp [mul_assoc]

private theorem wedge_toAlternatingMap [CharZero 𝕜] {m n : ℕ}
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h).toAlternatingMap =
      ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
        MultilinearMap.alternatization (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap := by
  apply AlternatingMap.ext
  intro v
  exact wedge_product_eq_alternatization g h (ContinuousLinearMap.mul 𝕜 𝕜) v

private theorem toAlternatingMap_domDomCongr {ι ι' : Type*} (e : ι ≃ ι')
    (f : M [⋀^ι]→L[𝕜] 𝕜) :
    (domDomCongr e f).toAlternatingMap = f.toAlternatingMap.domDomCongr e := by
  rfl

theorem wedge_mul_assoc [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) :
    domDomCongr Fin.finAssoc.symm (g ∧[𝕜] (h ∧[𝕜] l)) = ((g ∧[𝕜] h) ∧[𝕜] l) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [toAlternatingMap_domDomCongr]
  rw [wedge_toAlternatingMap (g := g) (h := h ∧[𝕜] l)]
  rw [wedge_toAlternatingMap (g := g ∧[𝕜] h) (h := l)]
  have hTgl : (tensorProductMap g (h ∧[𝕜] l) (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      ((↑(n.factorial * p.factorial) : 𝕜))⁻¹ •
        tensorMulML g.toAlternatingMap ↑(MultilinearMap.alternatization
          (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap) := by
    rw [tensorMulML_eq_tensorProductMap (g := g) (h := h ∧[𝕜] l)]
    rw [show ((h ∧[𝕜] l).toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin (n + p) => M) 𝕜) =
        ((↑(n.factorial * p.factorial) : 𝕜))⁻¹ • ↑(MultilinearMap.alternatization
          (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap) from by
      simpa using congrArg (fun x : M [⋀^Fin (n + p)]→ₗ[𝕜] 𝕜 =>
        (x : MultilinearMap 𝕜 (fun _ : Fin (n + p) => M) 𝕜))
          (wedge_toAlternatingMap (g := h) (h := l))]
    rw [tensorMulML_smul_right]
  have hAlt_smul : ∀ (c : 𝕜) {n : ℕ} (X : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜),
      MultilinearMap.alternatization (c • X) = c • MultilinearMap.alternatization X := by
    intro c n X
    ext v
    simp only [MultilinearMap.alternatization_apply, AlternatingMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext σ
    change Equiv.Perm.sign σ • (c • X (v ∘ σ)) = c • (Equiv.Perm.sign σ • X (v ∘ σ))
    exact smul_comm (Equiv.Perm.sign σ) c (X (v ∘ σ))
  have hL : MultilinearMap.alternatization (tensorProductMap g (h ∧[𝕜] l)
        (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      ((↑(n.factorial * p.factorial) : 𝕜))⁻¹ • (↑(n + p).factorial : 𝕜) •
        MultilinearMap.alternatization (tensorMulML g.toAlternatingMap
          (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap) := by
    rw [hTgl, hAlt_smul]
    rw [tensorMulML_alt_alt (a := g)
      (F := (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap)]
  have hTgh : (tensorProductMap (g ∧[𝕜] h) l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
        tensorMulML ↑(MultilinearMap.alternatization
          (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap)
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜) := by
    rw [tensorMulML_eq_tensorProductMap (g := g ∧[𝕜] h) (h := l)]
    rw [show ((g ∧[𝕜] h).toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin (m + n) => M) 𝕜) =
        ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ • ↑(MultilinearMap.alternatization
          (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap) from by
      simpa using congrArg (fun x : M [⋀^Fin (m + n)]→ₗ[𝕜] 𝕜 =>
        (x : MultilinearMap 𝕜 (fun _ : Fin (m + n) => M) 𝕜))
          (wedge_toAlternatingMap (g := g) (h := h))]
    rw [tensorMulML_smul_left]
  have hR : MultilinearMap.alternatization (tensorProductMap (g ∧[𝕜] h) l
        (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ • (↑(m + n).factorial : 𝕜) •
        MultilinearMap.alternatization (tensorMulML
          (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜)) := by
    rw [hTgh, hAlt_smul]
    rw [tensorMulML_alt_alt_left (F := (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap)
      (b := l)]
  rw [hL]
  rw [hR]
  have hZ : MultilinearMap.alternatization (tensorMulML
        (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜)) =
      (MultilinearMap.alternatization (tensorMulML (g.toAlternatingMap : MultilinearMap 𝕜
        (fun _ : Fin m => M) 𝕜)
        (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap)).domDomCongr
          Fin.finAssoc.symm := by
    have hta := tensorMulML_assoc (A := (g.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜))
      (B := (h.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜))
      (C := (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜))
    have hAlt := congrArg MultilinearMap.alternatization hta
    rw [ContinuousAlternatingMap.alternatization_domDomCongr] at hAlt
    have hconv : tensorMulML (tensorMulML (g.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
        (h.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜))
        (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜) =
        tensorMulML (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜) := by
      rw [tensorMulML_eq_tensorProductMap (g := g) (h := h)]
    rw [hconv] at hAlt
    have hconv' : tensorMulML (g.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜) (tensorMulML
        (h.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin n => M) 𝕜)
        (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜)) =
        tensorMulML (g.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin m => M) 𝕜)
          (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap := by
      rw [tensorMulML_eq_tensorProductMap (g := h) (h := l)]
    rw [hconv'] at hAlt
    have hsymm : (MultilinearMap.alternatization (tensorMulML
        (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜))).domDomCongr
          Fin.finAssoc =
        MultilinearMap.alternatization (tensorMulML (g.toAlternatingMap : MultilinearMap 𝕜
          (fun _ : Fin m => M) 𝕜)
          (tensorProductMap h l (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap) := hAlt
    rw [← hsymm]
    rw [← AlternatingMap.domDomCongr_trans (σ₁ := Fin.finAssoc) (σ₂ := Fin.finAssoc.symm)
      (f := MultilinearMap.alternatization (tensorMulML
        (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap
          (l.toAlternatingMap : MultilinearMap 𝕜 (fun _ : Fin p => M) 𝕜)))]
    simp
  rw [hZ]
  rw [AlternatingMap.domDomCongr_smul]
  rw [AlternatingMap.domDomCongr_smul]
  rw [AlternatingMap.domDomCongr_smul]
  simp only [smul_smul]
  have hscalar : (↑(m.factorial * (n + p).factorial) : 𝕜)⁻¹ * (↑(n.factorial * p.factorial) : 𝕜)⁻¹ *
        (↑(n + p).factorial : 𝕜) =
      (↑(p.factorial * (m + n).factorial) : 𝕜)⁻¹ * (↑(m.factorial * n.factorial) : 𝕜)⁻¹ *
        (↑(m + n).factorial : 𝕜) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev]
    have hm : (↑m.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hn : (↑n.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hp : (↑p.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
    have hnp : (↑(n + p).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + p))
    have hmn : (↑(n + m).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + m))
    have hnm : (↑(m + n).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n))
    field_simp [hm, hn, hp, hnp, hmn, hnm]
  rw [← mul_assoc, ← mul_assoc, hscalar]
  rw [show (↑(p.factorial * (m + n).factorial) : 𝕜)⁻¹ =
      (↑((m + n).factorial * p.factorial) : 𝕜)⁻¹ from by
    simp [Nat.mul_comm]]

private lemma tensorProductMap_mul_swap (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (tensorProductMap h g (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap =
      (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap.domDomCongr finAddFlip := by
  ext w
  simp only [ContinuousMultilinearMap.coe_coe, tensorProductMap_apply,
    ContinuousLinearMap.mul_apply', MultilinearMap.domDomCongr_apply]
  conv_lhs => rw [mul_comm]
  congr 1
  · apply congrArg g
    funext x
    change w (Fin.natAdd n x) = w (finAddFlip (Fin.castAdd n x))
    rw [← finAddFlip_apply_castAdd]
  · apply congrArg h
    funext x
    change w (Fin.castAdd m x) = w (finAddFlip (Fin.natAdd m x))
    rw [finAddFlip_apply_natAdd]

private lemma finAddCongr_val (i : Fin (m + n)) : (Fin.finAddCongr i).val = i.val := rfl

private lemma finAddFlip_trans_finAddCongr_eq :
    (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)) : Equiv.Perm (Fin (m + n))) =
      (_root_.finCongr (add_comm m n)).symm.permCongr (Equiv.Perm.addCasesSwapPerm n m) := by
  ext i
  by_cases h : i.val < m
  · simp [Equiv.permCongr_apply, Equiv.Perm.addCasesSwapPerm, _root_.finCongr,
      finAddFlip_apply_mk_left h, finAddCongr_val]
    simp [h]
  · have hge : m ≤ i.val := le_of_not_gt h
    simp [Equiv.permCongr_apply, Equiv.Perm.addCasesSwapPerm, _root_.finCongr,
      finAddFlip_apply_mk_right hge, finAddCongr_val]
    simp [h]

private lemma finAddFlip_trans_finAddCongr_sign :
    Equiv.Perm.sign (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)) :
      Equiv.Perm (Fin (m + n))) = (-1 : ℤˣ) ^ (m * n) := by
  rw [finAddFlip_trans_finAddCongr_eq, Equiv.Perm.sign_permCongr, Equiv.Perm.addCasesSwapPerm_sign]
  exact congrArg (fun k : ℕ => (-1 : ℤˣ) ^ k) (Nat.mul_comm n m)

private lemma units_neg_one_pow_smul (k : ℕ) (x : 𝕜) :
    ((-1 : ℤˣ) ^ k) • x = (-1 : 𝕜) ^ k • x := by
  rw [Units.smul_def]
  rw [← Int.cast_smul_eq_zsmul (R := 𝕜) ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ)) x]
  have hcast : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : 𝕜) = (-1 : 𝕜) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show (-1 : ℤˣ) ^ (k + 1) = (-1 : ℤˣ) ^ k * (-1 : ℤˣ) from pow_succ (-1 : ℤˣ) k]
      rw [pow_succ, Units.val_mul, Int.cast_mul, ih]
      norm_num
  rw [hcast]

theorem wedge_antisymm [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr Fin.finAddCongr := by
  ext v
  rw [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  rw [wedge_product_eq_alternatization (m := m) (n := n) g h (ContinuousLinearMap.mul 𝕜 𝕜) v]
  rw [wedge_product_eq_alternatization (m := n) (n := m) h g (ContinuousLinearMap.mul 𝕜 𝕜)
    (v ∘ Fin.finAddCongr)]
  rw [tensorProductMap_mul_swap g h]
  rw [ContinuousAlternatingMap.alternatization_domDomCongr finAddFlip]
  rw [AlternatingMap.domDomCongr_apply]
  have h_comp : (v ∘ Fin.finAddCongr) ∘ finAddFlip =
      v ∘ (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m))) := by
    funext x
    rfl
  rw [h_comp]
  rw [AlternatingMap.map_perm (g := MultilinearMap.alternatization
      (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap)
      v (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)))]
  rw [finAddFlip_trans_finAddCongr_sign]
  have hc : (↑(n.factorial * m.factorial) : 𝕜)⁻¹ = (↑(m.factorial * n.factorial) : 𝕜)⁻¹ := by
    congr 1
    rw [Nat.mul_comm]
  rw [hc]
  rw [units_neg_one_pow_smul (m * n)]
  rw [smul_smul, smul_smul]
  apply congrArg (fun s : 𝕜 => s • MultilinearMap.alternatization
      (tensorProductMap g h (ContinuousLinearMap.mul 𝕜 𝕜)).toMultilinearMap v)
  have hsq : (-1 : 𝕜) ^ (m * n) * (-1 : 𝕜) ^ (m * n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [mul_comm ((-1 : 𝕜) ^ (m * n)) (↑(m.factorial * n.factorial))⁻¹, mul_assoc, hsq, mul_one]

theorem elementaryCovector_iprod_wedge_product
    [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    {d : ℕ} (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin (m + 1) → Fin d) (J : Fin (n + 1) → Fin d) (x : M) :
    curryFin (domDomCongr Fin.finAddFlipAssoc
      ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J))) x =
      (curryFin (elementaryCovector b I) x ∧[𝕜] (elementaryCovector b J)) +
      (-1 : 𝕜) ^ (m + 1) • domDomCongr Fin.finAddFlipAssoc
        ((elementaryCovector b I) ∧[𝕜] curryFin (elementaryCovector b J) x) := by
  rw [elementaryCovector_wedge b I J,
    curryFin_elementaryCovector b I x, sum_smul_wedge_left]
  simp_rw [elementaryCovector_wedge b _ J]
  rw [curryFin_elementaryCovector b J x, sum_smul_wedge_right]
  simp_rw [elementaryCovector_wedge b I _]
  ext v; simp only [curryFin_apply, domDomCongr_apply, add_apply, smul_apply,
    sum_apply, smul_eq_mul, elementaryCovector_apply]
  rw [Matrix.det_succ_column_zero]
  simp_rw [show (Fin.cons x v ∘ ⇑Fin.finAddFlipAssoc)
      (0 : Fin ((m + 1) + (n + 1))) = x from by
    simp [Fin.finAddFlipAssoc, finCongr, Fin.cons_zero]]
  conv_rhs => rw [Finset.mul_sum]
  rw [show ∀ (f : Fin (m + 1) → 𝕜) (g : Fin (n + 1) → 𝕜),
      (∑ i, f i) + (∑ j, g j) =
      ∑ k, (Fin.addCases f g : Fin ((m + 1) + (n + 1)) → 𝕜) k from fun f g =>
    ((Fin.sum_univ_add (Fin.addCases f g)).symm ▸ by
      simp [Fin.addCases_left, Fin.addCases_right])]
  apply Finset.sum_congr rfl; intro ⟨k, hk⟩ _
  by_cases hlt : k < m + 1
  · rw [show (⟨k, hk⟩ : Fin _) = Fin.castAdd (n + 1) ⟨k, hlt⟩ from Fin.ext rfl]
    simp only [Fin.addCases_left, Fin.val_castAdd]
    congr 1
    exact Fin.det_subst_eq (Nat.add_right_comm m 1 n) _ _ (by
      intro i j; simp only [Matrix.submatrix_apply,
        Fin.addCases_succAbove_castAdd I J ⟨k, hlt⟩ i]
      have : ∀ j : Fin (m + n + 1),
          (Fin.cons x v ∘ ⇑(@Fin.finAddFlipAssoc m (n + 1) 1))
            (Fin.succ (Fin.cast (Nat.add_right_comm m 1 n).symm j)) = v j :=
        fun j => by simp [Function.comp, Fin.cons_succ, Fin.finAddFlipAssoc, finCongr]
      simp only [this])
  · have hge := Nat.le_of_not_lt hlt
    set j' : Fin (n + 1) := ⟨k - (m + 1), Nat.sub_lt_left_of_lt_add hge hk⟩
    rw [show (⟨k, hk⟩ : Fin _) = Fin.natAdd (m + 1) j' from
      Fin.ext (Nat.add_sub_cancel' hge).symm]
    simp only [Fin.addCases_right, Fin.val_natAdd]
    rw [pow_add]; ring_nf
    exact congr_arg (- ((b (J j')) x * · * (-1 : 𝕜) ^ m * (-1) ^ j'.val))
      (congr_arg Matrix.det (funext fun i => funext fun j => by
        simp only [Matrix.submatrix_apply,
          Fin.addCases_succAbove_natAdd I J j' i]; congr 1))

theorem iprod_wedge_product_mul [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (g : M [⋀^Fin (m + 1)]→L[𝕜] 𝕜) (h : M [⋀^Fin (n + 1)]→L[𝕜] 𝕜) (x : M) :
    curryFin (domDomCongr Fin.finAddFlipAssoc (g ∧[𝕜] h)) x =
      (curryFin g x ∧[𝕜] h) +
      (-1 : 𝕜) ^ (m + 1) • domDomCongr Fin.finAddFlipAssoc (g ∧[𝕜] curryFin h x) := by
  set d := Module.finrank 𝕜 M with hd_def
  let B : Module.Basis (Fin d) 𝕜 M := Module.finBasis 𝕜 M
  let b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜) := B.cDualBasis
  let basisG : Module.Basis (Fin (m + 1) ↪o Fin d) 𝕜 (M [⋀^Fin (m + 1)]→L[𝕜] 𝕜) :=
    elementaryCovectorBasis B
  let basisH : Module.Basis (Fin (n + 1) ↪o Fin d) 𝕜 (M [⋀^Fin (n + 1)]→L[𝕜] 𝕜) :=
    elementaryCovectorBasis B
  have basisG_eq : ∀ I : Fin (m + 1) ↪o Fin d,
      basisG I = elementaryCovector b ↑I := fun I => elementaryCovectorBasis_apply B I
  have basisH_eq : ∀ J : Fin (n + 1) ↪o Fin d,
      basisH J = elementaryCovector b ↑J := fun J => elementaryCovectorBasis_apply B J
  have hg : g = ∑ I : Fin (m + 1) ↪o Fin d, basisG.repr g I • elementaryCovector b ↑I := by
    conv_lhs => rw [← basisG.sum_repr g]
    apply Finset.sum_congr rfl; intro I _
    rw [basisG_eq]
  have hh : h = ∑ J : Fin (n + 1) ↪o Fin d, basisH.repr h J • elementaryCovector b ↑J := by
    conv_lhs => rw [← basisH.sum_repr h]
    apply Finset.sum_congr rfl; intro J _
    rw [basisH_eq]
  rw [hg, hh]
  rw [sum_smul_wedge_left]
  simp_rw [sum_smul_wedge_right]
  rw [domDomCongr_sum_smul]
  simp_rw [domDomCongr_sum_smul]
  simp_rw [curryFin_sum_smul]
  simp_rw [sum_smul_wedge_left, sum_smul_wedge_right]
  rw [domDomCongr_sum_smul]
  simp_rw [domDomCongr_sum_smul]
  rw [Finset.smul_sum]
  simp_rw [Finset.smul_sum, smul_comm ((-1 : 𝕜) ^ (m + 1))]
  rw [Finset.sum_comm
    (f := fun J I => basisH.repr h J •
      basisG.repr g I •
        (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro I _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro J _
  rw [show basisH.repr h J • basisG.repr g I •
      (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J) =
      basisG.repr g I • basisH.repr h J •
        (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J) from
    smul_comm _ _ _]
  rw [← smul_add, ← smul_add]
  congr 1
  congr 1
  exact elementaryCovector_iprod_wedge_product b I J x

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

open Fin

omit [FiniteDimensional ℝ M] in
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

omit [FiniteDimensional ℝ M] in
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

end ContinuousAlternatingMap
