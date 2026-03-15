/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F F' F'' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n m k : ℕ}

-- TODO: change notation
notation "Ω^" n "⟮" E ", " F "⟯" => E → E [⋀^Fin n]→L[ℝ] F

variable {v : E}
variable (ω τ : Ω^n⟮E, F⟯)
variable (f : E → F)

@[simp]
theorem add_apply : (ω + τ) v = ω v + τ v :=
  rfl

@[simp]
theorem sub_apply : (ω - τ) v = ω v - τ v :=
  rfl

@[simp]
theorem neg_apply : (-ω) v = -ω v :=
  rfl

@[simp]
theorem smul_apply (ω : Ω^n⟮E, F⟯) (c : ℝ) : (c • ω) v = c • ω v :=
  rfl

@[simp]
theorem zero_apply : (0 : Ω^n⟮E, F⟯) v = 0 :=
  rfl

/- The natural equivalence between differential forms from `E` to `F`
and maps from `E` to continuous 1-multilinear alternating maps from `E` to `F`. -/
def ofSubsingleton :
    (E → E →L[ℝ] F) ≃ (Ω^1⟮E, F⟯) where
  toFun f := fun e ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F 0 (f e)
  invFun f := fun e ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ E F 0).symm (f e)
  left_inv _ := rfl
  right_inv _ := by simp

/- The constant map is a differential form when `Fin n` is empty -/
def constOfIsEmpty (x : F) : Ω^0⟮E, F⟯ :=
  fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) x

/-- Exterior derivative of a differential form. -/
def ederiv (ω : Ω^n⟮E, F⟯) : Ω^n + 1⟮E, F⟯ :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

/- Exterior derivative of a differential form within a set -/
def ederivWithin (ω : Ω^n⟮E, F⟯) (s : Set E) : Ω^n + 1⟮E, F⟯ :=
  fun (x : E) ↦ .uncurryFin (fderivWithin ℝ ω s x)

@[simp]
theorem ederivWithin_univ (ω : Ω^n⟮E, F⟯) :
    ederivWithin ω univ = ederiv ω := by
  ext1 x
  rw[ederivWithin, ederiv, fderivWithin_univ]

theorem ederivWithin_add (ω₁ ω₂ : Ω^n⟮E, F⟯) (s : Set E) {x : E} (hsx : UniqueDiffWithinAt ℝ s x)
    (hω₁ : DifferentiableWithinAt ℝ ω₁ s x) (hω₂ : DifferentiableWithinAt ℝ ω₂ s x) :
    ederivWithin (ω₁ + ω₂) s x = ederivWithin ω₁ s x + ederivWithin ω₂ s x := by
  simp [ederivWithin, fderivWithin_add hsx hω₁ hω₂, uncurryFin_add]

theorem ederivWithin_smul (ω : Ω^n⟮E, F⟯) (c : ℝ) (s : Set E) {x : E}
    (hsx : UniqueDiffWithinAt ℝ s x) (hω : DifferentiableWithinAt ℝ ω s x) :
      ederivWithin (c • ω) s x = c • ederivWithin ω s x := by
  simp [ederivWithin, fderivWithin_const_smul hsx hω, uncurryFin_smul]

theorem ederivWithin_constOfIsEmpty (s : Set E) (x : E) (y : F) :
    ederivWithin (constOfIsEmpty y) s x = .uncurryFin (fderivWithin ℝ (constOfIsEmpty y) s x) :=
  rfl

theorem Filter.EventuallyEq.ederivWithin_eq {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  simp only[ederivWithin, uncurryFin, hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.ederivWithin_eq_of_mem {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.ederivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.ederivWithin_eq_of_insert {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  apply Filter.EventuallyEq.ederivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.ederivWithin' {ω₁ ω₂ : Ω^n⟮E, F⟯} {s t : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) : ederivWithin ω₁ t =ᶠ[𝓝[s] x] ederivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.ederivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EverntuallyEq.ederivWithin {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) : ederivWithin ω₁ s =ᶠ[𝓝[s] x] ederivWithin ω₂ s :=
  hs.ederivWithin' Subset.rfl

theorem Filter.EventuallyEq.ederivWithin_eq_nhds {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).ederivWithin_eq h.self_of_nhds

theorem ederivWithin_congr {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).ederivWithin_eq hx

theorem ederivWithin_congr' {ω₁ ω₂ : Ω^n⟮E, F⟯} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  ederivWithin_congr hs (hs hx)

theorem ederivWithin_apply (ω : Ω^n⟮E, F⟯) {s : Set E} {x : E}
    (h : DifferentiableWithinAt ℝ ω s x) (hs : UniqueDiffWithinAt ℝ s x) (v : Fin (n + 1) → E) :
      ederivWithin ω s x v = ∑ i, (-1) ^ i.val • fderivWithin ℝ (ω · (i.removeNth v)) s x (v i)
  := by
  simp only [ederivWithin, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderivWithin_apply h hs]

theorem ederivWithin_ederivWithin_apply (ω : Ω^n⟮E, F⟯) {s : Set E} {x}
    (hxx : x ∈ closure (interior s)) (hx : x ∈ s) (h : ContDiffWithinAt ℝ 2 ω s x)
    (hs : UniqueDiffOn ℝ s) :
    ederivWithin (ederivWithin ω s) s x = 0 := calc
  ederivWithin (ederivWithin ω s) s x =
    uncurryFin (fderivWithin ℝ (fun y ↦ uncurryFin (fderivWithin ℝ ω s y)) s x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderivWithin ℝ (fderivWithin ℝ ω s) s x) := by
    congr 1
    let t :  Set (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) := univ
    let hst : MapsTo (fderivWithin ℝ ω s) s univ := by unfold MapsTo; intro x _; trivial
    have : DifferentiableWithinAt ℝ (fderivWithin ℝ ω s) s x := (h.fderivWithin_right
      (hs) (by ring_nf; exact le_of_eq rfl) (hx)).differentiableWithinAt
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
    let ⟨ω'', h⟩ := this -- ω' has deriv ω''
    have uncurryDeriv := @ContinuousLinearMap.hasFDerivWithinAt ℝ _ _ _ _ _ _ _ _ _
      (@uncurryFinCLM ℝ E F _ _ _ _ _ n) (fderivWithin ℝ ω s x) t
    have chain : HasFDerivWithinAt (uncurryFinCLM ∘ (fderivWithin ℝ ω s)) (uncurryFinCLM ∘L ω'') s x
      := @HasFDerivWithinAt.comp ℝ _ _ _ _ _ _ _ _ _ _ (fderivWithin ℝ ω s) ω'' x s uncurryFinCLM
        uncurryFinCLM t uncurryDeriv h hst
    have := UniqueDiffOn.uniqueDiffWithinAt hs hx
    rw [h.fderivWithin this]
    exact chain.fderivWithin this
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivWithinAt
      (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl]) hs hxx hx

theorem ederivWithin_ederivWithin (ω : Ω^n⟮E, F⟯) {s : Set E} (h : ContDiffOn ℝ 2 ω s)
    (hs : UniqueDiffOn ℝ s) :
    EqOn (ederivWithin (ederivWithin ω s) s) 0 (s ∩ (closure (interior s))) :=
  fun _ ⟨ hx, hxx ⟩ => ederivWithin_ederivWithin_apply ω hxx hx (h.contDiffWithinAt hx) hs

theorem ederiv_add (ω₁ ω₂ : Ω^n⟮E, F⟯) {x : E} (hω₁ : DifferentiableAt ℝ ω₁ x)
    (hω₂ : DifferentiableAt ℝ ω₂ x) : ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x := by
  simp [ederiv, fderiv_add hω₁ hω₂, uncurryFin_add]

theorem ederiv_smul (ω : Ω^n⟮E, F⟯) (c : ℝ) {x : E} (hω : DifferentiableAt ℝ ω x) :
    ederiv (c • ω) x = c • ederiv ω x := by
  simp [ederiv, fderiv_const_smul hω, uncurryFin_smul]

theorem ederiv_constOfIsEmpty (x : E) (y : F) :
    ederiv (constOfIsEmpty y) x = .uncurryFin (fderiv ℝ (constOfIsEmpty y) x) :=
  rfl

theorem Filter.EventuallyEq.ederiv_eq {ω₁ ω₂ : Ω^n⟮E, F⟯} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ x = ederiv ω₂ x := by
  ext v
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply, h.fderiv_eq]

protected theorem Filter.EventuallyEq.ederiv {ω₁ ω₂ : Ω^n⟮E, F⟯} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ =ᶠ[𝓝 x] ederiv ω₂ :=
  h.eventuallyEq_nhds.mono fun _x hx ↦ hx.ederiv_eq

theorem ederiv_apply (ω : Ω^n⟮E, F⟯) {x : E} (hx : DifferentiableAt ℝ ω x) (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω · (i.removeNth v)) x (v i) := by
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderiv_apply hx]

theorem ederiv_ederiv_apply (ω : Ω^n⟮E, F⟯) {x : E} (h : ContDiffAt ℝ 2 ω x) :
  ederiv (ederiv ω) x = 0 := calc
  ederiv (ederiv ω) x = uncurryFin (fderiv ℝ (fun y ↦ uncurryFin (fderiv ℝ ω y)) x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderiv ℝ (fderiv ℝ ω) x) := by
    congr 1
    have : DifferentiableAt ℝ (fderiv ℝ ω) x := (h.fderiv_right
      (by ring_nf; exact le_of_eq rfl)).differentiableAt
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
    let ⟨ω'', h⟩ := this -- ω' has deriv ω''
    have uncurryDeriv := @ContinuousLinearMap.hasFDerivAt ℝ _ _ _ _ _ _ _ _ _
      (@uncurryFinCLM ℝ E F _ _ _ _ _ n) (fderiv ℝ ω x)
    have chain : HasFDerivAt (uncurryFinCLM ∘ (fderiv ℝ ω)) (uncurryFinCLM ∘L ω'') x
      := @HasFDerivAt.comp ℝ _ _ _ _ _ _ _ _ _ _ (fderiv ℝ ω) ω'' x uncurryFinCLM uncurryFinCLM
        uncurryDeriv h
    rw [h.fderiv]
    exact chain.fderiv
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl])

theorem ederiv_ederiv (ω : Ω^n⟮E, F⟯) (h : ContDiff ℝ 2 ω) : ederiv (ederiv ω) = 0 :=
  funext fun _ ↦ ederiv_ederiv_apply ω h.contDiffAt

/- Pullback of a form under a function -/
namespace DifferentialForm

def domDomCongr (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) : Ω^m⟮E, F⟯ :=
  fun e => (ω e).domDomCongr σ

theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) (e : E) (v : Fin m → E) :
    (domDomCongr σ ω) e v = (ω e) (v ∘ σ)  :=
  rfl

/- Pullback of a differential form -/
def pullback (f : E → F) (ω : Ω^k⟮F, G⟯) : Ω^k⟮E, G⟯ :=
    fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem pullback_zero (f : E → F) :
    pullback f (0 : Ω^k⟮F, G⟯) = 0 :=
  rfl

theorem pullback_add (f : E → F) (ω : Ω^k⟮F, G⟯) (τ : Ω^k⟮F, G⟯) :
    pullback f (ω + τ) = pullback f ω + pullback f τ :=
  rfl

theorem pullback_sub (f : E → F) (ω : Ω^k⟮F, G⟯) (τ : Ω^k⟮F, G⟯) :
    pullback f (ω - τ) = pullback f ω - pullback f τ :=
  rfl

theorem pullback_neg (f : E → F) (ω : Ω^k⟮F, G⟯) :
    - pullback f ω = pullback f (-ω) :=
  rfl

theorem pullback_smul (f : E → F) (ω : Ω^k⟮F, G⟯) (c : ℝ) :
    c • (pullback f ω) = pullback f (c • ω) :=
  rfl

theorem pullback_ofSubsingleton (f : E → F) (ω : F → F →L[ℝ] G) :
    pullback f (ofSubsingleton ω) = ofSubsingleton (fun e ↦ (ω (f e)).comp (fderiv ℝ f e)) :=
  rfl

theorem pullback_constOfIsEmpty (f : E → F) (g : G) :
    pullback f (constOfIsEmpty g) = fun _ ↦ (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) g)
  := rfl

/- Interior product of differential forms -/
def iprod (ω : Ω^m + 1⟮E, F⟯) (v : E → E) : Ω^m⟮E, F⟯ :=
    fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)

theorem iprod_apply (ω : Ω^m + 1⟮E, F⟯) (v : E → E) (e : E) :
    iprod ω v e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

/- Interior product is antisymmetric -/
theorem iprod_antisymm (ω : Ω^m + 2⟮E, ℝ⟯) (v w : E → E) (e : E) (m' : Fin m → E) :
    iprod (iprod ω v) w e m' = - iprod (iprod ω w) v e m' := by
  repeat
    rw[iprod_apply, curryFin_apply]
  let h := AlternatingMap.map_swap (ω e).toAlternatingMap (Fin.cons (w e) (Fin.cons (v e) m'))
    Fin.zero_ne_one
  rw [@coe_toAlternatingMap] at h
  rw [← h]
  clear h
  congr 1
  ext i
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  · rw[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne] <;>
    simp only [Fin.cons_succ, ← Fin.succ_zero_eq_one, ne_eq, Fin.succ_inj,
      Fin.succ_ne_zero, not_false_eq_true]

/- Interior product with twice the same vector field is zero -/
theorem iprod_iprod (ω : Ω^m + 2⟮E, ℝ⟯) (v : E → E) :
    iprod (iprod ω v) v = 0 := by
  ext e m'
  let h := iprod_antisymm ω v v e m'
  rw [eq_neg_iff_add_eq_zero, add_self_eq_zero] at h
  exact h

/- Wedge product of differential forms -/
def wedge_product (ω₁ : Ω^m⟮E, F⟯) (ω₂ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    Ω^(m + n)⟮E, F''⟯ := fun e => ContinuousAlternatingMap.wedge_product (ω₁ e) (ω₂ e) f

-- TODO: change notation
notation ω₁ "∧["f"]" ω₂ => wedge_product ω₁ ω₂ f
notation ω₁ "∧" ω₂ => wedge_product ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_product_def {ω₁ : Ω^m⟮E, F⟯} {ω₂ : Ω^n⟮E, F'⟯} {f : F →L[ℝ] F' →L[ℝ] F''}
    {x : E} : (ω₁ ∧[f] ω₂) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) f :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, ℝ⟯} {x : E} :
    (ω₁ ∧ ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.mul ℝ ℝ) :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {ω₁ : Ω^m⟮E, ℝ⟯} {ω₂ : Ω^n⟮E, F⟯} {x : E} :
    (ω₁ ∧[ContinuousLinearMap.lsmul ℝ ℝ] ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.lsmul ℝ ℝ) :=
  rfl

/- Associativity of wedge product -/
theorem wedge_assoc (ω₁ : Ω^m⟮E, ℝ⟯) (ω₂ : Ω^n⟮E, ℝ⟯) (ω₃ : Ω^k⟮E, ℝ⟯) :
    domDomCongr Fin.finAssoc.symm (ω₁ ∧ ω₂ ∧ ω₃) = (ω₁ ∧ ω₂) ∧ ω₃ := by
  ext x y
  rw[wedge_product_def, wedge_product_def, domDomCongr_apply, wedge_product_def, wedge_product_def,
    ← ContinuousAlternatingMap.domDomCongr_apply]
  exact ContinuousAlternatingMap.wedge_mul_assoc (ω₁ x) (ω₂ x) (ω₃ x) y

/- Left distributivity of wedge product -/
theorem add_wedge (ω₁ ω₂ : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    ((ω₁ + ω₂) ∧[f] τ) = (ω₁ ∧[f] τ) + (ω₂ ∧[f] τ) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.add_wedge (ω₁ x) (ω₂ x) (τ x) f

/- Right distributivity of wedge product -/
theorem wedge_add (ω : Ω^m⟮E, F⟯) (τ₁ τ₂ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ω ∧[f] (τ₁ + τ₂)) = (ω ∧[f] τ₁) + (ω ∧[f] τ₂) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.wedge_add (ω x) (τ₁ x) (τ₂ x) f

theorem smul_wedge (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) (c : ℝ) :
    c • (ω ∧ τ) = (c • ω) ∧ τ := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact ContinuousAlternatingMap.smul_wedge (ω x) (τ x) c

theorem wedge_smul (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) (c : ℝ) :
    c • (ω ∧ τ) = ω ∧ (c • τ) := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact ContinuousAlternatingMap.wedge_smul (ω x) (τ x) c

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) :
    (ω ∧ τ) = DifferentialForm.domDomCongr Fin.finAddCongr ((-1 : ℝ)^(m*n) • (τ ∧ ω)) := by
  ext x y
  rw[wedge_product_mul, domDomCongr_apply, _root_.smul_apply,
    wedge_product_mul, ← ContinuousAlternatingMap.domDomCongr_apply]
  let h := ContinuousAlternatingMap.wedge_antisymm (ω x) (τ x)
  exact congrFun (congrArg DFunLike.coe h) y

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/- Corollary of `wedge_antisymm` saying that a wedge of a m-form with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero (ω : Ω^m⟮E, ℝ⟯) (m_odd : Odd m) :
    (ω ∧ ω) = 0 := by
  ext1 x
  rw[wedge_product_mul]
  exact ContinuousAlternatingMap.wedge_self_odd_zero (ω x) m_odd

/- Pullback commutes with taking the wedge product -/
theorem pullback_wedge (f : G → E) (ω₁ : Ω^m⟮E, F⟯) (ω₂ : Ω^n⟮E, F'⟯)
    (f' : F →L[ℝ] F' →L[ℝ] F'') : pullback f (ω₁ ∧[f'] ω₂) = pullback f ω₁ ∧[f'] pullback f ω₂ := by
  ext x y
  rw[wedge_product_def, pullback, wedge_product_def, pullback, pullback,
    compContinuousLinearMap_apply]
  rw[ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    compContinuousLinearMap_apply, compContinuousLinearMap_apply]
  simp only [Function.comp_apply, smul_left_cancel_iff]
  rfl

/- The graded Leibniz rule for the exterior derivative of the wedge product -/
theorem ederiv_wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    ederiv (ω ∧[f] τ) = (domDomCongr Fin.finAddFlipAssoc (ederiv ω ∧[f] τ))
      + ((-1 : ℝ)^m) • ((ω ∧[f] ederiv τ)) := by
  ext x y
  rw[Pi.add_apply]
  erw[ContinuousAlternatingMap.add_apply] -- FIXME
  simp only [Pi.smul_apply, coe_smul]
  rw [domDomCongr_apply, wedge_product_def, ContinuousAlternatingMap.wedge_product_def,
    uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, wedge_product_def,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, ederiv,
    uncurryFin_apply]
  sorry

/- The graded Leibniz rule for the interior product of the wedge product -/
theorem iprod_wedge (ω : Ω^(m + 1)⟮E, F⟯) (τ : Ω^(n + 1)⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'')
    (v : E → E) :
      iprod (domDomCongr Fin.finAddFlipAssoc (ω ∧[f] τ)) v = ((iprod ω v) ∧[f] τ)
        + (-1 : ℝ)^m • (domDomCongr Fin.finAddFlipAssoc (ω ∧[f] (iprod τ v))) := by
  ext e x
  rw[_root_.add_apply]
  erw[ContinuousAlternatingMap.add_apply] -- FIXME
  simp only [Nat.add_eq, Pi.smul_apply, coe_smul]
  rw[wedge_product_def, domDomCongr_apply, wedge_product_def,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousAlternatingMap.wedge_product_def,
    uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, iprod_apply, curryFin_apply, domDomCongr_apply,
    wedge_product_def, ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply]
  sorry

/- Exterior derivative commutes with pullback -/
theorem pullback_ederiv (f : E → F) (ω : Ω^n⟮F, G⟯) {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hω : DifferentiableAt ℝ ω (f x)) :
    pullback f (ederiv ω) x = ederiv (pullback f ω) x := by
  ext v
  rw[pullback, ederiv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    uncurryFin_apply, ederiv, uncurryFin_apply]
  apply Finset.sum_congr rfl
  intro p q
  refine Mathlib.Tactic.LinearCombination.smul_const_eq ?H.p ((-1) ^ (p : ℕ))
  simp only [Function.comp_apply]
  rw [← ContinuousLinearMap.comp_apply, ← fderiv_comp x hω (hf.differentiableAt (by simp))]
  simp +unfoldPartialApp only [pullback]
  rw[fderiv_apply, fderiv_apply]
  · simp only [Function.comp_apply, compContinuousLinearMap_apply]
    refine DFunLike.congr ?H.p.h₁ rfl
    have : p.removeNth (⇑(fderiv ℝ f x) ∘ v) = (fderiv ℝ f x) ∘ p.removeNth v :=
    rfl
    rw[this]
    apply EventuallyEq.fderiv_eq
    refine EventuallyEq.comp₂ (Eq.eventuallyEq rfl) DFunLike.coe ?h1
    refine EventuallyEq.comp₂ ?h2 Function.comp (Eq.eventuallyEq rfl)
    refine EventuallyEq.comp₂ (Eq.eventuallyEq rfl) (@DFunLike.coe (E →L[ℝ] F) E fun x ↦ F) ?h2.Hg
  -- Differentiability conditions
    sorry
  · sorry
  · exact DifferentiableAt.comp x hω (hf.differentiableAt (by simp))

end DifferentialForm

noncomputable section

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {m n : ℕ} {k l : ℕ∞}

-- Setup for Differential Form Space
notation "Ω^" k "," m "⟮" EM "," IM "," M "⟯" =>
  ContMDiffSection IM (EM [⋀^Fin m]→L[ℝ] ℝ) k
    (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM : M → Type _) ℝ
      (Bundle.Trivial M ℝ))

namespace DifferentialForm

section mpullback

variable
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  (IN : ModelWithCorners ℝ EN HN)
  (N : Type*) [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ⊤ N]

variable (α β : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x)

/- The pullback of a differential form
Want to keep k-times differentiability away from it. Is this the way? -/
def mpullback (f : M → N) : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial N ℝ (f x) :=
    fun x ↦ (α (f x)).compContinuousLinearMap (mfderiv IM IN f x)

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_zero (f : M → N) :
    mpullback IM M IN N (0 : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x) f = 0 :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_add (f : M → N) :
    mpullback IM M IN N (α + β) f = mpullback IM M IN N α f + mpullback IM M IN N β f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_sub (f : M → N) :
    mpullback IM M IN N (α - β) f = mpullback IM M IN N α f - mpullback IM M IN N β f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_neg (f : M → N) :
    - mpullback IM M IN N α f = mpullback IM M IN N (-α) f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_smul (f : M → N) (c : ℝ) :
    c • (mpullback IM M IN N α) f = mpullback IM M IN N (c • α) f :=
  rfl

end mpullback

section miprod

variable [Π (x : M), NormedAddCommGroup (TangentSpace IM x)]

def miprod (α : Ω^k,(m + 1)⟮EM,IM,M⟯) (V : Π (x : M), TangentSpace IM x) :
    (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial M ℝ x := by
  intro x
  let triv_α := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local := (triv_α ⟨x, α x⟩).2
  let ip_local := ContinuousAlternatingMap.curryFin α_local (V x)
  let triv_ip := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  exact triv_ip.symm x ip_local

end miprod

section mwedge_product

--TODO: Create instances for these charted spaces
variable
  [Π (x : M), NormedAddCommGroup (TangentSpace IM x)]

/- Place for wedge product definitions -/
def mwedge_product (α : Ω^k,m⟮EM,IM,M⟯) (β : Ω^l,n⟮EM,IM,M⟯) :
    (x : M) → TangentSpace IM x [⋀^Fin (m + n)]→L[ℝ] Trivial M ℝ x := by
  intro x
  let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let triv_β := trivializationAt (EM [⋀^Fin n]→L[ℝ] ℝ) ⋀^Fin n⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local := (triv_α ⟨x, α x⟩).2
  let β_local := (triv_β ⟨x, β x⟩).2
  let wedge_local := ContinuousAlternatingMap.wedge_product α_local β_local (ContinuousLinearMap.mul ℝ ℝ)
  let triv_wedge := trivializationAt (EM [⋀^Fin (m + n)]→L[ℝ] ℝ) ⋀^Fin (m + n)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  exact triv_wedge.symm x wedge_local

end mwedge_product

section mederiv

variable (α : Ω^k,m⟮EM,IM,M⟯)

/- Definition of the manifold exterior derivative of differential form within a set -/
def mederivWithin (s : Set M) (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
  let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
  let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
  let dα_local := ederivWithin α_local s_local
  let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  triv_dα.symm x (dα_local (extChartAt IM x x))

lemma mederivWithin_def (s : Set M) :
  mederivWithin IM M α s = fun x ↦
    let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
    let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
    let dα_local := ederivWithin α_local s_local
    let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    triv_dα.symm x (dα_local (extChartAt IM x x)) :=
  rfl

lemma mederivWithin_apply (s : Set M) (x : M) :
  mederivWithin IM M α s x =
    let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
    let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
    let dα_local := ederivWithin α_local s_local
    let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    triv_dα.symm x (dα_local (extChartAt IM x x)) :=
  rfl

def mederiv (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
    mederivWithin IM M α univ x

lemma mederiv_def : mederiv IM M α = fun x ↦ mederiv IM M α x :=
  rfl

theorem mederivWithin_univ : mederivWithin IM M α univ = mederiv IM M α :=
  rfl

end mederiv

end DifferentialForm
