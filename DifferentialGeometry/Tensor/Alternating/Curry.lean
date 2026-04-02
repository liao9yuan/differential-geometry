/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases

/-!
# Currying and uncurrying continuous alternating maps

This file constructs currying and uncurrying operations for continuous alternating maps,
which are the building blocks for defining the wedge product.

## Main definitions

* `ContinuousAlternatingMap.uncurryFin`: given `f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F`, produces
  `E [⋀^Fin (n+1)]→L[𝕜] F` by antisymmetrization: `uncurryFin f v = ∑ k, (-1)^k • f (v k) (k.removeNth v)`.
* `ContinuousAlternatingMap.uncurryFinCLM`: the continuous linear map version of `uncurryFin`.
* `ContinuousAlternatingMap.curryFin`: the interior product (contraction), sending
  `f : E [⋀^Fin (n+1)]→L[𝕜] F` to `E →L[𝕜] E [⋀^Fin n]→L[𝕜] F` by fixing the first argument.
* `ContinuousAlternatingMap.uncurrySum`: given `f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F`, produces
  `E [⋀^ι ⊕ ι']→L[𝕜] F` by summing over shuffle permutations in `Equiv.Perm.ModSumCongr ι ι'`.
* `ContinuousAlternatingMap.uncurryFinAdd`: the `Fin (m + n)` version of `uncurrySum`.

## Main results

* `ContinuousAlternatingMap.norm_uncurryFin_le`: the norm bound `‖uncurryFin f‖ ≤ (n+1) * ‖f‖`.
* `ContinuousAlternatingMap.uncurryFin_uncurryFinCLM_comp_of_symmetric`: if
  `f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F` is symmetric in its two `E` arguments, then
  `uncurryFin (uncurryFinCLM.comp f) = 0`.
* `ContinuousAlternatingMap.lift_comp_domCoprod_eq_uncurrySum`: the tensor product lift of a
  bilinear map composed with `AlternatingMap.domCoprod` equals `uncurrySum` of the composition.
-/

namespace ContinuousAlternatingMap

noncomputable section curry

variable {𝕜 E F G ι ι' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [Fintype ι] [Fintype ι']
  {m n : ℕ}

/-- Given `f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F`, produce the continuous alternating `(n+1)`-form
`uncurryFin f : E [⋀^Fin (n+1)]→L[𝕜] F` by antisymmetrization:
`uncurryFin f v = ∑ k, (-1)^k • f (v k) (k.removeNth v)`.
The norm satisfies `‖uncurryFin f‖ ≤ (n+1) * ‖f‖`. See `norm_uncurryFin_le`. -/
def uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuous (.alternatizeUncurryFin <| toAlternatingMapLinear ∘ₗ f)
    ((n + 1) * ‖f‖) fun v ↦ calc
      _ = ‖∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)‖ := by
        simp [AlternatingMap.alternatizeUncurryFin_apply]
      _ ≤ ∑ k, ‖f‖ * ‖v k‖ * ∏ j, ‖v (k.succAbove j)‖ := by
        refine norm_sum_le_of_le _ fun k _ ↦ ?_
        rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]
        exact (f (v k)).le_of_opNorm_le (f.le_opNorm _) _
      _ = _ := by
        simp [mul_assoc, ← Fin.prod_univ_succAbove (‖v ·‖)]

/-- The underlying alternating map of `uncurryFin f` is `alternatizeUncurryFin` applied to
`toAlternatingMapLinear ∘ₗ f`. -/
lemma toAlternatingMap_uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (uncurryFin f).toAlternatingMap = .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ f) :=
  rfl

/-- Norm bound for `uncurryFin`: `‖uncurryFin f‖ ≤ (n + 1) * ‖f‖`. -/
theorem norm_uncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖uncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  AlternatingMap.mkContinuous_norm_le _ (by positivity) _

/-- Evaluation formula for `uncurryFin`:
`uncurryFin f v = ∑ k, (-1)^k • f (v k) (k.removeNth v)`. -/
theorem uncurryFin_apply (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v) :=
  AlternatingMap.alternatizeUncurryFin_apply ..

/-- `uncurryFin` is additive in `f`. -/
theorem uncurryFin_add (f g : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g := by
  ext v
  simp [uncurryFin_apply, Finset.sum_add_distrib]

/-- `uncurryFin` commutes with scalar multiplication. -/
theorem uncurryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    uncurryFin (c • f) = c • uncurryFin f := by
  ext v
  simp [uncurryFin_apply, smul_comm _ c, Finset.smul_sum]

/-- `uncurryFin` as a continuous linear map
`(E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n+1)]→L[𝕜] F`.
The operator norm is bounded by `n + 1`. -/
@[simps! apply]
def uncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := uncurryFin (𝕜 := 𝕜) (E := E) (F := F) (n := n)
      map_add' := by exact uncurryFin_add -- TODO: why does it fail without `by exact`?
      map_smul' := by exact uncurryFin_smul }
    (n + 1) norm_uncurryFin_le

/-- If `f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F` is symmetric in its two `E` arguments
(i.e. `f x y = f y x`), then `uncurryFin (uncurryFinCLM.comp f) = 0`.
Intuitively, applying the antisymmetrization `uncurryFin` twice with a symmetric inner map
annihilates the result. -/
theorem uncurryFin_uncurryFinCLM_comp_of_symmetric {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinCLM.comp f) = 0 := by
  let g := LinearMap.compr₂ f.toLinearMap₁₂ toAlternatingMapLinear
  have g_symm : ∀ x y, g x y = g y x := by
    intro x y
    have : g x y = (f x y).toAlternatingMap := rfl
    aesop
  let h₀ := AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric (g_symm)
  exact toAlternatingMap_injective h₀

/-- The interior product (contraction): given `f : E [⋀^Fin (n+1)]→L[𝕜] F`, produce the
continuous linear map `E →L[𝕜] E [⋀^Fin n]→L[𝕜] F` that fixes `x : E` as the first argument
of `f`, i.e. `curryFin f x m = f (Fin.cons x m)`.
The operator norm satisfies `‖curryFin f‖ ≤ ‖f‖`. -/
def curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  have f_curry_bounded (x : E) : ∀ (m : Fin n → E), ‖(f.curryLeft x) m‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖
    := by
    intro m
    let m' : Fin (n + 1) → E := Fin.cons x m
    have h₀ : (f.curryLeft x) m = f m' := rfl
    rw [h₀]
    let m_norm : Fin n → ℝ := fun i => ‖m i‖
    let m_norm' : Fin (n + 1) → ℝ := Fin.cons (‖x‖) m_norm
    have h₁ : ∏ i, ‖m' i‖ = ‖x‖ * ∏ i, ‖m i‖ := by
      have aux := Fin.prod_cons (‖x‖) m_norm
      unfold m_norm at aux
      have : ∀ i, ‖m' i‖ = m_norm' i := by
        apply Fin.induction
        · simp [Fin.cons_zero, m', m_norm']
        · intro i _
          simp [Fin.cons_succ, m', m_norm', m_norm]
      rw [← aux]
      simp [this, m_norm', Fin.prod_cons, m_norm]
    rw [mul_assoc, ←h₁]
    exact f.le_opNorm m'
  let f_curry (x : E) := (f.1.curryLeft x).mkContinuous (‖f‖ * ‖x‖) (f_curry_bounded x)
  LinearMap.mkContinuous
    { toFun := fun x =>
        { toContinuousMultilinearMap := f_curry x
          map_eq_zero_of_eq' := fun v i j hv hne ↦ by
            apply f.map_eq_zero_of_eq (Fin.cons x v) (i := i.succ) (j := j.succ) <;> simpa }
      map_add' := fun x y => by unfold f_curry; ext; simp
      map_smul' := fun c x => by unfold f_curry; ext; simp }
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, ← norm_toContinuousMultilinearMap]
      dsimp
      apply (ContinuousMultilinearMap.opNorm_le_iff _).mpr
      · intro m
        have : (f_curry x) m = (f.curryLeft x) m := rfl
        rw [this]
        exact f_curry_bounded x m
      · positivity


/-- Evaluation formula for `curryFin`: `curryFin f x m = f (Fin.cons x m)`. -/
theorem curryFin_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (m : Fin n → E) :
    curryFin f x m = f (Fin.cons x m) :=
  rfl

/-- `curryFin` is additive in `f`. -/
theorem curryFin_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (f + g) = curryFin f + curryFin g := by
  ext e v
  simp [curryFin_apply]

/-- `curryFin` commutes with scalar multiplication. -/
theorem curryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (c • f) = c • curryFin f := by
  ext e v
  simp [curryFin_apply]

variable [DecidableEq ι] [DecidableEq ι']

/-- A single summand in `uncurrySum`. For each coset `σ ∈ Equiv.Perm.ModSumCongr ι ι'`
(permutations of `ι ⊕ ι'` modulo block-permutations of `ι` and `ι'` separately), this is the
signed, permuted, uncurried multilinear map `sign(σ) • (f uncurried) ∘ σ`.
Well-definedness on the quotient follows because block-permutations act by the sign of their
components, which cancels the effect on `f`. -/
def uncurrySum.summand (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm.ModSumCongr ι ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => E) F :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (ContinuousMultilinearMap.uncurrySum
          (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
            : ContinuousMultilinearMap 𝕜 (fun _ => E) (F)).domDomCongr σ)
    fun σ₁ σ₂ H => by
      rw [QuotientGroup.leftRel_apply] at H
      obtain ⟨⟨sl, sr⟩, h⟩ := H
      ext v
      simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
        ContinuousMultilinearMap.uncurrySum_apply]
      replace h := inv_mul_eq_iff_eq_mul.mp h.symm
      have : Equiv.Perm.sign (σ₁ * Equiv.Perm.sumCongrHom _ _ (sl, sr))
        = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
      rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, smul_comm]
      simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.sumCongr_apply]
      erw [← (f.flipAlternating
        ((fun i ↦ v (σ₁ (Sum.map (⇑sl) (⇑sr) i))) ∘ Sum.inr)).map_congr_perm fun i => v (σ₁ _)]
      simp only [AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe,
        coe_toContinuousMultilinearMap]
      erw [← (f fun i ↦ v (σ₁ (Sum.inl i))).map_congr_perm fun i => v (σ₁ _)]
      simp [ContinuousMultilinearMap.flipAlternating]
      rfl

/-- Evaluation of `uncurrySum.summand f` at the coset represented by `σ` via `Quot.mk`. -/
theorem uncurrySum.summand_mk (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quot.mk
    (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom ι ι').range)) σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
  rfl

/-- Evaluation of `uncurrySum.summand f` at the coset represented by `σ` via `Quotient.mk''`. -/
theorem uncurrySum.summand_mk'' (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quotient.mk'' σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
  rfl

/-- If `v i = v j` and `i ≠ j`, then a summand and its image under swapping cancel:
`uncurrySum.summand f σ v + uncurrySum.summand f (Equiv.swap i j • σ) v = 0`.
This is the key cancellation used by `Finset.sum_involution` in the proof that `uncurrySum f`
is alternating. -/
theorem uncurrySum.summand_add_swap_smul_eq_zero (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    uncurrySum.summand f σ v + uncurrySum.summand f (Equiv.swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    uncurrySum.summand]
  rw [smul_eq_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Equiv.Perm.coe_mul,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.neg_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply]
  convert add_neg_cancel (G := F) _ using 6 <;>
    · ext k
      simp [Function.comp_apply, Function.comp_apply, Equiv.apply_swap_eq_self hv]

/-- If `v i = v j`, `i ≠ j`, and `Equiv.swap i j • σ = σ` in `Equiv.Perm.ModSumCongr ι ι'`,
then `uncurrySum.summand f σ v = 0`. Together with `summand_add_swap_smul_eq_zero`, this is
used in `Finset.sum_involution` to prove that `uncurrySum f` is alternating. -/
theorem uncurrySum.summand_eq_zero_of_smul_invariant (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    Equiv.swap i j • σ = σ → uncurrySum.summand f σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply,
    uncurrySum.summand]
  intro hσ
  -- TODO: Remove use of `cases'` tactic
  cases' hi : σ⁻¹ i with val val <;> cases' hj : σ⁻¹ j with val_1 val_1 <;>
    rw [Equiv.Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj <;> revert val val_1
  -- the term pairs with and cancels another term
  case inl.inr =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv,
      inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inl =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv,
      inv_mul_cancel_right] at hσ
    simp at hσ
  -- the term does not pair but is zero
  case inr.inr =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := F) _
    exact ContinuousAlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inl.inl =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := F) _
    simp only [ContinuousMultilinearMap.flipMultilinear, coe_toContinuousMultilinearMap,
    MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk]
    exact ContinuousAlternatingMap.map_eq_zero_of_eq (
      (f.flipAlternating ((fun i ↦ v (σ i)) ∘ Sum.inr))) _ hv fun hij' => hij (hij' ▸ rfl)

/-- Given `f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F`, produce the continuous alternating map
`uncurrySum f : E [⋀^ι ⊕ ι']→L[𝕜] F` by summing signed permuted uncurried maps over cosets
in `Equiv.Perm.ModSumCongr ι ι'` (shuffle permutations). The alternating property follows
from `summand_add_swap_smul_eq_zero` and `summand_eq_zero_of_smul_invariant` via
`Finset.sum_involution`. -/
def uncurrySum (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) : E [⋀^ι ⊕ ι']→L[𝕜] F :=
    { ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ with
    toFun := fun v => (⇑(∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [ContinuousMultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => uncurrySum.summand_add_swap_smul_eq_zero f σ hv hij)
          (fun σ _ => mt <| uncurrySum.summand_eq_zero_of_smul_invariant f σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

/-- The underlying continuous multilinear map of `uncurrySum f` is the sum of the summands. -/
theorem uncurrySum_coe (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) :
    ((uncurrySum f).toContinuousMultilinearMap : ContinuousMultilinearMap 𝕜 (fun _ => E) F) =
      ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ :=
  ContinuousMultilinearMap.ext fun _ => rfl

/-- Evaluation formula for `uncurrySum`. -/
theorem uncurrySum_apply (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (m : ι ⊕ ι' → E) :
    uncurrySum f m = (∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ) m :=
  rfl

/-- The `Fin (m + n)` version of `uncurrySum`: given `f : E [⋀^Fin m]→L[𝕜] E [⋀^Fin n]→L[𝕜] F`,
produce `E [⋀^Fin (m + n)]→L[𝕜] F` by applying `uncurrySum` and rearranging the domain along
`finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)`. -/
def uncurryFinAdd (f : E [⋀^Fin m]→L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (m + n)]→L[𝕜] F :=
  ContinuousAlternatingMap.domDomCongr finSumFinEquiv (uncurrySum f)

variable [DecidableEq ι] [DecidableEq ι']

open scoped TensorProduct

/-- Composing `TensorProduct.lift` of a bilinear map `f` with `AlternatingMap.domCoprod`
gives `uncurrySum` of `f.compContinuousAlternatingMap₂ g h`. -/
theorem lift_comp_domCoprod_eq_uncurrySum
    {N N' N'' : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
    (g : E [⋀^Fin m]→L[𝕜] N) (h : E [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (φ : N ⊗[𝕜] N' →ₗ[𝕜] N'') (hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b) :
    φ.compAlternatingMap (g.toAlternatingMap.domCoprod h.toAlternatingMap) =
      (uncurrySum (f.compContinuousAlternatingMap₂ g h)).toAlternatingMap := by
  ext w; simp only [LinearMap.compAlternatingMap_apply, coe_toAlternatingMap]
  change φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) w) =
    (uncurrySum (f.compContinuousAlternatingMap₂ g h)) w
  rw [uncurrySum_apply, ContinuousMultilinearMap.sum_apply,
    AlternatingMap.domCoprod_apply, MultilinearMap.sum_apply, _root_.map_sum φ]
  apply Finset.sum_congr rfl; intro q _
  induction q using Quotient.inductionOn' with | h σ =>
  simp only [AlternatingMap.domCoprod.summand_mk'', uncurrySum.summand_mk'',
    MultilinearMap.smul_apply, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, TensorProduct.smul_tmul', hφ,
    Function.comp_def, f.map_smul_of_tower, ContinuousLinearMap.smul_apply]; rfl

end curry
end ContinuousAlternatingMap
