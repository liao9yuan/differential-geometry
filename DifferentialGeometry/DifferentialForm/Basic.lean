/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.DifferentialForm.Defs
import DifferentialGeometry.DifferentialForm.Congr
import DifferentialGeometry.DifferentialForm.Rough
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
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

/- Smooth differential form counterparts of the exterior derivative theorems above -/
namespace DifferentialForm

variable {n m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness implies differentiability everywhere. -/
theorem differentiableAt (ω : DifferentialForm n E F) (x : E) :
    DifferentiableAt ℝ ω x :=
  (ω.smooth.differentiable (by norm_cast)).differentiableAt

variable {n m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exterior derivative of a smooth differential form. The result is again smooth. -/
def ederiv (ω : Ω^n⟮E, F⟯) : Ω^(n + 1)⟮E, F⟯ where
  toFun := _root_.ederiv ω.toFun
  smooth := by
    show ContDiff ℝ ⊤ (uncurryFinCLM ∘ fderiv ℝ ω.toFun)
    exact uncurryFinCLM.contDiff.comp (ω.smooth.fderiv_right le_top)

@[simp]
theorem ederiv_toFun (ω : Ω^n⟮E, F⟯) :
    (ederiv ω).toFun = _root_.ederiv ω.toFun := rfl

theorem ederiv_add (ω₁ ω₂ : Ω^n⟮E, F⟯) {x : E} :
    ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x :=
  _root_.ederiv_add ω₁.toFun ω₂.toFun (ω₁.differentiableAt x) (ω₂.differentiableAt x)

theorem ederiv_smul (c : ℝ) (ω : Ω^n⟮E, F⟯) {x : E} :
    ederiv (c • ω) x = c • ederiv ω x :=
  _root_.ederiv_smul ω.toFun c (ω.differentiableAt x)

theorem ederiv_apply (ω : Ω^n⟮E, F⟯) {x : E} (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω.toFun · (i.removeNth v)) x (v i) :=
  _root_.ederiv_apply ω.toFun (ω.differentiableAt x) v

/-- d² = 0 for smooth differential forms. -/
theorem ederiv_ederiv (ω : Ω^n⟮E, F⟯) : ederiv (ederiv ω) = 0 :=
  ext fun x => _root_.ederiv_ederiv_apply ω.toFun (ω.smooth.contDiffAt.of_le le_top)

end DifferentialForm

/-- Interior product of smooth differential forms. -/
noncomputable def iprod (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) (hv : ContDiff ℝ ⊤ v) : Ω^m⟮E, F⟯ where
  toFun := fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)
  smooth := by
    -- curryFin is a bounded linear map, so curryFin ∘ ω is smooth; then apply to v
    have hbl : IsBoundedLinearMap ℝ (curryFin (𝕜 := ℝ) (E := E) (F := F) (n := m)) :=
      ⟨⟨curryFin_add, fun c f => curryFin_smul c f⟩, 1, one_pos, fun g => by
        simp only [one_mul]
        exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x =>
          ContinuousAlternatingMap.opNorm_le_bound _
            (mul_nonneg (norm_nonneg g) (norm_nonneg x)) fun w => by
              rw [curryFin_apply]; have h := g.le_opNorm (Fin.cons x w)
              simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
              rw [← mul_assoc] at h; exact h⟩
    exact (hbl.contDiff.comp ω.smooth).clm_apply hv

@[simp]
theorem iprod_apply (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) (hv : ContDiff ℝ ⊤ v) (e : E) :
    iprod ω v hv e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

/-- The wedge product of smooth differential forms. -/
noncomputable def DifferentialForm.wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') : Ω^(m+n)⟮E, F''⟯ where
  toFun := fun x => ω.toFun x ∧[f] τ.toFun x
  smooth := by
    have hω : ContDiff ℝ ⊤ ω.toFun := ω.smooth
    have hτ : ContDiff ℝ ⊤ τ.toFun := τ.smooth
    let wedgeL := ContinuousAlternatingMap.wedge_productL
      (M := E) (m := m) (n := n) f
    change ContDiff ℝ ⊤ (fun x => wedgeL (ω.toFun x) (τ.toFun x))
    exact (wedgeL.contDiff.comp hω).clm_apply hτ

-- TODO: change notation
notation ω₁ " ∧["f"] " ω₂ => DifferentialForm.wedge ω₁ ω₂ f
notation ω₁ " ∧ " ω₂ => DifferentialForm.wedge ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

/-- The exterior derivative of a finite sum is the sum of the exterior derivatives. -/
theorem _root_.ederiv_finset_sum {ι : Type*} {s : Finset ι}
    (ω : ι → (E → E [⋀^Fin n]→L[ℝ] F)) {x : E}
    (hω : ∀ i ∈ s, DifferentiableAt ℝ (ω i) x) :
    _root_.ederiv (∑ i ∈ s, ω i) x = ∑ i ∈ s, _root_.ederiv (ω i) x := by
  change ContinuousAlternatingMap.uncurryFinCLM (fderiv ℝ (∑ i ∈ s, ω i) x) =
    ∑ i ∈ s, ContinuousAlternatingMap.uncurryFinCLM (fderiv ℝ (ω i) x)
  rw [fderiv_sum hω, _root_.map_sum]

/-- Pointwise basis expansion for a smooth differential form: at each point `y`,
`ω y = ∑ I, basisG.equivFun (ω y) I • basisG I`. -/
theorem basis_expansion [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (basisG : Module.Basis ι ℝ (E [⋀^Fin m]→L[ℝ] ℝ))
    (ω : Ω^m⟮E, ℝ⟯) (y : E) :
    ω y = ∑ I, basisG.equivFun (ω y) I • basisG I :=
  (basisG.sum_equivFun (ω y)).symm

/-- Leibniz rule for the exterior derivative of a product of scalar functions times a
constant alternating form. For smooth `a, b : E → ℝ` and constant `e : Alt^k`:
`fderiv (a · b) y = fderiv a y · b y + a y · fderiv b y`
This is `HasFDerivAt.mul` from Mathlib, restated at the `fderiv` level. -/
theorem fderiv_mul_scalar (a b : E → ℝ) (y : E)
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) :
    fderiv ℝ (fun z ↦ a z * b z) y =
      a y • fderiv ℝ b y + b y • fderiv ℝ a y :=
  (ha.hasFDerivAt.mul hb.hasFDerivAt).fderiv

/-- Smoothness of the coefficients of a smooth differential form in any basis of the
alternating-map space. Given a basis `basisG` for `E [⋀^Fin m]→L[ℝ] ℝ`, the coefficient
functions `fun y ↦ basisG.equivFunL (ω y) I` are smooth. -/
theorem contDiff_basis_coeff [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (basisG : Module.Basis ι ℝ (E [⋀^Fin m]→L[ℝ] ℝ))
    (ω : Ω^m⟮E, ℝ⟯) (I : ι) :
    ContDiff ℝ ⊤ (fun y ↦ basisG.equivFunL (ω y) I) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) I).comp
    basisG.equivFunL.toContinuousLinearMap).contDiff.comp ω.smooth

/-- Pointwise formula for the exterior derivative of a "scalar function times constant form".
For `a : E → ℝ` differentiable at `y` and a constant alternating `m`-form `e`, the
exterior derivative of `fun y ↦ a y • e` at `y` evaluated on `v : Fin (m+1) → E` is the
antisymmetrized sum
`∑ k, (-1)^k • (fderiv a y (v k)) • e (k.removeNth v)`.

This is the elementary "ederiv of a coefficient times a constant form" identity from which
the general Leibniz rule for `ederiv` of a wedge of scalar-valued forms follows by basis
expansion. -/
theorem _root_.ederiv_smul_const (a : E → ℝ) (e : E [⋀^Fin m]→L[ℝ] ℝ) (y : E)
    (ha : DifferentiableAt ℝ a y) (v : Fin (m + 1) → E) :
    _root_.ederiv (fun z ↦ a z • e) y v =
      ∑ k : Fin (m + 1), (-1 : ℤ) ^ k.val • (fderiv ℝ a y (v k)) • e (k.removeNth v) := by
  -- `(fun z ↦ a z • e)` has Frechet derivative `(fderiv a y).smulRight e` at `y`,
  -- since `e` is constant.
  have hd : HasFDerivAt (fun z ↦ a z • e) ((fderiv ℝ a y).smulRight e) y :=
    ha.hasFDerivAt.smul_const e
  -- Therefore `fderiv (fun z ↦ a z • e) y = (fderiv a y).smulRight e`.
  have hfderiv : fderiv ℝ (fun z ↦ a z • e) y = (fderiv ℝ a y).smulRight e := hd.fderiv
  -- `ederiv = uncurryFin ∘ fderiv`, then unfold via `uncurryFin_apply`.
  change ContinuousAlternatingMap.uncurryFin (fderiv ℝ (fun z ↦ a z • e) y) v = _
  rw [hfderiv, ContinuousAlternatingMap.uncurryFin_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- Each summand: `(-1)^k • ((fderiv a y).smulRight e) (v k) (k.removeNth v)`
  -- equals `(-1)^k • (fderiv a y (v k)) • e (k.removeNth v)`.
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply]

/-- The local exterior derivative used in this project agrees with Mathlib's `extDeriv`. -/
theorem _root_.ederiv_eq_extDeriv (ω : E → E [⋀^Fin n]→L[ℝ] F) (x : E) :
    _root_.ederiv ω x = extDeriv ω x := by
  change ContinuousAlternatingMap.uncurryFin (fderiv ℝ ω x) =
    ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ ω x)
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousAlternatingMap.toAlternatingMap_uncurryFin,
    ContinuousAlternatingMap.toAlternatingMap_alternatizeUncurryFin]

/-- Basis-expansion formula for the exterior derivative of a scalar-valued form.
Given a basis `B` of `E`, every alternating `n`-form expands uniquely as
`ω y = ∑_I ω_I(y) • elementaryCovector B.cDualBasis I`, where the sum ranges over
strictly increasing multi-indices `I : Fin n ↪o Fin d` and
`ω_I y := (elementaryCovectorBasis B).repr (ω y) I` is the coefficient function.

The classical textbook formula `d(∑_I ω_I • dx^I) = ∑_I dω_I ∧ dx^I` then reads:
the exterior derivative of `ω` is the sum over multi-indices `I` of the 1-form
`fderiv ω_I y` wedged with the constant `n`-form `elementaryCovector b I` via
`covectorWedge` (notation `∧₁`). -/
theorem _root_.ederiv_basis_expansion
    {d : ℕ} [FiniteDimensional ℝ E]
    (B : Module.Basis (Fin d) ℝ E)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) (y : E)
    (hω : DifferentiableAt ℝ ω y) :
    _root_.ederiv ω y =
      ∑ I : Fin n ↪o Fin d,
        fderiv ℝ (fun z => (elementaryCovectorBasis B).repr (ω z) I) y
          ∧₁ ContinuousAlternatingMap.elementaryCovector B.cDualBasis ↑I := by
  let basisG := elementaryCovectorBasis (k := n) B
  have hcoeff :
      ∀ I : Fin n ↪o Fin d,
        DifferentiableAt ℝ (fun z => basisG.repr (ω z) I) y := by
    intro I
    let coord : (E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↪o Fin d => ℝ) I).comp
        basisG.equivFunL.toContinuousLinearMap
    have hcoord : DifferentiableAt ℝ (fun z => coord (ω z)) y :=
      coord.differentiableAt.comp y hω
    simpa [coord, Module.Basis.equivFunL_apply] using hcoord
  have hω_expand :
      ω = fun z => ∑ I : Fin n ↪o Fin d, basisG.repr (ω z) I • basisG I := by
    funext z
    exact (basisG.sum_repr (ω z)).symm
  calc
    _root_.ederiv ω y =
        _root_.ederiv (fun z => ∑ I : Fin n ↪o Fin d,
          basisG.repr (ω z) I • basisG I) y := by
      exact congrArg (fun η => _root_.ederiv η y) hω_expand
    _ = ∑ I : Fin n ↪o Fin d,
        fderiv ℝ (fun z => basisG.repr (ω z) I) y
          ∧₁ ContinuousAlternatingMap.elementaryCovector B.cDualBasis ↑I := by
      have hsum_fun :
          (fun z => ∑ I : Fin n ↪o Fin d, basisG.repr (ω z) I • basisG I) =
            (∑ I : Fin n ↪o Fin d, fun z => basisG.repr (ω z) I • basisG I) := by
        funext z
        simp
      rw [hsum_fun]
      rw [_root_.ederiv_finset_sum
        (s := Finset.univ)
        (ω := fun I : Fin n ↪o Fin d => fun z => basisG.repr (ω z) I • basisG I)
        (x := y)]
      · refine Finset.sum_congr rfl fun I _ => ?_
        have hderiv :
            fderiv ℝ (fun z => basisG.repr (ω z) I • basisG I) y =
              (fderiv ℝ (fun z => basisG.repr (ω z) I) y).smulRight (basisG I) :=
          ((hcoeff I).hasFDerivAt.smul_const (basisG I)).fderiv
        change
          ContinuousAlternatingMap.uncurryFin
              (fderiv ℝ (fun z => basisG.repr (ω z) I • basisG I) y) =
            ContinuousAlternatingMap.covectorWedge
              (fderiv ℝ (fun z => basisG.repr (ω z) I) y)
              (ContinuousAlternatingMap.elementaryCovector B.cDualBasis ↑I)
        rw [hderiv]
        simp [basisG, ContinuousAlternatingMap.covectorWedge]
      · intro I _
        exact (hcoeff I).smul_const (basisG I)

/-- Leibniz rule for the exterior derivative of a wedge of scalar-valued differential forms.
This is the `f = mul ℝ ℝ` specialization of `ederiv_wedge`. The proof is via basis expansion
in the `elementaryCovectorBasis`, distributing `ederiv` and the wedge over the resulting
sums, and using the Leibniz rule for ordinary scalar products on the coefficients.

**Strategy** (basis expansion):
1. Pick a basis `B : Module.Basis (Fin d) ℝ E` of `E` and its dual `b`, then form
   `basisG := elementaryCovectorBasis B b dual` for `Alt^m` and similarly `basisH` for `Alt^n`.
2. Pointwise expand `ω y = ∑_I (basisG.repr (ω y) I) • elementaryCovector b I` and likewise
   for `τ`. The coefficients `(fun y ↦ basisG.repr (ω y) I) : E → ℝ` are smooth (composing
   the smooth `ω.toFun` with the continuous linear map `basisG.repr_I`).
3. Distribute the wedge product over the basis sums to get
   `(ω ∧ τ) y = ∑_{I,J} (a_I y · b_J y) • (e_I ∧ e_J)` where `a_I, b_J` are the smooth
   coefficients and `e_I ∧ e_J` is a constant alternating `(m+n)`-form.
4. Apply `ederiv_smul_const` to each summand: `ederiv ((a_I · b_J) • (e_I ∧ e_J)) y` is a
   sum of terms involving `fderiv (a_I · b_J) y`.
5. Apply the ordinary Leibniz rule for scalar products
   `fderiv (a_I · b_J) y = (fderiv a_I y) · b_J(y) + a_I(y) · (fderiv b_J y)`.
6. Reorganize the resulting double sum to match the RHS, using `ederiv_smul_const` again
   on `ederiv ω` and `ederiv τ`.

The reorganization in step 6 still involves a `(-1)^m` sign and a `domDomCongr
finAddFlipAssoc`, both arising from the order in which the new differentiation index appears
relative to the existing alternating-form indices. These match the corresponding pieces in
the theorem statement of `ederiv_wedge` for the scalar case. -/

theorem ederiv_wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ederiv (ω ∧[f] τ) : E → E [⋀^Fin (m+n+1)]→L[ℝ] F'') =
      fun x => (ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc (ContinuousAlternatingMap.wedge_product (ederiv ω.toFun x) (τ.toFun x) f) : E [⋀^Fin (m+n+1)]→L[ℝ] F'')
      + (ContinuousAlternatingMap.domDomCongr (Equiv.refl _) (((-1 : ℝ)^m) • (ContinuousAlternatingMap.wedge_product (ω.toFun x) (ederiv τ.toFun x) f)) : E [⋀^Fin (m+n+1)]→L[ℝ] F'') := by
  -- Strategy:
  -- (1) `(ω ∧[f] τ).toFun y = wedge_productL f (ω y) (τ y)`.
  -- (2) `ederiv g x = uncurryFin (fderiv g x)`.
  -- (3) `fderiv (wedge_productL f ∘ (ω, τ)) x` via `ContinuousLinearMap.fderiv_of_bilinear`
  --     splits as `(precompR f (ω x) (fderiv τ x)) + (precompL f (fderiv ω x) (τ x))`.
  -- (4) `uncurryFin` is linear, so the sum distributes.
  -- (5) The two helpers `uncurryFin_wedge_productL_precompL/R` in Wedge.lean identify each
  --     summand with the corresponding wedge of an `ederiv` factor.
  funext x
  change ContinuousAlternatingMap.uncurryFin
      (fderiv ℝ (DifferentialForm.wedge ω τ f).toFun x) = _
  have hΩ : (DifferentialForm.wedge ω τ f).toFun =
      fun y => ContinuousAlternatingMap.wedge_productL f (ω.toFun y) (τ.toFun y) := by
    funext y; rfl
  rw [hΩ]
  have hω : DifferentiableAt ℝ ω.toFun x := ω.differentiableAt x
  have hτ : DifferentiableAt ℝ τ.toFun x := τ.differentiableAt x
  rw [(ContinuousAlternatingMap.wedge_productL f).fderiv_of_bilinear hω hτ,
      ContinuousAlternatingMap.uncurryFin_add,
      ContinuousAlternatingMap.uncurryFin_wedge_productL_precompR,
      ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL]
  -- Goal: (-1)^m • wedge_product (ω x) (uncurryFin (fderiv τ x)) f
  --       + domDomCongr finAddFlipAssoc (wedge_product (uncurryFin (fderiv ω x)) (τ x) f)
  --     = domDomCongr finAddFlipAssoc (wedge_product (ederiv ω.toFun x) (τ x) f)
  --       + domDomCongr (Equiv.refl _) ((-1)^m • wedge_product (ω x) (ederiv τ.toFun x) f)
  -- `ederiv ω.toFun x = uncurryFin (fderiv ω.toFun x)` (definitionally) and
  -- `domDomCongr (Equiv.refl _)` is the identity, so this is just `add_comm`.
  change ((-1 : ℝ) ^ m • ContinuousAlternatingMap.wedge_product
          (ω.toFun x) (ContinuousAlternatingMap.uncurryFin (fderiv ℝ τ.toFun x)) f)
      + ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
          (ContinuousAlternatingMap.wedge_product
            (ContinuousAlternatingMap.uncurryFin (fderiv ℝ ω.toFun x)) (τ.toFun x) f) =
    ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
        (ContinuousAlternatingMap.wedge_product
          (ContinuousAlternatingMap.uncurryFin (fderiv ℝ ω.toFun x)) (τ.toFun x) f)
      + ((-1 : ℝ) ^ m • ContinuousAlternatingMap.wedge_product
          (ω.toFun x) (ContinuousAlternatingMap.uncurryFin (fderiv ℝ τ.toFun x)) f)
  exact add_comm _ _

/-- Scalar specialization of `ederiv_wedge` with `f = mul ℝ ℝ`. -/
theorem ederiv_wedge_mul (ω : Ω^m⟮E, ℝ⟯) (τ : Ω^n⟮E, ℝ⟯) :
    (ederiv (ω ∧ τ) : E → E [⋀^Fin (m + n + 1)]→L[ℝ] ℝ) =
      fun x => (ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
                  (ContinuousAlternatingMap.wedge_product (ederiv ω.toFun x) (τ.toFun x)
                    (ContinuousLinearMap.mul ℝ ℝ)) :
                  E [⋀^Fin (m + n + 1)]→L[ℝ] ℝ)
              + (ContinuousAlternatingMap.domDomCongr (Equiv.refl _)
                  ((-1 : ℝ) ^ m • ContinuousAlternatingMap.wedge_product (ω.toFun x)
                    (ederiv τ.toFun x) (ContinuousLinearMap.mul ℝ ℝ)) :
                  E [⋀^Fin (m + n + 1)]→L[ℝ] ℝ) :=
  ederiv_wedge ω τ (ContinuousLinearMap.mul ℝ ℝ)

/- The graded Leibniz rule for the interior product of the scalar wedge product. -/
theorem iprod_wedge [FiniteDimensional ℝ E]
    (ω : Ω^(m + 1)⟮E, ℝ⟯) (τ : Ω^(n + 1)⟮E, ℝ⟯)
    (v : E → E) (hv : ContDiff ℝ ⊤ v) :
      iprod (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧ τ)) v hv =
        ((iprod ω v hv) ∧ τ)
        + (-1 : ℝ)^(m + 1) •
          (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧ (iprod τ v hv))) := by
  ext e x
  simpa [iprod_apply, DifferentialForm.domDomCongr_apply, DifferentialForm.wedge,
    ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
    using congrArg (fun η : E [⋀^Fin (m + n + 1)]→L[ℝ] ℝ => η x)
      (ContinuousAlternatingMap.iprod_wedge_product_mul (ω e) (τ e) (v e))

namespace DifferentialForm

/-- Pullback of a smooth differential form under a smooth map. -/
noncomputable def pullback (f : E → F) (ω : Ω^k⟮F, G⟯)
    (h_smooth : ContDiff ℝ ⊤ (RoughDifferentialForm.pullback f ω.toFun)) : Ω^k⟮E, G⟯ where
  toFun := RoughDifferentialForm.pullback f ω.toFun
  smooth := h_smooth

@[simp]
theorem pullback_toFun (f : E → F) (ω : Ω^k⟮F, G⟯)
    (h_smooth : ContDiff ℝ ⊤ (RoughDifferentialForm.pullback f ω.toFun)) :
    (pullback f ω h_smooth).toFun = RoughDifferentialForm.pullback f ω.toFun := rfl

/- Exterior derivative commutes with pullback -/
theorem pullback_ederiv (f : E → F) (ω : Ω^n⟮F, G⟯)
    (h_pull : ContDiff ℝ ⊤ (RoughDifferentialForm.pullback f ω.toFun))
    (h_ederiv_pull : ContDiff ℝ ⊤ (RoughDifferentialForm.pullback f (ederiv ω).toFun))
    {x : E} (hf : ContDiffAt ℝ 2 f x) :
    pullback f (ederiv ω) h_ederiv_pull x = ederiv (pullback f ω h_pull) x := by
  have h := extDeriv_pullback
    (𝕜 := ℝ) (ω := ω.toFun) (f := f) (x := x)
    (hω := ω.differentiableAt (f x)) (hf := hf) (hr := by simp)
  change (_root_.ederiv ω.toFun (f x)).compContinuousLinearMap (fderiv ℝ f x) =
    _root_.ederiv (RoughDifferentialForm.pullback f ω.toFun) x
  rw [_root_.ederiv_eq_extDeriv, _root_.ederiv_eq_extDeriv]
  exact h.symm

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
