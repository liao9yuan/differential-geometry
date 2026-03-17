/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.DifferentialForm.Defs
import DifferentialGeometry.Tensor.DifferentialForm.Congr
import DifferentialGeometry.Tensor.DifferentialForm.Rough
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
noncomputable def ederiv (ω : Ω^n⟮E, F⟯) : Ω^(n + 1)⟮E, F⟯ where
  toFun := _root_.ederiv ω.toFun
  smooth := by
    -- ederiv ω = uncurryFinCLM ∘ fderiv ℝ ω, and fderiv of a C∞ map is C∞
    sorry

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
noncomputable def iprod (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) : Ω^m⟮E, F⟯ where
  toFun := fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)
  smooth := sorry

@[simp]
theorem iprod_apply (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) (e : E) :
    iprod ω v e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

/- The graded Leibniz rule for the exterior derivative of the wedge product -/
noncomputable def DifferentialForm.wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') : Ω^(m+n)⟮E, F''⟯ where
  toFun := fun x => ω.toFun x ∧[f] τ.toFun x
  smooth := by
    -- Mathlib does not currently have ContDiff properties for ContinuousAlternatingMap wedge products
    sorry

-- TODO: change notation
notation ω₁ " ∧["f"] " ω₂ => DifferentialForm.wedge ω₁ ω₂ f
notation ω₁ " ∧ " ω₂ => DifferentialForm.wedge ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem ederiv_wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ederiv (ω ∧[f] τ) : E → E [⋀^Fin (m+n+1)]→L[ℝ] F'') =
      fun x => (ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc (ContinuousAlternatingMap.wedge_product (ederiv ω.toFun x) (τ.toFun x) f) : E [⋀^Fin (m+n+1)]→L[ℝ] F'')
      + (ContinuousAlternatingMap.domDomCongr (Equiv.refl _) (((-1 : ℝ)^m) • (ContinuousAlternatingMap.wedge_product (ω.toFun x) (ederiv τ.toFun x) f)) : E [⋀^Fin (m+n+1)]→L[ℝ] F'') := by
  ext x y
  /- rw[Pi.add_apply]
  erw[ContinuousAlternatingMap.add_apply] -- FIXME
  simp only [Pi.smul_apply, coe_smul]
  rw [domDomCongr_apply, wedge_product_def, ContinuousAlternatingMap.wedge_product_def,
    uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, wedge_product_def,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, ederiv,
    uncurryFin_apply] -/
  sorry

/- The graded Leibniz rule for the interior product of the wedge product -/
theorem iprod_wedge (ω : Ω^(m + 1)⟮E, F⟯) (τ : Ω^(n + 1)⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'')
    (v : E → E) :
      iprod (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧[f] τ)) v = ((iprod ω v) ∧[f] τ)
        + (-1 : ℝ)^m • (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧[f] (iprod τ v))) := by
  ext e x
  erw[DifferentialForm.add_apply, ContinuousAlternatingMap.add_apply] -- FIXME
  simp only [Nat.add_eq, iprod_apply, DifferentialForm.domDomCongr_apply, DifferentialForm.smul_apply, coe_smul]
  sorry

namespace DifferentialForm

/-- Pullback of a smooth differential form under a smooth map. -/
noncomputable def pullback (f : E → F) (ω : Ω^k⟮F, G⟯) : Ω^k⟮E, G⟯ where
  toFun := fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)
  smooth := by sorry

@[simp]
theorem pullback_toFun (f : E → F) (ω : Ω^k⟮F, G⟯) :
    (pullback f ω).toFun = RoughDifferentialForm.pullback f ω.toFun := rfl

/- Exterior derivative commutes with pullback -/
theorem pullback_ederiv (f : E → F) (ω : Ω^n⟮F, G⟯) {x : E} (hf : ContDiffAt ℝ 2 f x) :
    pullback f (ederiv ω) x = ederiv (pullback f ω) x := by
  /- ext v
  rw[pullback, ederiv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    uncurryFin_apply, ederiv, uncurryFin_apply]
  apply Finset.sum_congr rfl
  intro p q
  refine Mathlib.Tactic.LinearCombination.smul_const_eq ?H.p ((-1) ^ (p : ℕ))
  simp only [Function.comp_apply]
  have hω_diff : DifferentiableAt ℝ ω.toFun (f x) := ω.differentiableAt (f x)
  rw [← ContinuousLinearMap.comp_apply, ← fderiv_comp x hω_diff (hf.differentiableAt (by simp))]
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
  · exact DifferentiableAt.comp x hω_diff (hf.differentiableAt (by simp)) -/
  sorry

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
