import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear
import DifferentialGeometry.Tensor.Multilinear.DomDomCongrSection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Naturality of the covariant derivative under slot reindexing

The directional covariant derivative `nabla0SFun` commutes with reindexing the
tensor slots by an equivalence `e : Fin s ≃ Fin s'`:

`∇_X (Z·e) (slots) = (∇_X Z) (slots ∘ e)`.

Lifted to the canonical total derivative, this says `∇(Z·e) = (∇Z)·(e.front)`
where `e.front : Fin (s+1) ≃ Fin (s'+1)` fixes the new leading derivative slot
and reindexes the rest by `e`.  This is what lets `∇ᵐ` pass through the
`domDomCongr` that appears in the second term of the tensor-product Leibniz rule,
so that `normSq0S` permutation-invariance applies to the inductive hypothesis.
-/

noncomputable section

namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace E] [IsManifold I ∞ M]

/-- The front-slot extension of `e : Fin s ≃ Fin s'` to `Fin (s+1) ≃ Fin (s'+1)`:
fixes the leading slot `0` and reindexes the remaining `s` slots by `e`. -/
def frontExtendEquiv {s s' : ℕ} (e : Fin s ≃ Fin s') : Fin (s + 1) ≃ Fin (s' + 1) :=
  (finSuccEquiv s).trans ((Equiv.optionCongr e).trans (finSuccEquiv s').symm)

@[simp] theorem frontExtendEquiv_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    frontExtendEquiv e 0 = 0 := by
  simp [frontExtendEquiv]

@[simp] theorem frontExtendEquiv_succ {s s' : ℕ} (e : Fin s ≃ Fin s') (i : Fin s) :
    frontExtendEquiv e i.succ = (e i).succ := by
  simp [frontExtendEquiv]

/-- Evaluating a `Fin.cons` tuple at a front-extended index reindexes the tail by
`e` (pointwise form, fires under binders). -/
@[simp] theorem cons_apply_frontExtendEquiv {s s' : ℕ} (e : Fin s ≃ Fin s')
    {α : Type*} (c : α) (g : Fin s' → α) (i : Fin (s + 1)) :
    (Fin.cons c g : Fin (s' + 1) → α) (frontExtendEquiv e i)
      = (Fin.cons c (g ∘ e) : Fin (s + 1) → α) i := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · subst h; rw [frontExtendEquiv_zero, Fin.cons_zero, Fin.cons_zero]
  · subst h; rw [frontExtendEquiv_succ, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]

/-- **Naturality of the directional covariant derivative under slot reindexing.**
`∇_X (Z · e) (slots) = (∇_X Z) (slots ∘ e)`. -/
theorem nabla0SFun_domDomCongr [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] {s s' : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s' -> TangentSpace I x) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s' cov X
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e Z) x) slots
      = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X Z x)
          (slots ∘ e) := by
  classical
  let V : Fin s' -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin s', V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  have h1 := nabla0SFun_eval_smooth_slots (I := I) cov X V
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e Z) x
  have h2 := nabla0SFun_eval_smooth_slots (I := I) cov X (fun a : Fin s => V (e a)) Z x
  rw [show slots = (fun a : Fin s' => V a x) from (funext hV).symm, h1,
    show ((fun a : Fin s' => V a x) ∘ e) = (fun a : Fin s => V (e a) x) from rfl, h2]
  refine congrArg₂ (· - ·) ?_ ?_
  · -- exterior-derivative terms
    congr 1
  · -- correction sums
    refine Fintype.sum_equiv e.symm _ _ ?_
    intro a
    rw [MultilinearSection.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    simp only [Function.comp_apply, Function.update_apply, Equiv.apply_symm_apply,
      Equiv.apply_eq_iff_eq_symm_apply]

/-- **Naturality of the total covariant derivative under slot reindexing.**
`∇(Z · e) = (∇Z) · (frontExtendEquiv e)`: the canonical covariant derivative
commutes with a slot reindexing (the new leading derivative slot is fixed). -/
theorem totalNabla0SFun_domDomCongr [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] {s s' : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s' cov
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e Z) x
      = ContinuousMultilinearMap.domDomCongr (frontExtendEquiv e)
          (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov Z x) := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s' + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s' => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons,
    totalNabla0SFun_apply_section, nabla0SFun_domDomCongr,
    ContinuousMultilinearMap.domDomCongr_apply]
  simp only [cons_apply_frontExtendEquiv]
  rw [totalNabla0SFun_apply_section]

end Tensor0SBundle
