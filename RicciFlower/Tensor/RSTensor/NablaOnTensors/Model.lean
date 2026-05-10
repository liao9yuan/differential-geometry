import RicciFlower.Tensor.RSTensor.LieDerivative
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

/-!
# Model-space formulas for tensor covariant derivatives

This module contains the pure model-space definitions and component/evaluation lemmas used by
`TensorLieDeriv.nabla0SFun` and `TensorLieDeriv.nablaRSFun`.
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

/-!
## Implementation layer: model-space tensor formula

These definitions are the fixed-vector-space formulas used after trivializing
the tensor bundle in a chart.  They are deliberately lower-level than
`nabla0SFun` / `nablaRSFun`.
-/

/-- Pointwise model formula for the covariant derivative of a covariant tensor.

The input `dα_X` is the first-order derivative of the tensor components in the
direction `X`, while `ΓX` is the connection endomorphism acting on each input
slot. -/
def covariantDeriv_tensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDeriv_correction s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDeriv_correction s ΓX α := by
  rfl

/-- Model-space covariant derivative of a covariant tensor field.

This is the chart-level formula
`∇_X α = Dα(X) - Σᵢ α(..., Γ_X -, ...)`. -/
def covariantDeriv_tensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

/-- Within-set variant of `covariantDeriv_tensor0SModel`. -/
def covariantDeriv_tensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

theorem covariantDeriv_tensor0SModelAt_apply_slots {s : ℕ}
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α slots =
      dα_X slots -
        ∑ a : Fin s, α (Function.update slots a (ΓX (slots a))) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

theorem covariantDeriv_tensor0SModelWithin_apply_slots {s : ℕ}
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x slots =
      fderivWithin 𝕜 α u x (X x) slots -
        ∑ a : Fin s, α x (Function.update slots a (ΓX x (slots a))) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_slots (𝕜 := 𝕜) (E := E)
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots

/-- Product rule for evaluating a model `(0,s)` tensor on variable model slots
written as continuous linear maps from `𝕜` and then evaluated on fixed scalar
slots. This is the pure model-space calculus input behind the moving-slot
derivation formula. -/
theorem fderivWithin_tensor0SModel_eval_linear_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (L : Fin s → E → 𝕜 →L[𝕜] E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (c : Fin s → 𝕜) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (c a))) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (c b)) a
            (fderivWithin 𝕜 (L a) u y Xy (c a))) := by
  classical
  let F : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => 𝕜) 𝕜 :=
    fun z => (α z).compContinuousLinearMap (fun a : Fin s => L a z)
  have hFdiff : DifferentiableWithinAt 𝕜 F u y := by
    exact hα.continuousMultilinearMapCompContinuousLinearMap hL
  have happly :=
    fderivWithin_continuousMultilinear_apply_const_apply
      (𝕜 := 𝕜) (s := u) (x := y) (c := F) hu hFdiff c Xy
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    (fderivWithin 𝕜 F u y) Xy c at happly
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun b : Fin s => L b y (c b)) a
          (fderivWithin 𝕜 (L a) u y Xy (c a)))
  rw [happly]
  have hF :=
    fderivWithin_continuousMultilinearMapCompContinuousLinearMap
      (𝕜 := 𝕜) (f := α) (g := L) (s := u) (x := y) hα hL hu
  rw [hF]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.add_apply]
  change
    ((fderivWithin 𝕜 α u y) Xy).compContinuousLinearMap
        (fun x : Fin s => L x y) c +
      (ContinuousMultilinearMap.fderivCompContinuousLinearMap (α y)
        (fun x : Fin s => L x y)
        (fun i : Fin s => (fderivWithin 𝕜 (L i) u y) Xy)) c =
    ((fderivWithin 𝕜 α u y) Xy) (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun a : Fin s => L a y (c a)) a
          (((fderivWithin 𝕜 (L a) u y) Xy) (c a)))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

/-- Product rule for evaluating a model `(0,s)` tensor on genuinely `E`-valued
variable model slots. -/
theorem fderivWithin_tensor0SModel_eval_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let one : 𝕜 →L[𝕜] 𝕜 := 1
  let A : E →L[𝕜] (𝕜 →L[𝕜] E) :=
    ContinuousLinearMap.smulRightL 𝕜 𝕜 E one
  let L : Fin s → E → 𝕜 →L[𝕜] E := fun a z => A (V a z)
  have hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y := by
    intro a
    exact A.differentiableWithinAt.comp y (hV a) (Set.mapsTo_univ _ _)
  have h := fderivWithin_tensor0SModel_eval_linear_slots
    (𝕜 := 𝕜) (E := E) (s := s) α L u y Xy hα hL hu (fun _ => (1 : 𝕜))
  have hderiv (a : Fin s) :
      ((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜) =
        fderivWithin 𝕜 (V a) u y Xy := by
    have hA :
        fderivWithin 𝕜 (L a) u y =
          A.comp (fderivWithin 𝕜 (V a) u y) := by
      have hcomp := A.hasFDerivAt.comp_hasFDerivWithinAt y (hV a).hasFDerivWithinAt
      simpa [L, Function.comp_def] using hcomp.fderivWithin hu
    rw [hA]
    simp [A, one, ContinuousLinearMap.smulRight_apply]
  calc
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy
        = fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (1 : 𝕜))) u y Xy := by
            simp [L, A, one, ContinuousLinearMap.smulRight_apply]
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (1 : 𝕜)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (1 : 𝕜)) a
            (((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜))) := h
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
            congr 1
            · congr
              funext a
              simp [L, A, one, ContinuousLinearMap.smulRight_apply]
            · refine Finset.sum_congr rfl fun a _ => ?_
              congr 1
              funext b
              by_cases hb : b = a
              · subst hb
                simpa using hderiv b
              · simp [Function.update, hb, L, A, one, ContinuousLinearMap.smulRight_apply]

/-- Pointwise model formula for the covariant derivative of a mixed `(r,s)` tensor.

In the `Hom((0,r),(0,s))` model the connection acts on output covariant slots
with a minus sign and on input covariant slots with a plus sign. For `r = 1`,
`s = 0`, this recovers the usual `D Y(X) + Γ_X Y` vector-field formula under
the vector-as-`Hom(V*, 𝕜)` identification. -/
def covariantDeriv_tensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

/-- Evaluation form of the model-space covariant derivative of an `(r,s)`
tensor.

In the `Hom((0,r),(0,s))` model, the connection correction subtracts from the
output covariant slots and adds through the input covariant slots. -/
theorem covariantDeriv_tensorRSModelAt_eval (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) r) (v : Fin s → E) :
    (covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T β) v =
      (dT_X β) v -
        ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX) (T β)) v +
        (T ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) β)) v := by
  simp [covariantDeriv_tensorRSModelAt, sub_eq_add_neg, add_assoc]

section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

/-- Matrix coefficient of a model connection endomorphism in a basis:
`Γ^k_j = e^k (Γ e_j)`. -/
def connectionEndomorphismCoeff
    (basis : Module.Basis Idx 𝕜 E) (ΓX : E →L[𝕜] E)
    (j k : Idx) : 𝕜 :=
  basis.coord k (ΓX (basis j))

private theorem tensor0SModel_eval_update_basis_sum {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Idx, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Idx, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Idx,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset Idx) i (fun k : Idx => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

private theorem tensor0SModel_one_eval_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1) (v : E) :
    α (fun _ : Fin 1 => v) =
      ∑ k : Idx, basis.coord k v * α (fun _ : Fin 1 => basis k) := by
  have hupdate (w : E) :
      Function.update (fun _ : Fin 1 => v) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have h := tensor0SModel_eval_update_basis_sum basis α
    (fun _ : Fin 1 => v) (0 : Fin 1) v
  simpa [hupdate] using h

private theorem tensor0SModel_two_eval_first_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k v *
        α (fun q : Fin 2 => if q = 0 then basis k else w) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (0 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then z else w := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (0 : Fin 2) v
  have hbase : Function.update base (0 : Fin 2) v = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

private theorem tensor0SModel_two_eval_second_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k w *
        α (fun q : Fin 2 => if q = 0 then v else basis k) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (1 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then v else z := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (1 : Fin 2) w
  have hbase : Function.update base (1 : Fin 2) w = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

/-- Model-space covariant derivative in Christoffel coordinates for arbitrary
covariant valence.

This is the recursive slot formula behind the one- and two-slot component
lemmas: evaluate on basis slots, then subtract the connection correction in
each slot. -/
theorem covariantDeriv_tensor0SModelAt_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α
        (fun a : Fin s => basis (slots a)) =
      dα_X (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis ΓX (slots a) k *
            α (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hslot :
      α (fun b : Fin s =>
          (if b = a then ΓX else ContinuousLinearMap.id 𝕜 E) (basis (slots b))) =
        α (Function.update (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))) := by
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [Function.update, hb]
  rw [hslot]
  exact tensor0SModel_eval_update_basis_sum basis α
    (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))

/-- Within-set variant of
`covariantDeriv_tensor0SModelAt_apply_basis_slots`. -/
theorem covariantDeriv_tensor0SModelWithin_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (u : Set E) (x : E) (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜 α u x (X x) (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX x) (slots a) k *
            α x (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_basis_slots (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots

/-- Model-space one-form covariant derivative in Christoffel coordinates:
`(∇_X α)_j = X(α_j) - Γ^k_j α_k`.

This is the algebraic core used by `nabla0SFun`; the remaining manifold-layer
work is identifying the model derivative and model connection coefficients
with the chosen local coordinate or local-frame component functions. -/
theorem covariantDeriv_tensor0SModelAt_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (j : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 1 dα_X ΓX α
        (fun _ : Fin 1 => basis j) =
      dα_X (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          α (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hcorr :
      α (fun i : Fin 1 =>
        (if i = 0 then ΓX else ContinuousLinearMap.id 𝕜 E) (basis j)) =
        α (fun _ : Fin 1 => ΓX (basis j)) := by
    congr 1
    funext q
    fin_cases q
    simp
  rw [hcorr]
  rw [tensor0SModel_one_eval_basis_sum basis α (ΓX (basis j))]

/-- Model-space `(0,2)` covariant derivative in Christoffel coordinates:
`(∇_X A)_{jl} = X(A_{jl}) - Γ^k_j A_{kl} - Γ^k_l A_{jk}`.

This is the two-slot algebraic core behind the usual tensor Christoffel formula. -/
theorem covariantDeriv_tensor0SModelAt_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dA_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (ΓX : E →L[𝕜] E)
    (A : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (j l : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 2 dA_X ΓX A
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      dA_X (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          A (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX l k *
          A (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hfin :
      (∑ i : Fin 2,
          A (fun j_1 : Fin 2 =>
            (if j_1 = i then ΓX else ContinuousLinearMap.id 𝕜 E)
              ((fun q : Fin 2 => if q = 0 then basis j else basis l) j_1))) =
        A (fun q : Fin 2 => if q = 0 then ΓX (basis j) else basis l) +
          A (fun q : Fin 2 => if q = 0 then basis j else ΓX (basis l)) := by
    rw [Fin.sum_univ_two]
    congr 1
    · congr 1
      funext q
      fin_cases q <;> simp
    · congr 1
      funext q
      fin_cases q <;> simp
  rw [hfin]
  rw [tensor0SModel_two_eval_first_basis_sum basis A (ΓX (basis j)) (basis l)]
  rw [tensor0SModel_two_eval_second_basis_sum basis A (basis j) (ΓX (basis l))]
  abel

/-- Within-set variant of the one-form Christoffel component formula. -/
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) j

/-- Within-set variant of the `(0,2)` Christoffel component formula. -/
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 A u x (X x)) (ΓX x) (A x) j l

/-- Raw-`ContinuousMultilinearMap` version of the within-set one-form formula.

This is the same component identity as
`covariantDeriv_tensor0SModelWithin_one_apply_basis`, but its derivative term
has a raw continuous-multilinear-map codomain. This avoids exposing
`Tensor0SModel` alias instance elaboration to coordinate-facing files. -/
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => E) 𝕜)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  exact covariantDeriv_tensor0SModelWithin_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX α u x j

/-- Raw-`ContinuousMultilinearMap` version of the within-set `(0,2)` formula. -/
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) 𝕜)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  exact covariantDeriv_tensor0SModelWithin_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX A u x j l

end ChristoffelModel

/-- Model-space covariant derivative of a mixed `(r,s)` tensor field. -/
def covariantDeriv_tensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

/-- Within-set variant of `covariantDeriv_tensorRSModel`. -/
def covariantDeriv_tensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

/-- Smoothness of the fixed-set model covariant derivative of a covariant tensor.

This is the model-space calculus component of the regularity proof: if the
tensor components have one more derivative than the output target, and the
direction field and connection endomorphism are smooth to the target order,
then `Dα(X) - C(ΓX) α` is smooth to the target order. -/
theorem contDiffWithinAt_covariantDeriv_tensor0SModelWithin (s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hα : ContDiffWithinAt 𝕜 n' α u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
        s X ΓX α u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 α u y (X y)) u x :=
    hα.fderivWithin_right_apply hX hu hmn hx
  have hα_m : ContDiffWithinAt 𝕜 m α u x :=
    hα.of_le (le_trans le_self_add hmn)
  have hCorrOp :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) s)
  have hCorr :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correction (𝕜 := 𝕜) (E := E) s (ΓX y) (α y)) u x := by
    simpa [lieDeriv_correctionL] using hCorrOp.clm_apply hα_m
  simpa [covariantDeriv_tensor0SModelWithin, covariantDeriv_tensor0SModelAt] using
    hprincipal.sub hCorr

/-- Smoothness of the fixed-set model covariant derivative of a mixed tensor.

This is the mixed-tensor analogue of
`contDiffWithinAt_covariantDeriv_tensor0SModelWithin`: the principal term is
`DT(X)`, the output covariant slots are corrected by precomposition with
`C_s(ΓX)`, and the input covariant slots by postcomposition with `C_r(ΓX)`. -/
theorem contDiffWithinAt_covariantDeriv_tensorRSModelWithin (r s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {T : E → TensorRSModel r s 𝕜 E}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 T u y (X y)) u x :=
    hT.fderivWithin_right_apply hX hu hmn hx
  have hT_m : ContDiffWithinAt 𝕜 m T u x :=
    hT.of_le (le_trans le_self_add hmn)
  have hCorrS :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) s)
  have hCorrR :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) r)
  have hOut :
      ContDiffWithinAt 𝕜 m
        (fun y => (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)).comp (T y)) u x :=
    hCorrS.clm_comp hT_m
  have hIn :
      ContDiffWithinAt 𝕜 m
        (fun y => (T y).comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y))) u x :=
    hT_m.clm_comp hCorrR
  simpa [covariantDeriv_tensorRSModelWithin, covariantDeriv_tensorRSModelAt] using
    (hprincipal.sub hOut).add hIn

/- Reusable slot-correction Leibniz rule for the covariant tensor product.

This is the same algebra proved for Lie derivatives; the only semantic change
is that `ΓX` is read as the connection endomorphism in the `X` direction. -/
omit [CompleteSpace 𝕜] in
lemma covariantSlotCorrection_modelProduct (s q : ℕ) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDeriv_correction (s + q) ΓX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDeriv_correction s ΓX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDeriv_correction q ΓX β) :=
  lieDeriv_correction_modelProduct (𝕜 := 𝕜) (E := E) s q ΓX α β

end ModelCovariantDerivative

end

end TensorLieDeriv
