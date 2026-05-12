import RicciFlower.Tensor.RSTensor.NablaOnTensors.Model.Tensor0S

/-!
# Model-space covariant derivative for mixed tensors
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
theorem fderivWithin_tensorRSModel_eval_slots {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => (T z (β z)) (fun a : Fin s => V a z)) u y Xy =
      ((fderivWithin 𝕜 T u y Xy) (β y)) (fun a : Fin s => V a y) +
        (T y (fderivWithin 𝕜 β u y Xy)) (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          (T y (β y)) (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun z => T z (β z)
  have hα : DifferentiableWithinAt 𝕜 α u y := hT.clm_apply hβ
  have hslots := fderivWithin_tensor0SModel_eval_slots
    (𝕜 := 𝕜) (E := E) (s := s) α V u y Xy hα hV hu
  have hαderiv :
      fderivWithin 𝕜 α u y =
        (T y).comp (fderivWithin 𝕜 β u y) +
          (fderivWithin 𝕜 T u y).flip (β y) := by
    simpa [α] using fderivWithin_clm_apply (𝕜 := 𝕜) (s := u) (x := y) hu hT hβ
  rw [hslots, hαderiv]
  simp [α, add_assoc, add_comm]

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

/-- Hom-derivation form of the mixed model covariant derivative. Evaluating
`∇_X T` on a variable input covariant tensor and variable output slots equals
the directional derivative of the scalar evaluation, minus the covariant
derivative of the input and minus the covariant derivatives of the output
slots. -/
theorem covariantDeriv_tensorRSModelWithin_eval_derivation {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (u : Set E) (y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y (β y)) (fun a : Fin s => V a y)
      =
        fderivWithin 𝕜
          (fun z : E => (T z (β z)) (fun a : Fin s => V a z))
          u y (X y)
        - (T y
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
            r X ΓX β u y))
          (fun a : Fin s => V a y)
        - ∑ a : Fin s,
          (T y (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y))) := by
  classical
  have hprod := fderivWithin_tensorRSModel_eval_slots
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    T β V u y (X y) hT hβ hV hu
  rw [covariantDeriv_tensorRSModelWithin]
  rw [covariantDeriv_tensorRSModelAt_eval]
  rw [hprod]
  have hβcov :
      ((T y)
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
          r X ΓX β u y)) (fun a : Fin s => V a y) =
        ((T y) (fderivWithin 𝕜 β u y (X y))) (fun a : Fin s => V a y) -
          ((T y) ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y)) (β y)))
            (fun a : Fin s => V a y) := by
    simp [covariantDeriv_tensor0SModelWithin, covariantDeriv_tensor0SModelAt,
      lieDeriv_correctionL_apply]
  have hCorrS :
      ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) ((T y) (β y)))
          (fun a : Fin s => V a y) =
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    exact lieDeriv_correctionL_apply_slots (𝕜 := 𝕜) (E := E)
      (s := s) (ΓX y) ((T y) (β y)) (fun a : Fin s => V a y)
  have hsum :
      (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y)))) =
        (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y)))) +
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ((T y) (β y)).map_update_add
      (fun b : Fin s => V b y) a
      (fderivWithin 𝕜 (V a) u y (X y)) (ΓX y (V a y))
  rw [hβcov, hCorrS, hsum]
  abel

end ModelCovariantDerivative

end

end TensorLieDeriv
