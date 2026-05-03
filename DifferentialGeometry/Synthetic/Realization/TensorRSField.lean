import DifferentialGeometry.Synthetic.Realization.TensorContract
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Tensor.RSTensor.Field

/-!
# Realization: `Tensor0SField → TensorData` (Stage A)

Forward direction of the equivalence
`TensorRSField ∞ r s ≃ TensorData (C^∞(M,ℝ)) (Γ(TM)) r s`,
covering the cases `r = 0` with `s = 0, 1, 2`.

## Scope of this stage

The general case requires two pieces of machinery not yet in the codebase:

* **General `s` smoothness** — a multilinear smoothness lemma for sections of
  the `(0,s)`-tensor bundle evaluated on `s` smooth vector fields. The `s = 1`
  case is in `TensorContract.lean` (`covectorFieldPair_contMDiff`, ~80 lines);
  the `s = 2` case is effectively in `Metric.lean` (`gFun_smooth`, specialized
  to the metric inner product). The general form is a straightforward induction
  on `s`, deferred to Stage A'.

* **General `r` tensoriality** — for `r ≥ 1`, the `TensorData` has `r` covector
  slots typed as `V →ₗ[R] R` (C^∞(M)-linear functionals on `Γ(TM)`). Evaluating
  a smooth `TensorRSField` on such a functional requires the classical
  tensoriality lemma (every C^∞(M)-linear functional on `Γ(TM)` comes from a
  smooth 1-form), deferred to Stage B.

## Main definitions

* `Tensor0SField.toTensorData_0 α` : wraps a (0,0)-field (scalar field) as
  `TensorData (R_) (V_) 0 0`, via `toScalarField`.
* `Tensor0SField.toTensorData_1 α` : wraps a (0,1)-field (1-form) as
  `TensorData (R_) (V_) 0 1`, composing `covectorToFunctional` from
  `TensorContract.lean` with the synthetic `covectorToData`.
* `Tensor0SField.toTensorData_2 α` : wraps a (0,2)-field as
  `TensorData (R_) (V_) 0 2`, mirroring the construction of `concreteGTensor`
  in `Metric.lean`.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle SyntheticTensor
open Tensor0SBundle

namespace TensorRSFieldRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Shorthand: `C^∞(M, ℝ)`. -/
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-- Shorthand: smooth sections of the tangent bundle, `Γ(TM)`. -/
private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯

-- The `Tensor0SField (n := ∞) s` abbreviation requires `[IsManifold I (∞ + 1) M]`.
-- In `WithTop ℕ∞`, `∞ + 1 = ∞`, so this is satisfied by the ambient `[IsManifold I ∞ M]`;
-- we make the instance available explicitly so elaboration can synthesize it.
private instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  have h : ((∞ : WithTop ℕ∞) + 1) = ∞ := rfl
  rw [h]; infer_instance

/-! ## (0, 0) case — wrap `toScalarField` -/

/-- Forward map for the `(0,0)` case: a `(0,0)`-tensor field is a scalar field. -/
noncomputable def Tensor0SField.toTensorData_0
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0) :
    TensorData (R_ I M) (V_ I M) 0 0 :=
  scalarToData ⟨Tensor0SField.toScalarField ∞ α,
    Tensor0SField.toScalarField_contMDiff ∞ α⟩

theorem Tensor0SField.toTensorData_0_eval
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0) :
    Tensor0SField.toTensorData_0 I M α ![] ![] =
      ⟨Tensor0SField.toScalarField ∞ α,
       Tensor0SField.toScalarField_contMDiff ∞ α⟩ := rfl

/-! ## (0, 1) case — wrap `covectorToFunctional` -/

/-- Forward map for the `(0,1)` case: compose `covectorToFunctional` (from
`TensorContract.lean`, which turns a 1-form into a C^∞(M)-linear functional on
`Γ(TM)`) with the synthetic `covectorToData` packaging. -/
noncomputable def Tensor0SField.toTensorData_1
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1) :
    TensorData (R_ I M) (V_ I M) 0 1 :=
  covectorToData (TensorContractRealization.covectorToFunctional I M α)

theorem Tensor0SField.toTensorData_1_eval
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (X : V_ I M) :
    Tensor0SField.toTensorData_1 I M α ![X] ![] =
      TensorContractRealization.covectorToFunctional I M α X := rfl

theorem Tensor0SField.toTensorData_1_eval_pt
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 1)
    (X : V_ I M) (x : M) :
    (Tensor0SField.toTensorData_1 I M α ![X] ![]) x =
      (Tensor0SSpace.toModel (α x)) (fun _ : Fin 1 => X x) := rfl

/-! ## (0, 2) case — pointwise pairing of a (0,2)-field with two vector fields

Parallel to `gSmooth` / `concreteGTensor` in `Metric.lean`, but for a general
smooth (0,2)-tensor field `α` rather than a metric. Smoothness of the pointwise
pairing follows from the bilinear-continuous model evaluation
(`continuousMultilinearCurryFin1` iterated), with trivialization round-trips. -/

namespace Tensor0SField

/-- Pointwise pairing of a smooth (0,2)-tensor field with two smooth vector fields,
as a function `M → ℝ`. -/
private noncomputable def pair_2
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) : M → ℝ :=
  fun x => (Tensor0SSpace.toModel (α x)) (fun i : Fin 2 => if i = 0 then X x else Y x)

private theorem pair_2_contMDiff
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (pair_2 I M α X Y) := by
  intro x₀
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  have hY := Y.contMDiff x₀
  rw [contMDiffAt_section] at hY
  -- Bilinear-continuous evaluation: (T, v, w) ↦ T(fun i => if i = 0 then v else w)
  -- Factor as two `clm_apply` steps at the model level, using the left-curry equiv twice.
  let curry1 : Tensor0SModel 2 ℝ E →L[ℝ] (E →L[ℝ] Tensor0SModel 1 ℝ E) :=
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 2 => E) ℝ).toContinuousLinearMap
  let evalCLM : Tensor0SModel 1 ℝ E →L[ℝ] E →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearMap
  -- Step 1: curry1 applied to trivialized α gives a fiber-wise `E →L CMM(1)`.
  have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E) ∞
      (fun x => curry1 ((trivializationAt (Tensor0SModel 2 ℝ E)
        (fun x => Tensor0SSpace 2 I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    (contMDiffAt_const (c := curry1)).clm_apply hα
  -- Step 2: Apply at trivialized X to get a fiber-wise CMM(1).
  have h2 : ContMDiffAt I 𝓘(ℝ, Tensor0SModel 1 ℝ E) ∞
      (fun x => curry1 ((trivializationAt (Tensor0SModel 2 ℝ E)
        (fun x => Tensor0SSpace 2 I x) x₀ ⟨x, α x⟩).2)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, X x⟩).2)) x₀ :=
    h1.clm_apply hX
  -- Step 3: evalCLM turns CMM(1) into an `E →L ℝ` CLM.
  have h3 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun x => evalCLM
        (curry1 ((trivializationAt (Tensor0SModel 2 ℝ E)
          (fun x => Tensor0SSpace 2 I x) x₀ ⟨x, α x⟩).2)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, X x⟩).2))) x₀ :=
    (contMDiffAt_const (c := evalCLM)).clm_apply h2
  -- Step 4: Apply at trivialized Y to get a scalar.
  have h_combine : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => evalCLM
        (curry1 ((trivializationAt (Tensor0SModel 2 ℝ E)
          (fun x => Tensor0SSpace 2 I x) x₀ ⟨x, α x⟩).2)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, X x⟩).2))
        ((trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x, Y x⟩).2)) x₀ :=
    h3.clm_apply hY
  -- Translate the trivialized expression back to the fiber-level pair_2.
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase_tan := (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hbase_2 := (trivializationAt (Tensor0SModel 2 ℝ E)
    (fun x => Tensor0SSpace 2 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase_tan, hbase_2] with x hx_tan hx_2
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀
  set e_2 := trivializationAt (Tensor0SModel 2 ℝ E) (fun x => Tensor0SSpace 2 I x) x₀
  -- Unfold curry1 and evalCLM to get: LHS = α(x)(X x, Y x).
  -- The trick: `curry1 T v = T ∘ (fun i => if i = 0 then v else rest)` — well, more precisely
  -- `curry1 T v w = T (Fin.cons v w)`.
  unfold pair_2
  set β : Tensor0SModel 2 ℝ E := (e_2 ⟨x, α x⟩).2
  set vX : E := (e_tan ⟨x, X x⟩).2
  set vY : E := (e_tan ⟨x, Y x⟩).2
  change (Tensor0SSpace.toModel (α x))
      (fun i : Fin 2 => if i = 0 then X x else Y x) =
    evalCLM (curry1 β vX) vY
  -- `curry1 β vX` : `Tensor0SModel 1 ℝ E = CMM (Fin 1 → E) ℝ`.
  -- `evalCLM (curry1 β vX) vY = (curry1 β vX)(fun _ => vY) = β (Fin.cons vX (fun _ => vY))`.
  have hevalCLM :
      evalCLM (curry1 β vX) vY =
        β (Fin.cons vX (fun _ : Fin 1 => vY)) := by
    change (continuousMultilinearCurryFin1 ℝ E ℝ) (curry1 β vX) vY =
      β (Fin.cons vX (fun _ : Fin 1 => vY))
    rw [continuousMultilinearCurryFin1_apply]
    -- `curry1 β vX (Fin.snoc 0 vY) = β (Fin.cons vX (Fin.snoc 0 vY))` by curry-left
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ β) vX
        (Fin.snoc 0 vY) = β (Fin.cons vX (fun _ : Fin 1 => vY))
    rw [continuousMultilinearCurryLeftEquiv_apply]
    rfl
  rw [hevalCLM]
  -- Now: (toModel (α x)) (fun i => if i = 0 then X x else Y x) = β (Fin.cons vX (fun _ => vY))
  -- Use the trivialization-round-trip pattern from covectorFieldPair_contMDiff.
  have h_eq : β = e_2.continuousLinearMapAt ℝ x (α x) := by
    change (e_2 ⟨x, α x⟩).2 = e_2.linearMapAt ℝ x (α x)
    rw [e_2.coe_linearMapAt_of_mem (R := ℝ) hx_2]
  have h_eq_X : vX = e_tan.continuousLinearMapAt ℝ x (X x) := by
    change (e_tan ⟨x, X x⟩).2 = e_tan.linearMapAt ℝ x (X x)
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
  have h_eq_Y : vY = e_tan.continuousLinearMapAt ℝ x (Y x) := by
    change (e_tan ⟨x, Y x⟩).2 = e_tan.linearMapAt ℝ x (Y x)
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
  rw [h_eq, h_eq_X, h_eq_Y]
  have h_round_X : e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (X x)) = X x :=
    e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan (X x)
  have h_round_Y : e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (Y x)) = Y x :=
    e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan (Y x)
  -- 2-slot analog of `h_1MLap` from `covectorFieldPair_contMDiff`.
  have h_2MLap : ∀ (G : Tensor0SSpace 2 I x) (v' : Fin 2 → TangentSpace I x),
      (e_2.continuousLinearMapAt ℝ x G) v' = G (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro G v'
    have hGfib : G = e_2.symmL ℝ x (e_2.continuousLinearMapAt ℝ x G) :=
      (e_2.symmL_continuousLinearMapAt (R := ℝ) hx_2 G).symm
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan
      (e_2.continuousLinearMapAt ℝ x G)
    rw [hsym] at hGfib
    conv_rhs => rw [hGfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  rw [h_2MLap (α x)
    (Fin.cons (e_tan.continuousLinearMapAt ℝ x (X x))
      (fun _ : Fin 1 => e_tan.continuousLinearMapAt ℝ x (Y x)))]
  congr 1
  funext i
  fin_cases i
  · change X x = e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (X x))
    exact h_round_X.symm
  · change Y x = e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (Y x))
    exact h_round_Y.symm

/-- Pointwise pairing packaged as a smooth function. -/
private noncomputable def pair_2_smooth
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) : R_ I M :=
  ⟨pair_2 I M α X Y, pair_2_contMDiff I M α X Y⟩

private theorem pair_2_smooth_eval
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) (x : M) :
    (pair_2_smooth I M α X Y) x =
      (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else Y x) := rfl

/-! ### C^∞(M)-bilinearity of `pair_2_smooth` -/

private theorem pair_2_smooth_add_left
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X₁ X₂ Y : V_ I M) :
    pair_2_smooth I M α (X₁ + X₂) Y =
      pair_2_smooth I M α X₁ Y + pair_2_smooth I M α X₂ Y := by
  apply ContMDiffMap.ext; intro x
  simp only [pair_2_smooth_eval]
  change (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then (X₁ + X₂) x else Y x) =
      (Tensor0SSpace.toModel (α x))
          (fun i : Fin 2 => if i = 0 then X₁ x else Y x) +
      (Tensor0SSpace.toModel (α x))
          (fun i : Fin 2 => if i = 0 then X₂ x else Y x)
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [show (fun i : Fin 2 => if i = 0 then X₁ x + X₂ x else Y x) =
        Function.update (fun i : Fin 2 => if i = 0 then X₁ x else Y x) 0 (X₁ x + X₂ x) by
    funext k; fin_cases k <;> simp [Function.update]]
  rw [show ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X₁ x else Y x) 0
          (X₁ x + X₂ x))) =
      ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X₁ x else Y x) 0
          (X₁ x))) +
      ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X₁ x else Y x) 0
          (X₂ x))) from
    (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_add
      (fun i : Fin 2 => if i = 0 then X₁ x else Y x) 0 (X₁ x) (X₂ x)]
  congr 1
  · congr 1; funext k; fin_cases k <;> simp [Function.update]
  · congr 1; funext k; fin_cases k <;> simp [Function.update]

private theorem pair_2_smooth_smul_left
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (f : R_ I M) (X Y : V_ I M) :
    pair_2_smooth I M α (f • X) Y = f * pair_2_smooth I M α X Y := by
  apply ContMDiffMap.ext; intro x
  simp only [pair_2_smooth_eval]
  change (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then (f • X) x else Y x) =
      f x * (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else Y x)
  simp only [ContMDiffSection.coe_smulContMDiffMap]
  rw [show (fun i : Fin 2 => if i = 0 then (f x : ℝ) • X x else Y x) =
        Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 0 ((f x : ℝ) • X x) by
    funext k; fin_cases k <;> simp [Function.update]]
  rw [show ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 0
          ((f x : ℝ) • X x))) =
      (f x : ℝ) • ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 0
          (X x))) from
    (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_smul
      (fun i : Fin 2 => if i = 0 then X x else Y x) 0 (f x) (X x)]
  rw [show Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 0 (X x) =
        (fun i : Fin 2 => if i = 0 then X x else Y x) by
    funext k; fin_cases k <;> simp [Function.update]]
  simp [smul_eq_mul]

private theorem pair_2_smooth_add_right
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y₁ Y₂ : V_ I M) :
    pair_2_smooth I M α X (Y₁ + Y₂) =
      pair_2_smooth I M α X Y₁ + pair_2_smooth I M α X Y₂ := by
  apply ContMDiffMap.ext; intro x
  simp only [pair_2_smooth_eval]
  change (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else (Y₁ + Y₂) x) =
      (Tensor0SSpace.toModel (α x))
          (fun i : Fin 2 => if i = 0 then X x else Y₁ x) +
      (Tensor0SSpace.toModel (α x))
          (fun i : Fin 2 => if i = 0 then X x else Y₂ x)
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [show (fun i : Fin 2 => if i = 0 then X x else Y₁ x + Y₂ x) =
        Function.update (fun i : Fin 2 => if i = 0 then X x else Y₁ x) 1 (Y₁ x + Y₂ x) by
    funext k; fin_cases k <;> simp [Function.update]]
  rw [show ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y₁ x) 1
          (Y₁ x + Y₂ x))) =
      ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y₁ x) 1
          (Y₁ x))) +
      ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y₁ x) 1
          (Y₂ x))) from
    (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_add
      (fun i : Fin 2 => if i = 0 then X x else Y₁ x) 1 (Y₁ x) (Y₂ x)]
  congr 1
  · congr 1; funext k; fin_cases k <;> simp [Function.update]
  · congr 1; funext k; fin_cases k <;> simp [Function.update]

private theorem pair_2_smooth_smul_right
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (f : R_ I M) (X Y : V_ I M) :
    pair_2_smooth I M α X (f • Y) = f * pair_2_smooth I M α X Y := by
  apply ContMDiffMap.ext; intro x
  simp only [pair_2_smooth_eval]
  change (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else (f • Y) x) =
      f x * (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else Y x)
  simp only [ContMDiffSection.coe_smulContMDiffMap]
  rw [show (fun i : Fin 2 => if i = 0 then X x else (f x : ℝ) • Y x) =
        Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 1 ((f x : ℝ) • Y x) by
    funext k; fin_cases k <;> simp [Function.update]]
  rw [show ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 1
          ((f x : ℝ) • Y x))) =
      (f x : ℝ) • ((Tensor0SSpace.toModel (α x))
        (Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 1
          (Y x))) from
    (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_smul
      (fun i : Fin 2 => if i = 0 then X x else Y x) 1 (f x) (Y x)]
  rw [show Function.update (fun i : Fin 2 => if i = 0 then X x else Y x) 1 (Y x) =
        (fun i : Fin 2 => if i = 0 then X x else Y x) by
    funext k; fin_cases k <;> simp [Function.update]]
  simp [smul_eq_mul]

/-! ### Packaging as TensorData -/

/-- Forward map for the `(0,2)` case: package `pair_2_smooth` into a synthetic
`TensorData _ _ 0 2`, mirroring `concreteGTensor` in `Metric.lean`. -/
noncomputable def toTensorData_2
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2) :
    TensorData (R_ I M) (V_ I M) 0 2 where
  toFun vs :=
    MultilinearMap.constOfIsEmpty (R_ I M)
      (fun _ : Fin 0 => (V_ I M) →ₗ[R_ I M] R_ I M)
      (pair_2_smooth I M α (vs 0) (vs 1))
  map_update_add' m i x y := by
    suffices h : pair_2_smooth I M α (Function.update m i (x + y) 0)
          (Function.update m i (x + y) 1) =
        pair_2_smooth I M α (Function.update m i x 0) (Function.update m i x 1) +
        pair_2_smooth I M α (Function.update m i y 0) (Function.update m i y 1) by
      ext n
      simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.add_apply]
      exact h ▸ rfl
    rcases i with ⟨i, hi⟩
    interval_cases i
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact pair_2_smooth_add_left I M α x y (m 1)
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact pair_2_smooth_add_right I M α (m 0) x y
  map_update_smul' m i c x := by
    suffices h : pair_2_smooth I M α (Function.update m i (c • x) 0)
          (Function.update m i (c • x) 1) =
        c * pair_2_smooth I M α (Function.update m i x 0) (Function.update m i x 1) by
      ext n
      simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply, smul_eq_mul]
      exact h ▸ rfl
    rcases i with ⟨i, hi⟩
    interval_cases i
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact pair_2_smooth_smul_left I M α c x (m 1)
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact pair_2_smooth_smul_right I M α c (m 0) x

theorem toTensorData_2_eval
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) :
    toTensorData_2 I M α ![X, Y] ![] = pair_2_smooth I M α X Y := by
  simp [toTensorData_2]

theorem toTensorData_2_eval_pt
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 2)
    (X Y : V_ I M) (x : M) :
    (toTensorData_2 I M α ![X, Y] ![]) x =
      (Tensor0SSpace.toModel (α x))
        (fun i : Fin 2 => if i = 0 then X x else Y x) := by
  simp [toTensorData_2_eval, pair_2_smooth_eval]

end Tensor0SField

/-! ## General (0, s) case

Smoothness of pointwise evaluation `x ↦ (toModel (α x)) (fun i => vs i x)` for
arbitrary `s`, proved by induction on `s` via iterated
`continuousMultilinearCurryLeftEquiv` + `clm_apply` at the model level, then a
single trivialization round-trip.
-/

namespace Tensor0SField

/-- **Model-level helper**: evaluation of a smooth section `T` of the model
fiber bundle at `s` smooth vector-valued functions is smooth. Pure normed-space
calculus; no bundle topology. Proved by induction on `s`: the successor case
curries one slot via `continuousMultilinearCurryLeftEquiv` (a CLE) and applies
to `vs 0`, reducing to the inductive hypothesis. -/
private theorem model_eval_contMDiffAt :
    ∀ (s : ℕ) (x₀ : M)
      {T : M → Tensor0SModel s ℝ E}
      (_hT : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) ∞ T x₀)
      (vs : Fin s → M → E)
      (_hvs : ∀ i, ContMDiffAt I 𝓘(ℝ, E) ∞ (vs i) x₀),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => (T x) (fun i => vs i x)) x₀
  | 0, _, T, hT, vs, _ => by
      have h := (contMDiffAt_const
          (c := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ
            Fin.elim0))).clm_apply hT
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with x
      change (T x) (fun i : Fin 0 => vs i x) =
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ Fin.elim0) (T x)
      rw [ContinuousMultilinearMap.apply_apply]
      congr 1
      funext i
      exact i.elim0
  | s + 1, x₀, T, hT, vs, hvs => by
      let curry : Tensor0SModel (s + 1) ℝ E →L[ℝ]
          (E →L[ℝ] Tensor0SModel s ℝ E) :=
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (s + 1) => E) ℝ).toContinuousLinearMap
      have h_curry : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E) ∞
          (fun x => curry (T x)) x₀ :=
        (contMDiffAt_const (c := curry)).clm_apply hT
      have h_at0 : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) ∞
          (fun x => curry (T x) (vs 0 x)) x₀ :=
        h_curry.clm_apply (hvs 0)
      have h_ih := model_eval_contMDiffAt s x₀ h_at0
        (fun j : Fin s => fun x => vs j.succ x)
        (fun j => hvs j.succ)
      refine h_ih.congr_of_eventuallyEq ?_
      filter_upwards with x
      change (T x) (fun i : Fin (s + 1) => vs i x) =
        (curry (T x) (vs 0 x)) (fun j : Fin s => vs j.succ x)
      change (T x) (fun i : Fin (s + 1) => vs i x) =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ
          (T x)) (vs 0 x) (fun j : Fin s => vs j.succ x)
      rw [continuousMultilinearCurryLeftEquiv_apply]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; rfl

/-- **Main smoothness theorem**: for a smooth `(0,s)`-tensor field `α` and `s`
smooth vector fields `vs`, the pointwise evaluation `x ↦ α(x)(vs₀(x), …, vs_{s-1}(x))`
is a smooth real-valued function on `M`.

Generalizes `covectorFieldPair_contMDiff` (s=1) and `pair_2_contMDiff` (s=2). -/
theorem apply_contMDiff (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    (vs : Fin s → V_ I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => (Tensor0SSpace.toModel (α x)) (fun i => vs i x)) := by
  intro x₀
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  set e_α := trivializationAt (Tensor0SModel s ℝ E)
    (fun x => Tensor0SSpace s I x) x₀ with he_α
  set e_tan := trivializationAt E (TangentSpace I : M → Type _) x₀ with he_tan
  have hvs_triv : ∀ i, ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun x => (e_tan ⟨x, vs i x⟩).2) x₀ := by
    intro i
    have h := (vs i).contMDiff x₀
    rw [contMDiffAt_section] at h
    exact h
  have h_combine := model_eval_contMDiffAt (I := I) (M := M) s x₀ hα
    (fun i x => (e_tan ⟨x, vs i x⟩).2) hvs_triv
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase_tan := e_tan.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hbase_s := e_α.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase_tan, hbase_s] with x hx_tan hx_s
  -- Round-trip: LHS = (α x)(fun i => vs i x); RHS = (e_α.2 (α x))(fun i => (e_tan.2 (vs i x))).
  change (Tensor0SSpace.toModel (α x)) (fun i => vs i x) =
    (e_α ⟨x, α x⟩).2 (fun i => (e_tan ⟨x, vs i x⟩).2)
  -- Step 1: (e_α ⟨x, α x⟩).2 = e_α.continuousLinearMapAt ℝ x (α x)
  have hG : (e_α ⟨x, α x⟩).2 = e_α.continuousLinearMapAt ℝ x (α x) := by
    change (e_α ⟨x, α x⟩).2 = e_α.linearMapAt ℝ x (α x)
    rw [e_α.coe_linearMapAt_of_mem (R := ℝ) hx_s]
  have hv : ∀ i, (e_tan ⟨x, vs i x⟩).2 =
      e_tan.continuousLinearMapAt ℝ x (vs i x) := by
    intro i
    change (e_tan ⟨x, vs i x⟩).2 = e_tan.linearMapAt ℝ x (vs i x)
    rw [e_tan.coe_linearMapAt_of_mem (R := ℝ) hx_tan]
  -- Step 2: s-slot analog of `h_1MLap` / `h_2MLap`.
  have h_sMLap : ∀ (H : Tensor0SSpace s I x) (v' : Fin s → TangentSpace I x),
      (e_α.continuousLinearMapAt ℝ x H) v' =
        H (fun i => e_tan.symmL ℝ x (v' i)) := by
    intro H v'
    have hHfib : H = e_α.symmL ℝ x (e_α.continuousLinearMapAt ℝ x H) :=
      (e_α.symmL_continuousLinearMapAt (R := ℝ) hx_s H).symm
    have hsym := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (F := E) (E := TangentSpace I) (𝕜 := ℝ) x₀ x hx_tan
      (e_α.continuousLinearMapAt ℝ x H)
    rw [hsym] at hHfib
    conv_rhs => rw [hHfib]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact (e_tan.continuousLinearMapAt_symmL (R := ℝ) hx_tan (v' i)).symm
  have h_round : ∀ i,
      e_tan.symmL ℝ x (e_tan.continuousLinearMapAt ℝ x (vs i x)) = vs i x :=
    fun i => e_tan.symmL_continuousLinearMapAt (R := ℝ) hx_tan (vs i x)
  rw [show (fun i : Fin s => (e_tan ⟨x, vs i x⟩).2) =
        (fun i : Fin s => e_tan.continuousLinearMapAt ℝ x (vs i x)) from funext hv,
      hG, h_sMLap (α x)
        (fun i => e_tan.continuousLinearMapAt ℝ x (vs i x))]
  congr 1
  funext i
  exact (h_round i).symm

/-- The pointwise pairing of a `(0,s)`-tensor field with `s` vector fields,
packaged as a smooth scalar function `C^∞(M, ℝ)`. -/
noncomputable def pair (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    (vs : Fin s → V_ I M) : R_ I M :=
  ⟨fun x => (Tensor0SSpace.toModel (α x)) (fun i => vs i x),
    apply_contMDiff I M s α vs⟩

@[simp] theorem pair_apply (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    (vs : Fin s → V_ I M) (x : M) :
    (pair I M s α vs) x = (Tensor0SSpace.toModel (α x)) (fun i => vs i x) := rfl

/-! ### C^∞(M)-multilinearity of `pair` -/

/-- `Function.update` on `V_`-valued tuples commutes with pointwise evaluation. -/
private theorem update_eval {s : ℕ} [DecidableEq (Fin s)]
    (vs : Fin s → V_ I M) (i : Fin s)
    (w : V_ I M) (x : M) (j : Fin s) :
    (Function.update vs i w j) x =
      Function.update (fun k => vs k x) i (w x) j := by
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · simp [Function.update_of_ne h]

private theorem pair_update_add (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    [DecidableEq (Fin s)]
    (vs : Fin s → V_ I M) (i : Fin s) (X Y : V_ I M) :
    pair I M s α (Function.update vs i (X + Y)) =
      pair I M s α (Function.update vs i X) +
      pair I M s α (Function.update vs i Y) := by
  apply ContMDiffMap.ext; intro x
  change (Tensor0SSpace.toModel (α x))
      (fun j => (Function.update vs i (X + Y) j) x) =
    (Tensor0SSpace.toModel (α x))
      (fun j => (Function.update vs i X j) x) +
    (Tensor0SSpace.toModel (α x))
      (fun j => (Function.update vs i Y j) x)
  rw [show (fun j => (Function.update vs i (X + Y) j) x) =
        Function.update (fun k => vs k x) i ((X + Y) x) from
      funext (update_eval I M vs i (X + Y) x),
      show (fun j => (Function.update vs i X j) x) =
        Function.update (fun k => vs k x) i (X x) from
      funext (update_eval I M vs i X x),
      show (fun j => (Function.update vs i Y j) x) =
        Function.update (fun k => vs k x) i (Y x) from
      funext (update_eval I M vs i Y x),
      show ((X + Y) x) = X x + Y x from rfl,
      show ((Tensor0SSpace.toModel (α x))
          (Function.update (fun k => vs k x) i (X x + Y x))) =
        ((Tensor0SSpace.toModel (α x))
          (Function.update (fun k => vs k x) i (X x))) +
        ((Tensor0SSpace.toModel (α x))
          (Function.update (fun k => vs k x) i (Y x))) from
      (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_add
        (fun k => vs k x) i (X x) (Y x)]

private theorem pair_update_smul (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    [DecidableEq (Fin s)]
    (vs : Fin s → V_ I M) (i : Fin s) (c : R_ I M) (X : V_ I M) :
    pair I M s α (Function.update vs i (c • X)) =
      c * pair I M s α (Function.update vs i X) := by
  apply ContMDiffMap.ext; intro x
  change (Tensor0SSpace.toModel (α x))
      (fun j => (Function.update vs i (c • X) j) x) =
    c x * (Tensor0SSpace.toModel (α x))
      (fun j => (Function.update vs i X j) x)
  rw [show (fun j => (Function.update vs i (c • X) j) x) =
        Function.update (fun k => vs k x) i ((c • X) x) from
      funext (update_eval I M vs i (c • X) x),
      show (fun j => (Function.update vs i X j) x) =
        Function.update (fun k => vs k x) i (X x) from
      funext (update_eval I M vs i X x),
      show ((c • X) x) = (c x : ℝ) • X x from rfl,
      show ((Tensor0SSpace.toModel (α x))
          (Function.update (fun k => vs k x) i ((c x : ℝ) • X x))) =
        (c x : ℝ) • ((Tensor0SSpace.toModel (α x))
          (Function.update (fun k => vs k x) i (X x))) from
      (Tensor0SSpace.toModel (α x)).toMultilinearMap.map_update_smul
        (fun k => vs k x) i (c x) (X x),
      smul_eq_mul]

/-- **General forward map**: a smooth `(0,s)`-tensor field `α` packaged as a
synthetic `TensorData (R_) (V_) 0 s`. Generalizes `toTensorData_0/_1/_2`. -/
noncomputable def toTensorData (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s) :
    TensorData (R_ I M) (V_ I M) 0 s where
  toFun vs :=
    MultilinearMap.constOfIsEmpty (R_ I M)
      (fun _ : Fin 0 => (V_ I M) →ₗ[R_ I M] R_ I M)
      (pair I M s α vs)
  map_update_add' m i X Y := by
    suffices h : pair I M s α (Function.update m i (X + Y)) =
        pair I M s α (Function.update m i X) +
        pair I M s α (Function.update m i Y) by
      ext n
      simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.add_apply]
      exact h ▸ rfl
    exact pair_update_add I M s α m i X Y
  map_update_smul' m i c X := by
    suffices h : pair I M s α (Function.update m i (c • X)) =
        c * pair I M s α (Function.update m i X) by
      ext n
      simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply,
        smul_eq_mul]
      exact h ▸ rfl
    exact pair_update_smul I M s α m i c X

theorem toTensorData_eval (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    (vs : Fin s → V_ I M) :
    toTensorData I M s α vs ![] = pair I M s α vs := by
  simp [toTensorData]

theorem toTensorData_eval_pt (s : ℕ)
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) s)
    (vs : Fin s → V_ I M) (x : M) :
    (toTensorData I M s α vs ![]) x =
      (Tensor0SSpace.toModel (α x)) (fun i => vs i x) := by
  simp [toTensorData_eval]

end Tensor0SField

end TensorRSFieldRealization

end
