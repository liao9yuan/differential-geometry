/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.RSTensor.Field
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
/-!
# Interior Product and Contraction of Tensors

This file defines the interior product (contraction with a tangent vector) and contraction
with a cotangent vector (1-form) for mixed tensors at a point of a smooth manifold.

## Main Definitions

* `interior_product s x v` : contraction of a (0,s+1)-tensor with a tangent vector `v`,
  giving a (0,s)-tensor by feeding `v` into the first slot.
* `contract_covariant r s x v` : contraction of an (r,s+1)-tensor with a tangent vector,
  giving an (r,s)-tensor by post-composing with `interior_product`.
* `contract_contravariant r s x α` : contraction of an (r+1,s)-tensor with a cotangent
  vector `α`, giving an (r,s)-tensor by pre-composing with tensoring with `α`.
* `contract_Tensor0SField_fun s α X` : pointwise contraction of a (0,s+1)-tensor field
  with a vector field, giving a (0,s)-tensor field.
* `contract_Tensor0SField s α X` : contraction of a smooth (0,s+1)-tensor field
  with a smooth vector field (a `ContMDiffSection` of the tangent bundle),
  yielding a smooth (0,s)-tensor field.

## Tags

interior product, contraction, cotangent, tensor, smooth manifold
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-!
## Model-level interior product

The pointwise interior product works at the model fiber level first. This is a pure
`NormedSpace`-level construction (currying + applying a vector), which we transport
to the bundle fiber via `tensor0SSpace_continuousLinearEquiv`.
-/

/-- The model-level interior product: given a vector `v : E`, contract a (0,s+1)-tensor
model fiber with `v` in its first slot. This is currying-then-applying. -/
noncomputable def model_interior_product (s : ℕ) (v : E) :
    Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  (ContinuousLinearMap.apply 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

/-- The model-level interior product, packaged as a continuous bilinear map in the
vector argument and the (0,s+1)-tensor argument. Used to prove smoothness of the
interior-product field operation. -/
noncomputable def model_interior_bilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] (s : ℕ) :
    E →L[𝕜] (Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

set_option linter.unusedSectionVars false in
theorem model_interior_bilinear_apply (s : ℕ) (v : E) (T : Tensor0SModel (s + 1) 𝕜 E) :
    model_interior_bilinear 𝕜 E s v T = model_interior_product s v T := rfl

/-!
## Interior product
-/

/-- Contraction of a (0,s+1)-tensor with a tangent vector `v`, giving a (0,s)-tensor
by feeding `v` into the first slot via the curry-left isomorphism. -/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm.toContinuousLinearMap.comp
    ((model_interior_product s (v : E)).comp
      (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).toContinuousLinearMap)

/-!
## Model-level tensor-with-covector embedding

Given a model-level (0,1)-tensor `α`, the map `β ↦ β ⊗ α` is a continuous linear map
`(0,r) →L (0,r+1)`. We build it as a linear map using `modelProduct` and promote to a
continuous linear map via finite-dimensionality.
-/

/-- The model-level embedding `β ↦ β ⊗ α : (0,r) →L (0,r+1)`, given a (0,1)-tensor `α`. -/
noncomputable def model_tensorWithCovector (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct r 1 β α
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.add_apply, add_mul]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-!
## Contraction of smooth tensor fields

We lift the pointwise `interior_product` to tensor fields: contracting a smooth
(0,s+1)-tensor field with a smooth vector field produces a smooth (0,s)-tensor field.
This corresponds to the standard result that contraction of a (0,s)-tensor field with
a smooth vector field yields a (0,s−1)-tensor field, using the Lean indexing
convention `s + 1 → s`.
-/

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
/-- Pointwise contraction of a (0,s+1)-tensor field with a vector field,
giving a (0,s)-tensor field. At each point `x`, this feeds `X(x)` into the first
slot of the (0,s+1)-tensor `α(x)` via the currying isomorphism. -/
noncomputable def contract_Tensor0SField_fun (s : ℕ)
    (α : (x : M) → Tensor0SSpace (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → Tensor0SSpace s I x :=
  fun x => interior_product s x (X x) (α x)

/-- Contraction of a smooth (0,s+1)-tensor field with a smooth vector field
yields a smooth (0,s)-tensor field.

If `α` is a smooth section of `T⁰_{s+1}M` and `X` is a smooth section of `TM`,
then the interior product `ι_X α`, defined pointwise by `(ι_X α)_x = ι_{X(x)} α_x`,
is a smooth section of `T⁰_s M`.

The proof reduces to smoothness of the bilinear model-level operation
`model_interior_bilinear` applied to the trivialized vector field and the
trivialized (0,s+1)-tensor field. The trivialization compatibility is a `rfl`-style
unfolding once the trivialization map's evaluation is expanded. -/
noncomputable def contract_Tensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  refine ⟨contract_Tensor0SField_fun s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  -- The trivialized image of `(ι_X α)(x)` equals `model_interior_bilinear 𝕜 E s g̃(x) f̃(x)`
  -- on the trivialization base set, where `f̃` and `g̃` are trivialized α and X.
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x => model_interior_bilinear 𝕜 E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
            (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := model_interior_bilinear 𝕜 E s)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  -- Equality of two model-fiber elements, prove via funext on `Fin s → E`.
  ext v
  -- LHS unfolds to `(α x) (Fin.cons (X x) (symmL ∘ v))`
  -- RHS unfolds to `(α x) (symmL ∘ Fin.cons g̃(x) v)`
  -- These are equal because `symmL (g̃(x)) = X x` for `x` in the base set, and
  -- `Fin.cons` commutes with composition.
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) (X x : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · -- i = 0
    change (X x : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · -- i = j.succ
    intro j
    rfl

/-- Contraction of (r,s+1) tensor with a tangent vector to get (r,s).

Given `T : (0,r) →L (0,s+1)` and `v ∈ TangentSpace`, we post-compose `T` with
`interior_product v`. The composition is done on the model fiber side (where `compL`
is available on normed spaces) and transported back via `tensorRSSpace_continuousLinearEquiv`. -/
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (model_interior_product s (v : E))).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) r (s + 1) x).toContinuousLinearMap)

/-- Contraction of (r+1,s) tensor with a cotangent vector (1-form) to get (r,s).

Given `T : (0,r+1) →L (0,s)` and `α ∈ (0,1)`, we pre-compose `T` with the embedding
`β ↦ β ⊗ α : (0,r) →L (0,r+1)`. The composition is done on the model fiber side
(using `compL.flip` for pre-composition) and transported back via
`tensorRSSpace_continuousLinearEquiv`. -/
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  let α_model : Tensor0SModel 1 𝕜 E := Tensor0SSpace.toModel α
  let embed_model : Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
    model_tensorWithCovector r α_model
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (r + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)).flip embed_model).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) (r + 1) s x).toContinuousLinearMap)

end FieldContraction

end
end Tensor0SBundle
