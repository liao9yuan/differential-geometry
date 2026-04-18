/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Tangent.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import DifferentialGeometry.Tensor.Tangent.Field
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
* `tensorWithCovector r x u` : the map `(0,r) →L (0,r+1)` given by `α ↦ α ⊗ u`.
* `contract_contravariant r s x u` : contraction of an (r+1,s)-tensor with a cotangent
  vector `u`, giving an (r,s)-tensor by pre-composing with `tensorWithCovector`.
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
## Interior product
-/

/-- Contraction of a (0,s+1)-tensor with a tangent vector `v`, giving a (0,s)-tensor
by feeding `v` into the first slot via the curry-left isomorphism. -/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
      ((continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).toContinuousLinearMap))


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
is a smooth section of `T⁰_s M`. -/
noncomputable def contract_Tensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := Bundle.continuousMultilinearMap.topologicalSpace_totalSpace 𝕜 _ E (TangentSpace I) (s + 1)
  unfold Tensor0SField
  letI := Bundle.continuousMultilinearMap.topologicalSpace_totalSpace 𝕜 _ E (TangentSpace I) s
  exact ⟨contract_Tensor0SField_fun s α.toFun X, sorry⟩

end FieldContraction

end
end Tensor0SBundle
