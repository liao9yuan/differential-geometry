/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Bundle
import DifferentialGeometry.Tensor.RSTensor.Product
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

## Tags

interior product, contraction, cotangent, tensor, smooth manifold
-/

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-!
## Interior product
-/

/-- Contraction of a (0,s+1)-tensor with a tangent vector `v`, giving a (0,s)-tensor
by feeding `v` into the first slot via the curry-left isomorphism. -/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x := by
  unfold Tensor0SSpace TangentSpace
  let curry_equiv := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => E) 𝕜
  exact ContinuousLinearMap.comp
    (ContinuousLinearMap.apply 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v)
    curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap

/-!
## Contraction of mixed tensors
-/

/-- Contraction of an (r,s+1)-tensor with a tangent vector `v`, giving an (r,s)-tensor
by post-composing with `interior_product s x v`. -/
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (s + 1) I x)
    (Tensor0SSpace s I x)
    (interior_product s x v)

/-- The map that tensors a covariant tensor with a fixed 1-form `u`:
`(0,r) →L (0,r+1)` given by `α ↦ α ⊗ u`. -/
noncomputable def tensorWithCovector (r : ℕ) (x : M)
    (u : CotangentSpace I x) :
    Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (r + 1) I x :=
  LinearMap.toContinuousLinearMap ((tensor0S_product_bilinear r 1 x).flip u)

/-- Contraction of an (r+1,s)-tensor with a 1-form (cotangent vector) `u`,
giving an (r,s)-tensor by pre-composing with `tensorWithCovector r x u`.

Concretely, `contract_contravariant T u` sends `α : (0,r)` to `T (α ⊗ u)`. -/
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (u : CotangentSpace I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  (ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (r + 1) I x)
    (Tensor0SSpace s I x)).flip
    (tensorWithCovector r x u)

end
end Tensor0SBundle
