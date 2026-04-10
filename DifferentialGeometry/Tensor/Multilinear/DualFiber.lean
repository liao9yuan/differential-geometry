/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Dual
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.VectorBundle.Dual
import Mathlib.Topology.VectorBundle.FiniteDimensional
/-!
# Bundle-fiber-level dual equivalence

This file lifts the model-fiber-level iso `dualMultilinearEquivMultilinearOfDual`
from `Multilinear/Dual.lean` to a bundle-fiber-level continuous linear equivalence.

For each `x : B`, we get the canonical iso

  `(ContinuousMultilinearMap 𝕜 (Fin r → E x) 𝕜 →L[𝕜] 𝕜) ≃L[𝕜]
   ContinuousMultilinearMap 𝕜 (Fin r → (E x →L[𝕜] 𝕜)) 𝕜`

By unfolding `Bundle.continuousMultilinearMap` and `Bundle.dual`, this is the same as

  `(Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃L[𝕜]
   Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x`

up to topology equality (the bundle topology on `Bundle.continuousMultilinearMap 𝕜 r F E x`
agrees with the norm topology by `topology_eq` from `Multilinear/Fiber.lean`).

We state and prove the iso using the underlying `ContinuousMultilinearMap` types directly,
which avoids the topology-diamond between the bundle topology (from `Bundle.lean`'s
`TopologicalSpace.induced` instance) and the norm topology (from
`Multilinear/Fiber.lean`'s `instNormedAddCommGroup`). The iso is obtained by directly
instantiating `dualMultilinearEquivMultilinearOfDual` at the fiber `E x` and lifting to a
`ContinuousLinearEquiv` via finite-dimensionality.

## Main Definitions

* `Bundle.continuousMultilinearMap.dualMultilinearContinuousLinearEquivAt` :
  the bundle-fiber-level CLE between the dual of the multilinear maps on `E x` and
  the multilinear maps on the dual `(E x →L[𝕜] 𝕜)`. Stated using `ContinuousMultilinearMap`
  on the underlying fiber types `E x` and their duals, equivalent (by `topology_eq` from
  `Multilinear/Fiber.lean`) to the bundle-multilinear and multilinear-of-dual fibers.

## Tags

multilinear map, dual bundle, vector bundle fiber
-/

noncomputable section

open Bundle

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-! ## Finite-dimensionality of vector bundle fibers -/

/-- The fibers of a vector bundle are finite-dimensional whenever the model fiber is.
This is a project-local restating of `VectorBundle.finiteDimensional`. The model fiber
`F` is left explicit so it can be supplied at use sites. -/
theorem fiberFiniteDimensional
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (x : B) : FiniteDimensional 𝕜 (E x) :=
  VectorBundle.finiteDimensional 𝕜 F E x

/-! ## The bundle-fiber-level dual equivalence -/

/-- The bundle-fiber-level continuous linear equivalence between the dual of
`r`-multilinear maps on the fiber `E x` and `r`-multilinear maps on the dual fiber
`E x →L[𝕜] 𝕜`.

By unfolding `Bundle.continuousMultilinearMap` and `Bundle.dual`, this is canonically
identified with the iso

  `(Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃L[𝕜]
   Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x`

We state it using the unfolded `ContinuousMultilinearMap` form to avoid the topology
diamond between the bundle topology (from `Multilinear/Bundle.lean`) and the norm
topology (from `Multilinear/Fiber.lean`'s `instNormedAddCommGroup`). -/
noncomputable def dualMultilinearLinearEquivAt (r : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜 :=
  haveI : FiniteDimensional 𝕜 (E x) := fiberFiniteDimensional 𝕜 F E x
  ContinuousMultilinearMap.dualMultilinearEquivMultilinearOfDual 𝕜 (E x) r

theorem dualMultilinearLinearEquivAt_apply (r : ℕ) (x : B)
    (φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜)
    (α : Fin r → (E x →L[𝕜] 𝕜)) :
    dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x φ α =
      φ ((ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (E x) r) α) := rfl

/-- The forward direction of `dualMultilinearLinearEquivAt`: take a continuous linear
functional on the multilinear maps on `E x` and produce an `r`-multilinear map on
`(E x →L[𝕜] 𝕜)`. This is just `(dualMultilinearLinearEquivAt r x).toLinearMap`, exposed
as a separate definition for use at section level. -/
noncomputable def dualMultilinearMapAt (r : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜 :=
  (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).toLinearMap

/-- The inverse direction of `dualMultilinearLinearEquivAt`. -/
noncomputable def dualMultilinearInverseMapAt (r : ℕ) (x : B) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜 →ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) :=
  (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).symm.toLinearMap

end Bundle.continuousMultilinearMap

end
