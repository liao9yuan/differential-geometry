/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Fiber
import DifferentialGeometry.Tensor.Multilinear.DualFiber
import Mathlib.LinearAlgebra.Contraction
/-!
# Mixed multilinear bundle fiber as a tensor product

This file establishes the canonical bundle-fiber-level linear equivalence

  `(MLF r at x) →L[𝕜] (MLF s at x)  ≃ₗ[𝕜]  (mlf-of-dual r at x) ⊗[𝕜] (MLF s at x)`

where:
* `MLF r at x = ContinuousMultilinearMap 𝕜 (Fin r → E x) 𝕜` (definitionally equal to
  `Bundle.continuousMultilinearMap 𝕜 r F E x`).
* `mlf-of-dual r at x = ContinuousMultilinearMap 𝕜 (Fin r → (E x →L[𝕜] 𝕜)) 𝕜`
  (the multilinear bundle of the dual at `x`).

The construction proceeds in two steps:

1. **Tensor-hom helper** `homEquivCDualTensor`: a model-fiber-level linear equivalence
   `(V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W)` for finite-dimensional normed spaces `V, W`,
   built by composing `LinearMap.toContinuousLinearMap.symm` with Mathlib's
   `dualTensorHomEquiv`.

2. **Substitution via the dual iso**: instantiate `homEquivCDualTensor` at
   `V := MLF r at x`, `W := MLF s at x`, then apply
   `dualMultilinearLinearEquivAt` (from `Multilinear/DualFiber.lean`) to the first
   tensor factor to convert `(MLF r at x →L[𝕜] 𝕜)` into the multilinear-of-dual fiber.

Crucially, we work entirely at the bundle-fiber level (over `E x`), not at the model
level (over `F`). The dual *bundle* of `E` has fibers `E x →L[𝕜] 𝕜`, not `F →L[𝕜] 𝕜`,
so the multilinear-of-dual bundle's fiber at `x` is multilinear maps on `E x →L[𝕜] 𝕜`.

## Main Definitions

* `ContinuousMultilinearMap.homEquivCDualTensor` : the abstract tensor-hom iso
  `(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W`.
* `Bundle.continuousMultilinearMap.mixedFiberTensorEquivAt` : the bundle-fiber-level
  iso between the mixed `(r, s)` fiber at `x` and `(mlf-of-dual r at x) ⊗ (MLF s at x)`.

## Tags

mixed tensor, dual, tensor product, vector bundle fiber
-/

noncomputable section

open Bundle TensorProduct

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (W : Type*) [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! ## Tensor-hom helper -/

/-- The canonical "tensor of duals" linear equivalence
`(V →L[𝕜] W) ≃ₗ[𝕜] (V →L[𝕜] 𝕜) ⊗[𝕜] W`
for finite-dimensional normed spaces `V` and `W`.

Built by composing `LinearMap.toContinuousLinearMap.symm` (in finite dimensions, all
linear maps are continuous), Mathlib's `Module.dualTensorHomEquiv` (which gives
`Module.Dual 𝕜 V ⊗[𝕜] W ≃ₗ[𝕜] V →ₗ[𝕜] W`), and `TensorProduct.congr` to bridge
between `Module.Dual` and the continuous dual. -/
noncomputable def homEquivCDualTensor :
    (V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) := by
  -- Step 1: (V →L[𝕜] W) ≃ₗ (V →ₗ[𝕜] W) (finite-dim)
  let e1 : (V →L[𝕜] W) ≃ₗ[𝕜] (V →ₗ[𝕜] W) := LinearMap.toContinuousLinearMap.symm
  -- Step 2: (V →ₗ[𝕜] W) ≃ₗ (Module.Dual 𝕜 V ⊗[𝕜] W) via dualTensorHomEquiv.symm
  let e2 : (V →ₗ[𝕜] W) ≃ₗ[𝕜] (Module.Dual 𝕜 V ⊗[𝕜] W) :=
    (dualTensorHomEquiv 𝕜 V W).symm
  -- Step 3: Replace `Module.Dual 𝕜 V` with the continuous dual `V →L[𝕜] 𝕜` in the first
  -- tensor factor.
  let cdualEquiv : (V →L[𝕜] 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 V :=
    LinearMap.toContinuousLinearMap.symm
  let e3 : (Module.Dual 𝕜 V ⊗[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) :=
    TensorProduct.congr cdualEquiv.symm (LinearEquiv.refl 𝕜 W)
  exact e1.trans (e2.trans e3)

end ContinuousMultilinearMap

/-! ## Transport between bundle and unfolded multilinear-fiber forms -/

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

-- Note: a transport CLE between the bundle form
-- `Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x`
-- and the unfolded form `CMM 𝕜 (Fin r → E x) 𝕜 →L[𝕜] CMM 𝕜 (Fin s → E x) 𝕜` would be
-- needed to bridge `MixedSection.toFun` (which uses the bundle form) with
-- `mixedFiberTensorEquivAt` (stated on the unfolded form).
--
-- An attempt to define such a transport via `arrowCongr` of two identity CLEs failed
-- due to instance diamonds: even though the underlying types are equal (since
-- `Bundle.continuousMultilinearMap` is `def`'d as a `ContinuousMultilinearMap`), Lean's
-- elaborator inserts different `TopologicalSpace` and `AddCommMonoid` instances
-- depending on which path it takes through the typeclass graph.
--
-- This is the same diamond that `Mixed/Fiber.lean` navigates with its private
-- `mixed_type_eq` theorem. Lifting `mixedFiberTensorEquivAt` to the section level
-- requires a more invasive approach (e.g. routing through the model fiber over `F`).

/-! ## The bundle-fiber-level mixed iso -/

/-- The bundle-fiber-level linear equivalence between the mixed multilinear bundle
fiber at `x` (= `Hom(MLF r fiber, MLF s fiber)`) and `(mlf-of-dual r at x) ⊗ (MLF s at x)`.

Stated using the unfolded `ContinuousMultilinearMap` form on the fibers `E x` and
their duals to avoid the topology diamond.

The construction:
1. Apply `homEquivCDualTensor` at `V := MLF r at x`, `W := MLF s at x`. This gives
   `((MLF r at x) →L[𝕜] (MLF s at x)) ≃ₗ ((MLF r at x →L[𝕜] 𝕜) ⊗ (MLF s at x))`.
2. Use `dualMultilinearLinearEquivAt` (the bundle-fiber-level dual iso from
   `Multilinear/DualFiber.lean`) to convert `(MLF r at x →L[𝕜] 𝕜)` into the
   multilinear-of-dual fiber `mlf-of-dual r at x`. -/
noncomputable def mixedFiberTensorEquivAt (r s : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  haveI : FiniteDimensional 𝕜 (E x) := fiberFiniteDimensional 𝕜 F E x
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  -- Step 1: The tensor-hom helper at V := MLF r fiber, W := MLF s fiber.
  let e1 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
        ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    ContinuousMultilinearMap.homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
  -- Step 2: Apply `dualMultilinearLinearEquivAt` to the first tensor factor.
  let e2 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 ≃ₗ[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    TensorProduct.congr
      (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x)
      (LinearEquiv.refl 𝕜 _)
  exact e1.trans e2

end Bundle.continuousMultilinearMap

end
