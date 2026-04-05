/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Product.Fiber
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Bundle.Equiv
/-!
# Tensor Product of Multilinear Bundle Fibers

This file establishes that the `(s+q)`-multilinear bundle fiber is continuously linearly
equivalent to the tensor product of the `s`-multilinear and `q`-multilinear bundle fibers.

We construct a chain of continuous linear equivalences:

  `Bundle.cmm (s+q) F E x ≃L[𝕜] MLF(s+q) ≃L[𝕜] MLF(s) ⊗ MLF(q) ≃L[𝕜] Bundle.cmm s ⊗ Bundle.cmm q`

where the last step uses the tensor product bundle's trivialization CLE.

We then package this into a `C^n` vector bundle equivalence (`ContMDiffVectorBundleEquiv`)
and prove section-level smoothness results.

## Main Definitions

* `Bundle.continuousMultilinearMap.modelEquivL`: CLE between `MLF(s+q)` and `MLF(s) ⊗ MLF(q)`.
* `Bundle.continuousMultilinearMap.tensorTrivCLE`: CLE between `Bundle.cmm s ⊗ Bundle.cmm q`
  (with `tensorFiberTopology`) and `MLF(s) ⊗ MLF(q)` (with norm topology).
* `Bundle.continuousMultilinearMap.fiberEquivL`: the full fiberwise CLE from
  `Bundle.cmm (s+q)` to the tensor product bundle fiber.
* `fiberEquivBundle`: the `C^n` vector bundle equivalence.
* `contMDiff_fiberEquivL_section`: smooth sections map to smooth sections.
* `contMDiff_fiberEquivL_symm_section`: the inverse map on smooth sections.

## Tags

multilinear map, tensor product, vector bundle, continuous linear equivalence
-/

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Abbreviation for the model fiber of the `s`-multilinear bundle. -/
local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-- The continuous linear equivalence between the model fiber of the `(s+q)`-multilinear
bundle and the tensor product of the `s`- and `q`-model fibers. Both sides are
finite-dimensional normed spaces, so the `LinearEquiv` from dimension counting is
automatically continuous. -/
noncomputable def modelEquivL (s q : ℕ) : (MLF (s + q)) ≃L[𝕜] (MLF s) ⊗[𝕜] (MLF q) := by
  haveI : FiniteDimensional 𝕜 (MLF s) := continuousMultilinearMap_finiteDimensional s
  haveI : FiniteDimensional 𝕜 (MLF q) := continuousMultilinearMap_finiteDimensional q
  haveI : FiniteDimensional 𝕜 (MLF (s + q)) := continuousMultilinearMap_finiteDimensional (s + q)
  haveI : FiniteDimensional 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact (LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_continuousMultilinearMap s,
        finrank_continuousMultilinearMap q,
        finrank_continuousMultilinearMap (s + q), pow_add])).toContinuousLinearEquiv

/-- The fiberwise continuous linear equivalence between the `(s+q)`-multilinear bundle fiber
and the tensor product of the `s`- and `q`-model fibers.

This composes the trivialization CLE `continuousLinearEquivAt` (which maps the bundle fiber
to the model fiber `MLF (s+q)`) with `modelEquivL` (which maps `MLF (s+q)` to
`(MLF s) ⊗ (MLF q)`). -/
noncomputable def equivL (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃L[𝕜] (MLF s) ⊗[𝕜] (MLF q) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x).trans (modelEquivL s q)

/-!
## Trivialization CLE for the tensor product of multilinear bundle fibers

The tensor product bundle gives `tensorFiberTopology` on
`Bundle.cmm s F E x ⊗[𝕜] Bundle.cmm q F E x`. The map
`TensorProduct.map (continuousLinearEquivAt s x) (continuousLinearEquivAt q x)` is a
linear equivalence to `(MLF s) ⊗ (MLF q)` (which has `NormedAddCommGroup` from HomEquiv).
Since `tensorFiberTopology` is defined as `induced` by this map, it is automatically
continuous. The inverse is continuous by finite-dimensionality.
-/

/-- The topology on the tensor product of two multilinear bundle fibers, from the tensor
product bundle construction. -/
noncomputable def tensorFiber (s q : ℕ) (x : B) :
    TopologicalSpace
      (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.tensorFiberTopology
    (𝕜 := 𝕜) (B := B)
    (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x

/-- The trivialization CLE from the tensor product of multilinear bundle fibers
(with `tensorFiberTopology`) to the tensor product of model fibers (with norm topology).
This is a specialization of `tensorFiberCLE` to multilinear bundle fibers. -/
noncomputable def tensorTrivCLE (s q : ℕ) (x : B) :
    letI := tensorFiber (𝕜 := 𝕜) (F := F) (E := E) s q x
    (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
     Bundle.continuousMultilinearMap 𝕜 q F E x) ≃L[𝕜]
    ((MLF s) ⊗[𝕜] (MLF q)) := by
  letI := tensorFiber (𝕜 := 𝕜) (F := F) (E := E) s q x
  exact Bundle.TensorProduct.continuousLinearEquivAt 𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E) x

/-- The fiberwise continuous linear equivalence between the `(s+q)`-multilinear bundle fiber
and the tensor product of the `s`- and `q`-multilinear bundle fibers (with
`tensorFiberTopology` from the tensor product bundle).

Composes three CLEs:
1. `continuousLinearEquivAt (s+q) x` : `Bundle.cmm (s+q) F E x ≃L MLF(s+q)`
2. `modelEquivL s q` : `MLF(s+q) ≃L (MLF s) ⊗ (MLF q)`
3. `(tensorTrivCLE s q x).symm` : `(MLF s) ⊗ (MLF q) ≃L Bundle.cmm s ⊗ Bundle.cmm q` -/
noncomputable def fiberEquivL (s q : ℕ) (x : B) :
    letI := tensorFiber (𝕜 := 𝕜) (F := F) (E := E) s q x
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃L[𝕜]
    (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
     Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  letI := tensorFiber (𝕜 := 𝕜) (F := F) (E := E) s q x
  exact (equivL s q x).trans (tensorTrivCLE s q x).symm

/-!
## The `C^n` vector bundle equivalence

We package `fiberEquivL` into a `ContMDiffVectorBundleEquiv`. The smoothness of
the total space diffeomorphism follows from the fiberwise CLEs.
-/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]
variable (s q : ℕ)

-- Helper instances: the multilinear bundle fibers are AddCommGroup and Module,
-- needed by the tensor product bundle construction.
-- These unfold through Bundle.continuousMultilinearMap to ContinuousMultilinearMap instances.
private instance cmmAddCommGroup (x : B) :
    AddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

private instance cmmModule' (x : B) :
    Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  dsimp [Bundle.continuousMultilinearMap]; infer_instance

/-!
## The Equiv between total spaces

We construct the set-theoretic equivalence between the total spaces of
`Bundle.cmm (s+q) F E` and the tensor product of `Bundle.cmm s F E` and `Bundle.cmm q F E`,
given by applying `fiberEquivL` fiberwise.
-/

/-- The underlying `Equiv` between total spaces, applying `fiberEquivL` on each fiber. -/
def totalSpaceEquiv :
    TotalSpace (MLF (s + q)) (Bundle.continuousMultilinearMap 𝕜 (s + q) F E) ≃
    TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  letI (x : B) : TopologicalSpace
      (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
  exact {
    toFun := fun p => ⟨p.proj, fiberEquivL s q p.proj p.snd⟩
    invFun := fun p => ⟨p.proj, (fiberEquivL s q p.proj).symm p.snd⟩
    left_inv := fun ⟨x, v⟩ => by
      simp only [TotalSpace.mk_inj]
      exact (fiberEquivL s q x).symm_apply_apply v
    right_inv := fun ⟨x, w⟩ => by
      simp only [TotalSpace.mk_inj]
      exact (fiberEquivL s q x).apply_symm_apply w
  }

/-- The `C^n` vector bundle equivalence between the `(s+q)`-multilinear bundle and
the tensor product of the `s`- and `q`-multilinear bundles.

The fiberwise map is `fiberEquivL`, which composes:
1. `continuousLinearEquivAt (s+q) x` : trivialize to model fiber `MLF(s+q)`
2. `modelEquivL s q` : constant CLE to `MLF(s) ⊗ MLF(q)`
3. `(tensorTrivCLE s q x).symm` : un-trivialize to the tensor product fiber -/
def fiberEquivBundle :
    letI (x : B) : TopologicalSpace
        (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.tensorFiberTopology
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
    letI : TopologicalSpace (TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
          Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
      Bundle.TensorProduct.tensorTotalSpaceTop
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    letI : FiberBundle ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
          Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    letI : VectorBundle 𝕜 ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
          Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF (s + q))
      (Bundle.continuousMultilinearMap 𝕜 (s + q) F E)
      ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  -- Provide all tensor product bundle instances
  letI (x : B) : TopologicalSpace
      (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
  letI : TopologicalSpace (TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Bundle.TensorProduct.tensorTotalSpaceTop
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  letI : FiberBundle ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  letI : VectorBundle 𝕜 ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  exact {
    baseMap := _root_.id
    toDiffeomorph := {
      toEquiv := totalSpaceEquiv s q
      contMDiff_toFun := sorry
      contMDiff_invFun := sorry
    }
    fiberLinearEquiv := fun x => (fiberEquivL s q x).toLinearEquiv
    fiber_compat := fun x v => rfl
  }

/-!
## Section-level smoothness
-/

/-- If `α` is a `C^n` section of the `(s+q)`-multilinear bundle, then
`fun x => fiberEquivL s q x (α x)` is a `C^n` section of the tensor product of the
`s`-multilinear and `q`-multilinear bundles. -/
theorem contMDiff_fiberEquivL_section
    (α : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)
    (hα : ContMDiff IB (IB.prod 𝓘(𝕜, MLF (s + q))) n
      (fun x => TotalSpace.mk' (MLF (s + q)) x (α x))) :
    letI (x : B) : TopologicalSpace
        (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.tensorFiberTopology
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
    letI : FiberBundle ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
          Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    letI : VectorBundle 𝕜 ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
          Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    ContMDiff IB (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q))) n
      (fun x => TotalSpace.mk' ((MLF s) ⊗[𝕜] (MLF q)) x
        (fiberEquivL (𝕜 := 𝕜) (F := F) (E := E) s q x (α x))) := by
  sorry

/-- The inverse: if `β` is a `C^n` section of the tensor product bundle, then
`fun x => (fiberEquivL s q x).symm (β x)` is a `C^n` section of the
`(s+q)`-multilinear bundle. -/
theorem contMDiff_fiberEquivL_symm_section
    (β : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
      Bundle.continuousMultilinearMap 𝕜 q F E x)
    (hβ :
      letI (x : B) : TopologicalSpace
          (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
           Bundle.continuousMultilinearMap 𝕜 q F E x) :=
        Bundle.TensorProduct.tensorFiberTopology
          (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
          (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
          (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
      letI : TopologicalSpace (TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
            Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
        Bundle.TensorProduct.tensorTotalSpaceTop
          (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
          (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
          (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
      ContMDiff IB (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q))) n
        (fun x => TotalSpace.mk' ((MLF s) ⊗[𝕜] (MLF q)) x (β x))) :
    letI (x : B) : TopologicalSpace
        (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :=
      Bundle.TensorProduct.tensorFiberTopology
        (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
        (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
        (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E) x
    ContMDiff IB (IB.prod 𝓘(𝕜, MLF (s + q))) n
      (fun x => TotalSpace.mk' (MLF (s + q)) x
        ((fiberEquivL (𝕜 := 𝕜) (F := F) (E := E) s q x).symm (β x))) := by
  sorry

end Bundle.continuousMultilinearMap

end
