/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Product
import DifferentialGeometry.Tensor.Product.Contract
import DifferentialGeometry.Tensor.Product.Equiv
import DifferentialGeometry.Tensor.Multilinear.Dual

/-!
# Contraction of Mixed `(1,1)`-Tensor Fields

This file defines the contraction (trace) of a mixed `(1,1)`-tensor field by routing
through the tensor product decomposition and applying the evaluation pairing.

The chain of smooth operations is:
1. `mixedSectionToTensorBundleSection` : `T^1_1(E) → T⁰₁(E*) ⊗ T⁰₁(E)`
2. `dualBundle_multilinearOfDual_equiv` on first factor :
   `T⁰₁(E*) ⊗ T⁰₁(E) → dual(T⁰₁(E)) ⊗ T⁰₁(E)`
3. `TensorProduct.comm` : `dual(T⁰₁(E)) ⊗ T⁰₁(E) → T⁰₁(E) ⊗ dual(T⁰₁(E))`
4. `contract_section` : `T⁰₁(E) ⊗ dual(T⁰₁(E)) → 𝕜`

## Tags

contraction, trace, mixed tensor, tensor field, vector bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap TensorProduct

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

namespace MixedSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

-- Abbreviations for multilinear bundle fibers
local notation "MLF" => fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x
local notation "MLF_dual" => fun x => Bundle.continuousMultilinearMap 𝕜 1 (F →L[𝕜] 𝕜)
    (Bundle.dual 𝕜 E) x
local notation "dualMLF" => fun x => Bundle.dual 𝕜 MLF x

/-- Contraction of a smooth `(1,1)`-mixed section to a smooth scalar function.

The contraction is the composition of four fiberwise linear maps, each smooth:
1. `mixedSectionToTensorBundleSection` : mixed(1,1) → `MLF_dual(1) ⊗ MLF(1)`
2. `dualBundle_multilinearOfDual_equiv 1` on first factor : `MLF_dual(1) ≃ dual(MLF(1))`
3. `TensorProduct.comm` : swap factors
4. `contract_section` : evaluation pairing → 𝕜

The fiberwise function is:
  `T x ↦ contract(comm(mapLeft(e_dual, mixedToTensor(T x))))` -/
noncomputable def contract_MixedSection_11
    (T : MixedSection 𝕜 F IB E n 1 1) :
    C^n⟮IB, B; 𝓘(𝕜), 𝕜⟯ :=
  -- The four fiberwise operations:
  let e_mixed := Bundle.continuousMultilinearMap.multilinearHomTensorEquivAt_bundle
    (𝕜 := 𝕜) (F := F) (E := E) 1 1
  let e_dual := Bundle.continuousMultilinearMap.dualMultilinearFiberwiseEquiv (𝕜 := 𝕜)
    (F := F) (E := E) 1
  -- Compose fiberwise: at each x, apply all four linear equivs then contract
  ⟨fun x =>
    let t := e_mixed x (T x)                               -- MLF_dual(1) x ⊗ MLF(1) x
    let t₂ := TensorProduct.map (e_dual x).symm.toLinearMap
      (LinearMap.id) t                                      -- dual(MLF(1)) x ⊗ MLF(1) x
    let t₃ := (TensorProduct.comm 𝕜 _ _) t₂                -- MLF(1) x ⊗ (MLF(1) x →L 𝕜)
    -- Apply the evaluation pairing v ⊗ f ↦ f(v).
    -- We inline this rather than using `evalTensorDualLM` because the bundle fiber
    -- `Bundle.continuousMultilinearMap` has a different TopologicalSpace instance
    -- than what `evalTensorDualLM` expects (bundle topology vs norm topology).
    (TensorProduct.lift
      ({ toFun := fun v =>
          ({ toFun := fun f => f v
             map_add' := fun f₁ f₂ => ContinuousLinearMap.add_apply f₁ f₂ v
             map_smul' := fun c f => ContinuousLinearMap.smul_apply c f v } :
            (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜)
         map_add' := fun v₁ v₂ => by ext f; exact map_add f v₁ v₂
         map_smul' := fun c v => by ext f; exact map_smul f c v })) t₃,
   by
    -- The 5 smooth maps whose composition gives smoothness:
    --
    -- (1) T.contMDiff :
    --     ContMDiff IB (IB.prod 𝓘(𝕜, MLF₁ →L MLF₁)) n (fun x => ⟨x, T x⟩)
    --
    -- (2) (mixedBundle_tensorBundle_equiv (r := 1) (s := 1)).toDiffeomorph.contMDiff :
    --     ContMDiff (IB.prod 𝓘(𝕜, MLF₁ →L MLF₁)) (IB.prod 𝓘(𝕜, MLF_dual₁ ⊗ MLF₁)) n
    --
    -- (3) (tensorProductMapLeft n (dualBundle_multilinearOfDual_equiv 1) _).toDiffeomorph.contMDiff :
    --     ContMDiff (IB.prod 𝓘(𝕜, MLF_dual₁ ⊗ MLF₁)) (IB.prod 𝓘(𝕜, dual(MLF₁) ⊗ MLF₁)) n
    --
    -- (4) (tensorProductComm n).toDiffeomorph.contMDiff :
    --     ContMDiff (IB.prod 𝓘(𝕜, dual(MLF₁) ⊗ MLF₁)) (IB.prod 𝓘(𝕜, MLF₁ ⊗ dual(MLF₁))) n
    --
    -- (5) (contract_tensorDual_bundleHom n).contMDiff_toFun :
    --     ContMDiff (IB.prod 𝓘(𝕜, MLF₁ ⊗ dual(MLF₁))) (IB.prod 𝓘(𝕜, 𝕜)) n
    --
    -- Composition: (5) ∘ (4) ∘ (3) ∘ (2) ∘ (1) gives ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜)) n.
    -- Extract scalar via (contMDiffAt_section x₀).mp.
    --
    -- Currently blocked by an AddCommMonoid instance diamond on the intermediate
    -- tensor product model fibers: `ContinuousMultilinearMap.addCommMonoid` vs
    -- `NormedAddCommGroup.toAddCommMonoid`. These are propositionally but not
    -- definitionally equal, preventing Lean from composing (2) with (3).
    sorry⟩

end MixedSection

end
