/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Product.Fiber
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.VectorBundle.Dual
import DifferentialGeometry.VectorBundle.Equiv

/-!
# Contraction on the tensor product `E ⊗ dual(E)`

The evaluation pairing `v ⊗ f ↦ f(v)` gives a contraction map on the tensor product
of a vector bundle `E` with its dual bundle `Bundle.dual 𝕜 E`. This is the `V ⊗ V*`
counterpart of the mixed `(1,1)`-contraction defined via `MixedSection.contract_11`
in `Tensor/Mixed/Contract.lean`.

## Main Definitions

* `evalTensorDualLM` : the evaluation pairing on the model fiber
  `F ⊗[𝕜] (F →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜`, sending `v ⊗ₜ f ↦ f(v)`.
* `evalTensorDualCLM` : the evaluation pairing promoted to a continuous linear map.
* `contract_tensorDual` : fiberwise contraction on `E x ⊗ (dual E x) →L[𝕜] 𝕜`,
  defined by composing `evalTensorDualCLM` with the CLE to the model fiber.

## Tags

contraction, evaluation pairing, tensor product, dual bundle, vector bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap TensorProduct

open scoped Manifold Topology Bundle ContDiff BigOperators

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The normed group on the model-fiber tensor product `F ⊗[𝕜] (F →L[𝕜] 𝕜)`. -/
local instance : NormedAddCommGroup (F ⊗[𝕜] (F →L[𝕜] 𝕜)) :=
  instNormedAddCommGroup_tensor 𝕜 F (F →L[𝕜] 𝕜)

local instance : NormedSpace 𝕜 (F ⊗[𝕜] (F →L[𝕜] 𝕜)) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F) (F₂ := F →L[𝕜] 𝕜)

/-!
## Evaluation pairing on the model fiber
-/

/-- The evaluation pairing on the model fiber `F ⊗[𝕜] (F →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜`:
on pure tensors, `v ⊗ₜ f ↦ f(v)`. -/
noncomputable def evalTensorDualLM :
    F ⊗[𝕜] (F →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift {
    toFun := fun v => {
      toFun := fun f => f v
      map_add' := fun f₁ f₂ => ContinuousLinearMap.add_apply f₁ f₂ v
      map_smul' := fun c f => ContinuousLinearMap.smul_apply c f v
    }
    map_add' := fun v₁ v₂ => by ext f; exact map_add f v₁ v₂
    map_smul' := fun c v => by ext f; exact map_smul f c v
  }

@[simp]
theorem evalTensorDualLM_tmul (v : F) (f : F →L[𝕜] 𝕜) :
    evalTensorDualLM 𝕜 F (v ⊗ₜ f) = f v := rfl

/-- The evaluation pairing as a continuous linear map, promoted from `evalTensorDualLM`
via finite-dimensionality of `F ⊗[𝕜] (F →L[𝕜] 𝕜)`. -/
noncomputable def evalTensorDualCLM :
    F ⊗[𝕜] (F →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap (evalTensorDualLM 𝕜 F)

@[simp]
theorem evalTensorDualCLM_tmul (v : F) (f : F →L[𝕜] 𝕜) :
    evalTensorDualCLM 𝕜 F (v ⊗ₜ f) = f v := rfl

/-!
## Naturality of the evaluation pairing

The evaluation pairing is invariant under the tensor product coordinate change
`TensorProduct.map Φ (· ∘ Φ⁻¹)` induced by a linear automorphism `Φ` of the model
fiber. This is the key ingredient for trivialization-independence of the contraction.
-/

/-- The evaluation pairing is natural on pure tensors: for any CLE `Φ : F ≃L[𝕜] F`,
`eval(Φ v ⊗ₜ (f ∘ Φ⁻¹)) = eval(v ⊗ₜ f)`. -/
theorem evalTensorDualLM_comp_symm (Φ : F ≃L[𝕜] F)
    (v : F) (f : F →L[𝕜] 𝕜) :
    evalTensorDualLM 𝕜 F (Φ v ⊗ₜ (f.comp Φ.symm.toContinuousLinearMap)) =
      evalTensorDualLM 𝕜 F (v ⊗ₜ f) := by
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The linear map `f ↦ f ∘ Φ⁻¹` on the continuous dual, induced by a CLE `Φ`. -/
noncomputable def precompSymmLM (Φ : F ≃L[𝕜] F) :
    (F →L[𝕜] 𝕜) →ₗ[𝕜] (F →L[𝕜] 𝕜) where
  toFun f := f.comp Φ.symm.toContinuousLinearMap
  map_add' f g := by ext; simp [ContinuousLinearMap.add_apply]
  map_smul' c f := by ext; simp [ContinuousLinearMap.smul_apply]

/-- Full naturality: the evaluation pairing is invariant under the tensor product
coordinate change `TensorProduct.map Φ (· ∘ Φ⁻¹)` for any CLE `Φ : F ≃L[𝕜] F`. -/
theorem evalTensorDualLM_map_natural (Φ : F ≃L[𝕜] F) (t : F ⊗[𝕜] (F →L[𝕜] 𝕜)) :
    evalTensorDualLM 𝕜 F
      (TensorProduct.map Φ.toLinearEquiv.toLinearMap (precompSymmLM 𝕜 F Φ) t) =
    evalTensorDualLM 𝕜 F t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul v f =>
    rw [TensorProduct.map_tmul]
    exact evalTensorDualLM_comp_symm 𝕜 F Φ v f
  | add t₁ t₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]

/-!
## Fiberwise contraction
-/

variable {𝕜 F}
variable {B : Type*} [TopologicalSpace B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Fiberwise contraction on the tensor product `E x ⊗ (dual E x)`, sending
`v ⊗ f ↦ f(v)`. Defined by composing the evaluation CLM on the model fiber with the
CLE to the model fiber from `Bundle.TensorProduct.continuousLinearEquivAt`. -/
noncomputable def contract_tensorDual (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 F (F →L[𝕜] 𝕜) E (Bundle.dual 𝕜 E) x
    E x ⊗[𝕜] Bundle.dual 𝕜 E x →L[𝕜] 𝕜 := by
  letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 F (F →L[𝕜] 𝕜) E (Bundle.dual 𝕜 E) x
  exact (evalTensorDualCLM 𝕜 F).comp
    (Bundle.TensorProduct.continuousLinearEquivAt 𝕜 F (F →L[𝕜] 𝕜) E
      (Bundle.dual 𝕜 E) x).toContinuousLinearMap

/-!
## Smooth bundle homomorphism

The contraction `contract_tensorDual` assembles into a `ContMDiffVectorBundleHom` from
`E ⊗ dual(E)` to the trivial `𝕜`-bundle. In any local trivialization, the total-space
map reduces to `(x, t) ↦ (x, evalTensorDualCLM t)` by `evalTensorDualLM_map_natural`,
which is manifestly smooth.
-/

section BundleHom

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [CompleteSpace 𝕜']
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜' EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜' EB HB}
variable {B' : Type*} [TopologicalSpace B'] [ChartedSpace HB B']
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] [FiniteDimensional 𝕜' F']
variable {E' : B' → Type*} [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace 𝕜' (E' x)]
  [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle 𝕜' F' E']
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F' E' IB]

local instance : NormedAddCommGroup (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) :=
  instNormedAddCommGroup_tensor 𝕜' F' (F' →L[𝕜'] 𝕜')
local instance : NormedSpace 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) :=
  instNormedSpace_tensor (𝕜 := 𝕜') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')

/-- The dual bundle trivialization is contragredient to the base bundle: evaluating
the trivialized covector at the trivialized vector recovers the original pairing.
This is the key naturality fact: `(L₂ f)(L₁ v) = f(v)` where `L₂ f = f ∘ L₁⁻¹`. -/
private theorem eval_dual_cLMA (y x : B')
    (hx : x ∈ (trivializationAt F' E' y).baseSet)
    (v : E' x) (f : E' x →L[𝕜'] 𝕜') :
    ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).continuousLinearMapAt
      𝕜' x f)
    ((trivializationAt F' E' y).continuousLinearMapAt 𝕜' x v) = f v := by
  -- The dual bundle trivialization maps f ↦ triv_out.cLMA ∘ f ∘ triv_E.symmL.
  -- For trivial codomain triv_out.cLMA = id. So (f ∘ symmL)(cLMA v) = f v.
  have hx_dual : x ∈ (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).baseSet := by
    simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap]
    exact ⟨hx, Set.mem_univ x⟩
  -- Unfold cLMAs, expand hom triv via inCoordinates_eq (in terms of CLEs),
  -- simplify trivial bundle CLE to refl, and use symm_apply_apply.
  have hx_triv : x ∈ (trivializationAt 𝕜' (Bundle.Trivial B' 𝕜') y).baseSet :=
    Set.mem_univ x
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hx_dual,
    Trivialization.coe_linearMapAt_of_mem _ hx,
    hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates_eq hx hx_triv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply]
  -- Remaining: (triv_trivial ⟨x, f (CLE_E.symm ((triv_E ⟨x, v⟩).2))⟩).2 = f v
  -- For the trivial bundle, (triv ⟨x, c⟩).2 = c (the trivialization is the identity)
  -- and CLE_E.symm ((triv_E ⟨x, v⟩).2) = CLE_E.symm (CLE_E v) = v
  change f ((trivializationAt F' E' y).continuousLinearEquivAt 𝕜' x hx |>.symm
    ((trivializationAt F' E' y ⟨x, v⟩).2)) = f v
  -- Goal: f (CLE.symm ((e ⟨x, v⟩).2)) = f v
  -- Since CLE.toFun = fun v => (e ⟨x, v⟩).2 definitionally,
  -- CLE.symm ((e ⟨x, v⟩).2) = CLE.symm (CLE v) = v
  exact congrArg f (ContinuousLinearEquiv.symm_apply_apply _ v)

/-- Variant of `eval_dual_cLMA` using `continuousLinearEquivAt` (via `toLinearEquiv`)
instead of `continuousLinearMapAt`. Needed because `TensorProduct.congr_tmul` produces
`CLE.toLinearEquiv` coercions. -/
private theorem eval_dual_CLE (y x : B')
    (hx : x ∈ (trivializationAt F' E' y).baseSet)
    (hx_dual : x ∈ (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).baseSet)
    (v : E' x) (f : E' x →L[𝕜'] 𝕜') :
    (((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).continuousLinearEquivAt
      𝕜' x hx_dual).toLinearEquiv f)
    (((trivializationAt F' E' y).continuousLinearEquivAt 𝕜' x hx).toLinearEquiv v) = f v := by
  -- CLE.toLinearEquiv coerces identically to cLMA at baseSet points
  -- Bridge CLE.toLinearEquiv → CLE → cLMA coercions
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
    (trivializationAt F' E' y).coe_continuousLinearEquivAt_eq hx,
    (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).coe_continuousLinearEquivAt_eq
      hx_dual]
  exact eval_dual_cLMA y x hx v f

/-- Trivialization compatibility: applying `evalTensorDualCLM` after the tensor
product trivialization at `x₀` agrees with `contract_tensorDual` at any `x` in the
base set. Both equal the evaluation pairing by `eval_dual_cLMA`. -/
private theorem contract_triv_compat (x₀ x : B')
    (hx : x ∈ (trivializationAt F' E' x₀).baseSet)
    (t : E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :
    contract_tensorDual (𝕜 := 𝕜') (F := F') x t =
    evalTensorDualCLM 𝕜' F'
      (TensorProduct.map
        ((trivializationAt F' E' x₀).continuousLinearMapAt 𝕜' x).toLinearMap
        ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') x₀).continuousLinearMapAt
          𝕜' x).toLinearMap
        t) := by
  -- Both sides are linear in t, so it suffices to check on pure tensors
  induction t using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | add t₁ t₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | tmul v f =>
    simp only [TensorProduct.map_tmul, evalTensorDualCLM_tmul]
    -- Goal: contract_tensorDual x (v ⊗ₜ f) = (dual_cLMA f)(E_cLMA v)
    -- Both sides equal f v by eval_dual_cLMA (at different trivialization points).
    -- LHS: contract_tensorDual = evalTensorDualCLM ∘ CLE_x, and CLE_x on pure tensors
    -- is definitionally (CLE_E v) ⊗ₜ (CLE_dual f) via TensorProduct.congr.
    -- Since CLE = cLMA at baseSet, this is (cLMA_x f)(cLMA_x v) = f v.
    -- RHS: (cLMA_x₀ f)(cLMA_x₀ v) = f v.
    trans (f v)
    · -- Unfold contract_tensorDual to evalTensorDualCLM ∘ CLE_x
      -- CLE_x on pure tensors is (CLE_E v) ⊗ₜ (CLE_dual f) (definitional via TensorProduct.congr)
      -- evalTensorDualCLM then gives (CLE_dual f)(CLE_E v) = (cLMA f)(cLMA v) = f v
      simp only [contract_tensorDual, ContinuousLinearMap.comp_apply]
      -- Goal: evalTensorDualCLM (CLE_x (v ⊗ₜ f)) = f v
      -- CLE_x wraps TensorProduct.congr, so unfold on pure tensors:
      -- CLE_x is built from TensorProduct.congr via the private trivEquiv.
      -- On pure tensors, congr maps v ⊗ₜ f ↦ (e₁ v) ⊗ₜ (e₂ f), which is rfl.
      -- After evalTensorDualCLM_tmul, the goal becomes (e₂ f)(e₁ v) = f v,
      -- which is eval_dual_cLMA.
      change (fun t => evalTensorDualCLM 𝕜' F' (TensorProduct.congr
        ((trivializationAt F' E' x).continuousLinearEquivAt 𝕜' x
          (mem_baseSet_trivializationAt F' E' x)).toLinearEquiv
        ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') x).continuousLinearEquivAt 𝕜' x
          (by simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap];
              exact ⟨mem_baseSet_trivializationAt F' E' x, Set.mem_univ x⟩)).toLinearEquiv
        t)) (v ⊗ₜ[𝕜'] f) = f v
      simp only [TensorProduct.congr_tmul, evalTensorDualCLM_tmul]
      -- Goal: (CLE_dual.toLinearEquiv f)(CLE_E.toLinearEquiv v) = f v
      exact eval_dual_CLE x x (mem_baseSet_trivializationAt F' E' x)
        (by simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap];
            exact ⟨mem_baseSet_trivializationAt F' E' x, Set.mem_univ x⟩) v f
    · exact (eval_dual_cLMA x₀ x hx v f).symm

-- TODO: The tensor product bundle is built via `VectorPrebundle`, adding layers of
-- definitional indirection that make `whnf`/`isDefEq` expensive. Refactoring
-- `Bundle.TensorProduct` to provide direct `FiberBundle`/`VectorBundle` instances
-- (as Mathlib does for the hom bundle) would eliminate the extra heartbeats here
-- and in all downstream tensor product bundle proofs.
set_option maxHeartbeats 400000 in
/-- The total-space map `(x, t) ↦ (x, contract_tensorDual x t)` is `C^n`. -/
private theorem contract_tensorDual_totalSpace_smooth :
    letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜') E' (Bundle.dual 𝕜' E') x
    letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
        (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
    letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
        (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
        (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
    ContMDiff
      (IB.prod 𝓘(𝕜', F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')))
      (IB.prod 𝓘(𝕜', 𝕜'))
      n
      (fun p : TotalSpace (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
          (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) =>
        (⟨_root_.id p.1, (contract_tensorDual (𝕜 := 𝕜') (F := F') p.1).toLinearMap p.2⟩ :
          TotalSpace 𝕜' (Bundle.Trivial B' 𝕜'))) := by
  letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜') E' (Bundle.dual 𝕜' E') x
  letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
      (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜', F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')))
        𝓘(𝕜', F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) n
        (fun p => (trivializationAt (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
          (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) p₀.proj p).2)
        p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := evalTensorDualCLM 𝕜' F')).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F' E' p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F' E' p₀.proj)
  ] with p hp
  simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
    Trivialization.tensorProduct_apply, _root_.id]
  change contract_tensorDual (𝕜 := 𝕜') (F := F') p.proj p.snd = _
  exact contract_triv_compat p₀.proj p.proj hp p.snd

set_option maxHeartbeats 400000 in
/-- The contraction `v ⊗ f ↦ f(v)` as a `C^n` vector bundle homomorphism from the tensor
product bundle `E ⊗ dual(E)` to the trivial `𝕜`-bundle. -/
noncomputable def contract_tensorDual_bundleHom :
    letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜') E' (Bundle.dual 𝕜' E') x
    letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
        (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
    letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
        (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
        (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
    ContMDiffVectorBundleHom 𝕜' IB n
      (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x)
      𝕜' (Bundle.Trivial B' 𝕜') :=
  letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜') E' (Bundle.dual 𝕜' E') x
  letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
      (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  { baseMap := _root_.id
    toFun := fun p => ⟨p.1, (contract_tensorDual (𝕜 := 𝕜') (F := F') p.1).toLinearMap p.2⟩
    contMDiff_toFun := contract_tensorDual_totalSpace_smooth n
    fiberLinearMap := fun x => (contract_tensorDual (𝕜 := 𝕜') (F := F') x).toLinearMap
    fiber_compat := fun _ _ => rfl }

/-!
## Contraction of smooth sections
-/

set_option maxHeartbeats 400000 in
/-- Contraction of a smooth section of `E ⊗ dual(E)` yields a smooth scalar function.
Constructed by composing the bundle hom's smooth total-space map with the section. -/
noncomputable def contract_section
    (σ : letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
            Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜')
              E' (Bundle.dual 𝕜' E') x
         letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
            (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
            Bundle.TensorProduct.fiberBundle
              (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
              (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
         letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
            (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
            Bundle.TensorProduct.vectorBundle
              (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
              (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
         ContMDiffSection IB (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) n
            (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x)) :
    C^n⟮IB, B'; 𝓘(𝕜'), 𝕜'⟯ := by
  letI (x : B') : TopologicalSpace (E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' F' (F' →L[𝕜'] 𝕜') E' (Bundle.dual 𝕜' E') x
  letI : FiberBundle (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜')) (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  letI : VectorBundle 𝕜' (F' ⊗[𝕜'] (F' →L[𝕜'] 𝕜'))
      (fun x => E' x ⊗[𝕜'] Bundle.dual 𝕜' E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F') (F₂ := F' →L[𝕜'] 𝕜')
      (E₁ := E') (E₂ := Bundle.dual 𝕜' E')
  -- The composition bundleHom.toFun ∘ σ is smooth into the trivial bundle total space.
  -- Extract the scalar component via contMDiffAt_section (trivial bundle triv = id).
  have h_comp := (contract_tensorDual_bundleHom n).contMDiff_toFun.comp σ.contMDiff
  exact ⟨fun x => contract_tensorDual (𝕜 := 𝕜') (F := F') x (σ x),
    fun x₀ => (Bundle.contMDiffAt_section x₀).mp h_comp.contMDiffAt⟩

end BundleHom

end
