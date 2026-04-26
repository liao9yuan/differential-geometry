/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Product.Fiber
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.VectorBundle.Dual
import DifferentialGeometry.VectorBundle.Equiv

/-!
# Contraction on the tensor product `dual(E) ⊗ E`

The evaluation pairing `f ⊗ v ↦ f(v)` gives a contraction map on the tensor product
of the dual bundle `Bundle.dual 𝕜 E` with a vector bundle `E`. This is the `V* ⊗ V`
contraction, which aligns with Mathlib's `contractLeft` and `dualTensorHomEquiv`.

## Main Definitions

* `evalDualTensorLM` : the evaluation pairing on the model fiber
  `(F →L[𝕜] 𝕜) ⊗[𝕜] F →ₗ[𝕜] 𝕜`, sending `f ⊗ₜ v ↦ f(v)`.
* `evalDualTensorCLM` : the evaluation pairing promoted to a continuous linear map.
* `contract_dualTensor` : fiberwise contraction on `(dual E x) ⊗ E x →L[𝕜] 𝕜`,
  defined by composing `evalDualTensorCLM` with the CLE to the model fiber.

## Tags

contraction, evaluation pairing, tensor product, dual bundle, vector bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap TensorProduct

open scoped Manifold Topology Bundle ContDiff BigOperators

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The normed group on the model-fiber tensor product `(F →L[𝕜] 𝕜) ⊗[𝕜] F`. -/
local instance : NormedAddCommGroup ((F →L[𝕜] 𝕜) ⊗[𝕜] F) :=
  instNormedAddCommGroup_tensor 𝕜 (F →L[𝕜] 𝕜) F

local instance : NormedSpace 𝕜 ((F →L[𝕜] 𝕜) ⊗[𝕜] F) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F →L[𝕜] 𝕜) (F₂ := F)

/-!
## Evaluation pairing on the model fiber
-/

/-- The evaluation pairing on the model fiber `(F →L[𝕜] 𝕜) ⊗[𝕜] F →ₗ[𝕜] 𝕜`:
on pure tensors, `f ⊗ₜ v ↦ f(v)`. -/
noncomputable def evalDualTensorLM :
    (F →L[𝕜] 𝕜) ⊗[𝕜] F →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift {
    toFun := fun f => {
      toFun := fun v => f v
      map_add' := fun v₁ v₂ => map_add f v₁ v₂
      map_smul' := fun c v => map_smul f c v
    }
    map_add' := fun f₁ f₂ => by ext v; exact ContinuousLinearMap.add_apply f₁ f₂ v
    map_smul' := fun c f => by ext v; exact ContinuousLinearMap.smul_apply c f v
  }

@[simp]
theorem evalDualTensorLM_tmul (f : F →L[𝕜] 𝕜) (v : F) :
    evalDualTensorLM 𝕜 F (f ⊗ₜ v) = f v := rfl

/-- The evaluation pairing as a continuous linear map, promoted from `evalDualTensorLM`
via finite-dimensionality of `(F →L[𝕜] 𝕜) ⊗[𝕜] F`. -/
noncomputable def evalDualTensorCLM :
    (F →L[𝕜] 𝕜) ⊗[𝕜] F →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap (evalDualTensorLM 𝕜 F)

@[simp]
theorem evalDualTensorCLM_tmul (f : F →L[𝕜] 𝕜) (v : F) :
    evalDualTensorCLM 𝕜 F (f ⊗ₜ v) = f v := rfl

/-!
## Naturality of the evaluation pairing

The evaluation pairing is invariant under the tensor product coordinate change
`TensorProduct.map (· ∘ Φ⁻¹) Φ` induced by a linear automorphism `Φ` of the model
fiber. This is the key ingredient for trivialization-independence of the contraction.
-/

/-- The evaluation pairing is natural on pure tensors: for any CLE `Φ : F ≃L[𝕜] F`,
`eval((f ∘ Φ⁻¹) ⊗ₜ (Φ v)) = eval(f ⊗ₜ v)`. -/
theorem evalDualTensorLM_comp_symm (Φ : F ≃L[𝕜] F)
    (f : F →L[𝕜] 𝕜) (v : F) :
    evalDualTensorLM 𝕜 F (f.comp Φ.symm.toContinuousLinearMap ⊗ₜ Φ v) =
      evalDualTensorLM 𝕜 F (f ⊗ₜ v) := by
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The linear map `f ↦ f ∘ Φ⁻¹` on the continuous dual, induced by a CLE `Φ`. -/
noncomputable def precompSymmLM (Φ : F ≃L[𝕜] F) :
    (F →L[𝕜] 𝕜) →ₗ[𝕜] (F →L[𝕜] 𝕜) where
  toFun f := f.comp Φ.symm.toContinuousLinearMap
  map_add' f g := by ext; simp [ContinuousLinearMap.add_apply]
  map_smul' c f := by ext; simp [ContinuousLinearMap.smul_apply]

/-- Full naturality: the evaluation pairing is invariant under the tensor product
coordinate change `TensorProduct.map (· ∘ Φ⁻¹) Φ` for any CLE `Φ : F ≃L[𝕜] F`. -/
theorem evalDualTensorLM_map_natural (Φ : F ≃L[𝕜] F) (t : (F →L[𝕜] 𝕜) ⊗[𝕜] F) :
    evalDualTensorLM 𝕜 F
      (TensorProduct.map (precompSymmLM 𝕜 F Φ) Φ.toLinearEquiv.toLinearMap t) =
    evalDualTensorLM 𝕜 F t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul f v =>
    rw [TensorProduct.map_tmul]
    exact evalDualTensorLM_comp_symm 𝕜 F Φ f v
  | add t₁ t₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]

/-!
## Fiberwise contraction
-/

variable {𝕜 F}
variable {B : Type*} [TopologicalSpace B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Fiberwise contraction on the tensor product `(dual E x) ⊗ E x`, sending
`f ⊗ v ↦ f(v)`. Defined by composing the evaluation CLM on the model fiber with the
CLE to the model fiber from `Bundle.TensorProduct.continuousLinearEquivAt`. -/
noncomputable def contract_dualTensor (x : B) :
    letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E) E x
    Bundle.dual 𝕜 E x ⊗[𝕜] E x →L[𝕜] 𝕜 := by
  letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E) E x
  exact (evalDualTensorCLM 𝕜 F).comp
    (Bundle.TensorProduct.continuousLinearEquivAt 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E)
      E x).toContinuousLinearMap

/-!
## Smooth bundle homomorphism

The contraction `contract_dualTensor` assembles into a `ContMDiffVectorBundleHom` from
`dual(E) ⊗ E` to the trivial `𝕜`-bundle. In any local trivialization, the total-space
map reduces to `(x, t) ↦ (x, evalDualTensorCLM t)` by `evalDualTensorLM_map_natural`,
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

local instance : NormedAddCommGroup ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') :=
  instNormedAddCommGroup_tensor 𝕜' (F' →L[𝕜'] 𝕜') F'
local instance : NormedSpace 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') :=
  instNormedSpace_tensor (𝕜 := 𝕜') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')

/-- The dual bundle trivialization is contragredient to the base bundle: evaluating
the trivialized covector at the trivialized vector recovers the original pairing.
This is the key naturality fact: `(L₂ f)(L₁ v) = f(v)` where `L₂ f = f ∘ L₁⁻¹`. -/
private theorem eval_dual_cLMA (y x : B')
    (hx : x ∈ (trivializationAt F' E' y).baseSet)
    (f : E' x →L[𝕜'] 𝕜') (v : E' x) :
    ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).continuousLinearMapAt
      𝕜' x f)
    ((trivializationAt F' E' y).continuousLinearMapAt 𝕜' x v) = f v := by
  have hx_dual : x ∈ (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).baseSet := by
    simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap]
    exact ⟨hx, Set.mem_univ x⟩
  have hx_triv : x ∈ (trivializationAt 𝕜' (Bundle.Trivial B' 𝕜') y).baseSet :=
    Set.mem_univ x
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hx_dual,
    Trivialization.coe_linearMapAt_of_mem _ hx,
    hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates_eq hx hx_triv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply]
  change f ((trivializationAt F' E' y).continuousLinearEquivAt 𝕜' x hx |>.symm
    ((trivializationAt F' E' y ⟨x, v⟩).2)) = f v
  exact congrArg f (ContinuousLinearEquiv.symm_apply_apply _ v)

/-- Variant of `eval_dual_cLMA` using `continuousLinearEquivAt` (via `toLinearEquiv`)
instead of `continuousLinearMapAt`. Needed because `TensorProduct.congr_tmul` produces
`CLE.toLinearEquiv` coercions. -/
private theorem eval_dual_CLE (y x : B')
    (hx : x ∈ (trivializationAt F' E' y).baseSet)
    (hx_dual : x ∈ (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).baseSet)
    (f : E' x →L[𝕜'] 𝕜') (v : E' x) :
    (((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).continuousLinearEquivAt
      𝕜' x hx_dual).toLinearEquiv f)
    (((trivializationAt F' E' y).continuousLinearEquivAt 𝕜' x hx).toLinearEquiv v) = f v := by
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
    (trivializationAt F' E' y).coe_continuousLinearEquivAt_eq hx,
    (trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') y).coe_continuousLinearEquivAt_eq
      hx_dual]
  exact eval_dual_cLMA y x hx f v

/-- Trivialization compatibility: applying `evalDualTensorCLM` after the tensor
product trivialization at `x₀` agrees with `contract_dualTensor` at any `x` in the
base set. Both equal the evaluation pairing by `eval_dual_cLMA`. -/
private theorem contract_triv_compat (x₀ x : B')
    (hx : x ∈ (trivializationAt F' E' x₀).baseSet)
    (t : Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :
    contract_dualTensor (𝕜 := 𝕜') (F := F') x t =
    evalDualTensorCLM 𝕜' F'
      (TensorProduct.map
        ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') x₀).continuousLinearMapAt
          𝕜' x).toLinearMap
        ((trivializationAt F' E' x₀).continuousLinearMapAt 𝕜' x).toLinearMap
        t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | add t₁ t₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | tmul f v =>
    simp only [TensorProduct.map_tmul, evalDualTensorCLM_tmul]
    trans (f v)
    · simp only [contract_dualTensor, ContinuousLinearMap.comp_apply]
      change (fun t => evalDualTensorCLM 𝕜' F' (TensorProduct.congr
        ((trivializationAt (F' →L[𝕜'] 𝕜') (Bundle.dual 𝕜' E') x).continuousLinearEquivAt 𝕜' x
          (by simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap];
              exact ⟨mem_baseSet_trivializationAt F' E' x, Set.mem_univ x⟩)).toLinearEquiv
        ((trivializationAt F' E' x).continuousLinearEquivAt 𝕜' x
          (mem_baseSet_trivializationAt F' E' x)).toLinearEquiv
        t)) (f ⊗ₜ[𝕜'] v) = f v
      simp only [TensorProduct.congr_tmul, evalDualTensorCLM_tmul]
      exact eval_dual_CLE x x (mem_baseSet_trivializationAt F' E' x)
        (by simp only [hom_trivializationAt, Trivialization.baseSet_continuousLinearMap];
            exact ⟨mem_baseSet_trivializationAt F' E' x, Set.mem_univ x⟩) f v
    · exact (eval_dual_cLMA x₀ x hx f v).symm

-- TODO: The tensor product bundle is built via `VectorPrebundle`, adding layers of
-- definitional indirection that make `whnf`/`isDefEq` expensive. Refactoring
-- `Bundle.TensorProduct` to provide direct `FiberBundle`/`VectorBundle` instances
-- (as Mathlib does for the hom bundle) would eliminate the extra heartbeats here
-- and in all downstream tensor product bundle proofs.
set_option maxHeartbeats 400000 in
/-- The total-space map `(x, t) ↦ (x, contract_dualTensor x t)` is `C^n`. -/
private theorem contract_dualTensor_totalSpace_smooth :
    letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F' (Bundle.dual 𝕜' E') E' x
    letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
        (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
    letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
        (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
        (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
    ContMDiff
      (IB.prod 𝓘(𝕜', (F' →L[𝕜'] 𝕜') ⊗[𝕜'] F'))
      (IB.prod 𝓘(𝕜', 𝕜'))
      n
      (fun p : TotalSpace ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
          (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) =>
        (⟨_root_.id p.1, (contract_dualTensor (𝕜 := 𝕜') (F := F') p.1).toLinearMap p.2⟩ :
          TotalSpace 𝕜' (Bundle.Trivial B' 𝕜'))) := by
  letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F' (Bundle.dual 𝕜' E') E' x
  letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
      (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜', (F' →L[𝕜'] 𝕜') ⊗[𝕜'] F'))
        𝓘(𝕜', (F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') n
        (fun p => (trivializationAt ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
          (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) p₀.proj p).2)
        p₀ :=
    (contMDiffAt_totalSpace.mp contMDiffAt_id).2
  refine ((contMDiffAt_const (c := evalDualTensorCLM 𝕜' F')).clm_apply
      h_fiber).congr_of_eventuallyEq ?_
  filter_upwards [
    ((trivializationAt F' E' p₀.proj).open_baseSet.preimage
      (FiberBundle.continuous_proj _ _)).mem_nhds
      (mem_baseSet_trivializationAt F' E' p₀.proj)
  ] with p hp
  simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
    Trivialization.tensorProduct_apply, _root_.id]
  change contract_dualTensor (𝕜 := 𝕜') (F := F') p.proj p.snd = _
  exact contract_triv_compat p₀.proj p.proj hp p.snd

set_option maxHeartbeats 400000 in
/-- The contraction `f ⊗ v ↦ f(v)` as a `C^n` vector bundle homomorphism from the tensor
product bundle `dual(E) ⊗ E` to the trivial `𝕜`-bundle. -/
noncomputable def contract_dualTensor_bundleHom :
    letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F' (Bundle.dual 𝕜' E') E' x
    letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.fiberBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
        (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
    letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
        (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
      Bundle.TensorProduct.vectorBundle
        (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
        (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
    ContMDiffVectorBundleHom 𝕜' IB n
      ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x)
      𝕜' (Bundle.Trivial B' 𝕜') :=
  letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F' (Bundle.dual 𝕜' E') E' x
  letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
      (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  { baseMap := _root_.id
    toFun := fun p => ⟨p.1, (contract_dualTensor (𝕜 := 𝕜') (F := F') p.1).toLinearMap p.2⟩
    contMDiff_toFun := contract_dualTensor_totalSpace_smooth n
    fiberLinearMap := fun x => (contract_dualTensor (𝕜 := 𝕜') (F := F') x).toLinearMap
    fiber_compat := fun _ _ => rfl }

/-!
## Contraction of smooth sections
-/

set_option maxHeartbeats 400000 in
/-- Contraction of a smooth section of `dual(E) ⊗ E` yields a smooth scalar function.
Constructed by composing the bundle hom's smooth total-space map with the section. -/
noncomputable def contract_section
    (σ : letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
            Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F'
              (Bundle.dual 𝕜' E') E' x
         letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
            (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
            Bundle.TensorProduct.fiberBundle
              (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
              (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
         letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
            (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
            Bundle.TensorProduct.vectorBundle
              (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
              (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
         ContMDiffSection IB ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') n
            (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x)) :
    C^n⟮IB, B'; 𝓘(𝕜'), 𝕜'⟯ := by
  letI (x : B') : TopologicalSpace (Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜' (F' →L[𝕜'] 𝕜') F' (Bundle.dual 𝕜' E') E' x
  letI : FiberBundle ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F') (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  letI : VectorBundle 𝕜' ((F' →L[𝕜'] 𝕜') ⊗[𝕜'] F')
      (fun x => Bundle.dual 𝕜' E' x ⊗[𝕜'] E' x) :=
    Bundle.TensorProduct.vectorBundle
      (𝕜 := 𝕜') (B := B') (F₁ := F' →L[𝕜'] 𝕜') (F₂ := F')
      (E₁ := Bundle.dual 𝕜' E') (E₂ := E')
  have h_comp := (contract_dualTensor_bundleHom n).contMDiff_toFun.comp σ.contMDiff
  exact ⟨fun x => contract_dualTensor (𝕜 := 𝕜') (F := F') x (σ x),
    fun x₀ => (Bundle.contMDiffAt_section x₀).mp h_comp.contMDiffAt⟩

end BundleHom

end
