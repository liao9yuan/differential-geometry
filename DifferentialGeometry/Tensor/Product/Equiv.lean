/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.VectorBundle.Equiv

/-!
# Tensor product bundle equivalences

Smooth bundle equivalences for swapping tensor product factors and mapping on one factor.

## Main Definitions

* `tensorProductComm` : `E₁ ⊗ E₂ ≃ E₂ ⊗ E₁` as a smooth bundle equivalence.
* `tensorProductMapLeft` : given `E₁ ≃ E₃`, produce `E₁ ⊗ E₂ ≃ E₃ ⊗ E₂`.

## Tags

tensor product, vector bundle, equivalence, commutativity
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set TensorProduct

open scoped Manifold Topology Bundle ContDiff BigOperators

section TensorEquivs

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]

variable {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

local instance : NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
  instNormedAddCommGroup_tensor 𝕜 F₁ F₂
local instance : NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂)
local instance : NormedAddCommGroup (F₂ ⊗[𝕜] F₁) :=
  instNormedAddCommGroup_tensor 𝕜 F₂ F₁
local instance : NormedSpace 𝕜 (F₂ ⊗[𝕜] F₁) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₂) (F₂ := F₁)

/-- Smooth bundle equivalence swapping the factors of a tensor product bundle:
`E₁ ⊗ E₂ ≃ E₂ ⊗ E₁`. The fiberwise equivalence is `TensorProduct.comm`. -/
noncomputable def tensorProductComm :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI (x : B) : TopologicalSpace (E₂ x ⊗[𝕜] E₁ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₂ F₁ E₂ E₁ x
    letI : FiberBundle (F₂ ⊗[𝕜] F₁) (fun x => E₂ x ⊗[𝕜] E₁ x) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₂) (F₂ := F₁) (E₁ := E₂) (E₂ := E₁)
    letI : VectorBundle 𝕜 (F₂ ⊗[𝕜] F₁) (fun x => E₂ x ⊗[𝕜] E₁ x) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₂) (F₂ := F₁) (E₁ := E₂) (E₂ := E₁)
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x)
      (F₂ ⊗[𝕜] F₁) (fun x => E₂ x ⊗[𝕜] E₁ x) := by
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI (x : B) : TopologicalSpace (E₂ x ⊗[𝕜] E₁ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₂ F₁ E₂ E₁ x
  letI : FiberBundle (F₂ ⊗[𝕜] F₁) (fun x => E₂ x ⊗[𝕜] E₁ x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₂) (F₂ := F₁) (E₁ := E₂) (E₂ := E₁)
  letI : VectorBundle 𝕜 (F₂ ⊗[𝕜] F₁) (fun x => E₂ x ⊗[𝕜] E₁ x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₂) (F₂ := F₁) (E₁ := E₂) (E₂ := E₁)
  exact ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => TensorProduct.comm 𝕜 (E₁ x) (E₂ x))
    sorry -- smoothness of the forward map
    sorry -- smoothness of the inverse map

/-!
### Mapping one factor
-/

variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [FiniteDimensional 𝕜 F₃]
variable {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, ContinuousAdd (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  [ContMDiffVectorBundle n F₃ E₃ IB]

local instance : NormedAddCommGroup (F₃ ⊗[𝕜] F₂) :=
  instNormedAddCommGroup_tensor 𝕜 F₃ F₂
local instance : NormedSpace 𝕜 (F₃ ⊗[𝕜] F₂) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₃) (F₂ := F₂)

/-- Smooth bundle equivalence from mapping the first factor of a tensor product:
given a smooth bundle equivalence `E₁ ≃ E₃` covering `id`, produce
`E₁ ⊗ E₂ ≃ E₃ ⊗ E₂`. The fiberwise equivalence is `TensorProduct.congr`. -/
noncomputable def tensorProductMapLeft
    (e : ContMDiffVectorBundleEquiv 𝕜 IB n F₁ E₁ F₃ E₃)
    (hid : e.baseMap = _root_.id) :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    letI (x : B) : TopologicalSpace (E₃ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₃ F₂ E₃ E₂ x
    letI : FiberBundle (F₃ ⊗[𝕜] F₂) (fun x => E₃ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₃) (F₂ := F₂) (E₁ := E₃) (E₂ := E₂)
    letI : VectorBundle 𝕜 (F₃ ⊗[𝕜] F₂) (fun x => E₃ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₃) (F₂ := F₂) (E₁ := E₃) (E₂ := E₂)
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x)
      (F₃ ⊗[𝕜] F₂) (fun x => E₃ x ⊗[𝕜] E₂ x) := by
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  letI : FiberBundle (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI (x : B) : TopologicalSpace (E₃ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₃ F₂ E₃ E₂ x
  letI : FiberBundle (F₃ ⊗[𝕜] F₂) (fun x => E₃ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₃) (F₂ := F₂) (E₁ := E₃) (E₂ := E₂)
  letI : VectorBundle 𝕜 (F₃ ⊗[𝕜] F₂) (fun x => E₃ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₃) (F₂ := F₂) (E₁ := E₃) (E₂ := E₂)
  -- The fiberwise equivalence is `TensorProduct.congr (e.fiberLinearEquiv x) (refl)`,
  -- but casting `E₃ (e.baseMap x) = E₃ x` via `hid` involves dependent instance issues.
  -- The smoothness proofs are also sorry'd.
  sorry

/-!
### Associativity
-/

local instance : NormedAddCommGroup (F₁ ⊗[𝕜] F₃) :=
  instNormedAddCommGroup_tensor 𝕜 F₁ F₃
local instance : NormedSpace 𝕜 (F₁ ⊗[𝕜] F₃) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₃)
local instance : NormedAddCommGroup ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃) :=
  instNormedAddCommGroup_tensor 𝕜 (F₁ ⊗[𝕜] F₂) F₃
local instance : NormedSpace 𝕜 ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₁ ⊗[𝕜] F₂) (F₂ := F₃)
local instance : NormedAddCommGroup (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃)) :=
  instNormedAddCommGroup_tensor 𝕜 F₁ (F₂ ⊗[𝕜] F₃)
local instance : NormedSpace 𝕜 (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃)) :=
  instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂ ⊗[𝕜] F₃)

variable [ContMDiffVectorBundle n F₃ E₃ IB]

/-- Smooth bundle equivalence for associativity of the tensor product bundle:
`(E₁ ⊗ E₂) ⊗ E₃ ≃ E₁ ⊗ (E₂ ⊗ E₃)`. The fiberwise equivalence is
`TensorProduct.assoc`. -/
noncomputable def tensorProductAssoc :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    letI (x : B) : TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 (F₁ ⊗[𝕜] F₂) F₃
        (fun x => E₁ x ⊗[𝕜] E₂ x) E₃ x
    letI : FiberBundle ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃)
        (fun x => (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁ ⊗[𝕜] F₂) (F₂ := F₃)
        (E₁ := fun x => E₁ x ⊗[𝕜] E₂ x) (E₂ := E₃)
    letI : VectorBundle 𝕜 ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃)
        (fun x => (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁ ⊗[𝕜] F₂) (F₂ := F₃)
        (E₁ := fun x => E₁ x ⊗[𝕜] E₂ x) (E₂ := E₃)
    letI (x : B) : TopologicalSpace (E₂ x ⊗[𝕜] E₃ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₂ F₃ E₂ E₃ x
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ (F₂ ⊗[𝕜] F₃)
        E₁ (fun x => E₂ x ⊗[𝕜] E₃ x) x
    letI : FiberBundle (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃))
        (fun x => E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
      Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂ ⊗[𝕜] F₃)
        (E₁ := E₁) (E₂ := fun x => E₂ x ⊗[𝕜] E₃ x)
    letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃))
        (fun x => E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
      Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
        (F₁ := F₁) (F₂ := F₂ ⊗[𝕜] F₃)
        (E₁ := E₁) (E₂ := fun x => E₂ x ⊗[𝕜] E₃ x)
    ContMDiffVectorBundleEquiv 𝕜 IB n
      ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃) (fun x => (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x)
      (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃)) (fun x => E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) := by
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  letI (x : B) : TopologicalSpace ((E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 (F₁ ⊗[𝕜] F₂) F₃
      (fun x => E₁ x ⊗[𝕜] E₂ x) E₃ x
  letI : FiberBundle ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃)
      (fun x => (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁ ⊗[𝕜] F₂) (F₂ := F₃)
      (E₁ := fun x => E₁ x ⊗[𝕜] E₂ x) (E₂ := E₃)
  letI : VectorBundle 𝕜 ((F₁ ⊗[𝕜] F₂) ⊗[𝕜] F₃)
      (fun x => (E₁ x ⊗[𝕜] E₂ x) ⊗[𝕜] E₃ x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁ ⊗[𝕜] F₂) (F₂ := F₃)
      (E₁ := fun x => E₁ x ⊗[𝕜] E₂ x) (E₂ := E₃)
  letI (x : B) : TopologicalSpace (E₂ x ⊗[𝕜] E₃ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₂ F₃ E₂ E₃ x
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ (F₂ ⊗[𝕜] F₃)
      E₁ (fun x => E₂ x ⊗[𝕜] E₃ x) x
  letI : FiberBundle (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃))
      (fun x => E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂ ⊗[𝕜] F₃)
      (E₁ := E₁) (E₂ := fun x => E₂ x ⊗[𝕜] E₃ x)
  letI : VectorBundle 𝕜 (F₁ ⊗[𝕜] (F₂ ⊗[𝕜] F₃))
      (fun x => E₁ x ⊗[𝕜] (E₂ x ⊗[𝕜] E₃ x)) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F₁) (F₂ := F₂ ⊗[𝕜] F₃)
      (E₁ := E₁) (E₂ := fun x => E₂ x ⊗[𝕜] E₃ x)
  exact ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => TensorProduct.assoc 𝕜 (E₁ x) (E₂ x) (E₃ x))
    sorry -- smoothness of the forward map
    sorry -- smoothness of the inverse map

end TensorEquivs

end
