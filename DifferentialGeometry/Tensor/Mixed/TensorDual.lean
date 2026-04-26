/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Product
import DifferentialGeometry.Tensor.Multilinear.Covector
import DifferentialGeometry.Tensor.Product.Equiv
import DifferentialGeometry.VectorBundle.Dual

/-!
# The `Mixed 1 1` equivalence: `T¹₁(E) ≃ E* ⊗ E`

The mixed `(1,1)`-tensor bundle decomposes as `E* ⊗ E` via the composition:

  `T¹₁(E) ≃ T⁰₁(E*) ⊗ T⁰₁(E) ≃ E ⊗ T⁰₁(E) ≃ E ⊗ E* ≃ E* ⊗ E`

using `mixedBundle_tensorBundle_equiv`, `tensorProductMapLeft` (of the composite
`covectorBundle_equiv.trans doubleDualBundleEquiv`), `tensorProductMapRight`
(of `covectorBundle_equiv`), and `tensorProductComm`.

## Main Definitions

* `mixedOneOne_tensorDual_equiv` : the `C^n` vector bundle equivalence `T¹₁(E) ≃ E* ⊗ E`.

## Tags

mixed tensor, tensor product, dual bundle, vector bundle, equivalence
-/

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

section Mixed11

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

set_option backward.isDefEq.respectTransparency false

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

private abbrev MLF' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
-- The `trans` chain involves four intermediate tensor product bundles, each requiring
-- explicit instances to avoid diamonds with `instDT*` from `Mixed.Product`.
/-- The `C^n` vector bundle equivalence `T¹₁(E) ≃ E* ⊗ E`, composed as
`T¹₁(E) ≃ T⁰₁(E*) ⊗ T⁰₁(E) ≃ E ⊗ T⁰₁(E) ≃ E ⊗ E* ≃ E* ⊗ E`. -/
noncomputable def mixedOneOne_tensorDual_equiv :
    letI (x : B) : TopologicalSpace (Bundle.dual 𝕜 E x ⊗[𝕜] E x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E) E x
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF' 𝕜 F →L[𝕜] MLF' 𝕜 F)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 1 F E x)
      ((F →L[𝕜] 𝕜) ⊗[𝕜] F)
      (fun x => Bundle.dual 𝕜 E x ⊗[𝕜] E x) := by
  -- Abbreviations
  let ML1d := fun x : B => Bundle.continuousMultilinearMap 𝕜 1 (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x
  let ML1  := fun x : B => Bundle.continuousMultilinearMap 𝕜 1 F E x
  -- ── Model-fiber instances ──────────────────────────────────────────────────
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  haveI : FiniteDimensional 𝕜 (MLF' 𝕜 F) := continuousMultilinearMap_finiteDimensional 1
  haveI : FiniteDimensional 𝕜 (MLF' 𝕜 (F →L[𝕜] 𝕜)) := continuousMultilinearMap_finiteDimensional 1
  letI : NormedAddCommGroup (MLF' 𝕜 (F →L[𝕜] 𝕜) ⊗[𝕜] MLF' 𝕜 F) := instNormedAddCommGroup_tensor ..
  letI : NormedSpace 𝕜     (MLF' 𝕜 (F →L[𝕜] 𝕜) ⊗[𝕜] MLF' 𝕜 F) := instNormedSpace_tensor ..
  letI : NormedAddCommGroup (F ⊗[𝕜] MLF' 𝕜 F)     := instNormedAddCommGroup_tensor ..
  letI : NormedSpace 𝕜     (F ⊗[𝕜] MLF' 𝕜 F)     := instNormedSpace_tensor ..
  letI : NormedAddCommGroup (F ⊗[𝕜] (F →L[𝕜] 𝕜))  := instNormedAddCommGroup_tensor ..
  letI : NormedSpace 𝕜     (F ⊗[𝕜] (F →L[𝕜] 𝕜))  := instNormedSpace_tensor ..
  letI : NormedAddCommGroup ((F →L[𝕜] 𝕜) ⊗[𝕜] F)  := instNormedAddCommGroup_tensor ..
  letI : NormedSpace 𝕜     ((F →L[𝕜] 𝕜) ⊗[𝕜] F)  := instNormedSpace_tensor ..
  -- ── Tensor product bundle instances: E ⊗ T⁰₁(E) ──────────────────────────
  letI (x : B) : TopologicalSpace (E x ⊗[𝕜] ML1 x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F (MLF' 𝕜 F) E ML1 x
  letI : TopologicalSpace (TotalSpace (F ⊗[𝕜] MLF' 𝕜 F) (fun x => E x ⊗[𝕜] ML1 x)) :=
    Bundle.TensorProduct.tensorTotalSpaceTop (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := MLF' 𝕜 F) (E₁ := E) (E₂ := ML1)
  letI : FiberBundle (F ⊗[𝕜] MLF' 𝕜 F) (fun x => E x ⊗[𝕜] ML1 x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := MLF' 𝕜 F) (E₁ := E) (E₂ := ML1)
  letI : VectorBundle 𝕜 (F ⊗[𝕜] MLF' 𝕜 F) (fun x => E x ⊗[𝕜] ML1 x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := MLF' 𝕜 F) (E₁ := E) (E₂ := ML1)
  -- ── Tensor product bundle instances: E ⊗ E* ───────────────────────────────
  letI (x : B) : TopologicalSpace (E x ⊗[𝕜] Bundle.dual 𝕜 E x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F (F →L[𝕜] 𝕜) E (Bundle.dual 𝕜 E) x
  letI : TopologicalSpace (TotalSpace (F ⊗[𝕜] (F →L[𝕜] 𝕜)) (fun x => E x ⊗[𝕜] Bundle.dual 𝕜 E x)) :=
    Bundle.TensorProduct.tensorTotalSpaceTop (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := F →L[𝕜] 𝕜) (E₁ := E) (E₂ := Bundle.dual 𝕜 E)
  letI : FiberBundle (F ⊗[𝕜] (F →L[𝕜] 𝕜)) (fun x => E x ⊗[𝕜] Bundle.dual 𝕜 E x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := F →L[𝕜] 𝕜) (E₁ := E) (E₂ := Bundle.dual 𝕜 E)
  letI : VectorBundle 𝕜 (F ⊗[𝕜] (F →L[𝕜] 𝕜)) (fun x => E x ⊗[𝕜] Bundle.dual 𝕜 E x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F) (F₂ := F →L[𝕜] 𝕜) (E₁ := E) (E₂ := Bundle.dual 𝕜 E)
  -- ── Tensor product bundle instances: E* ⊗ E ───────────────────────────────
  letI (x : B) : TopologicalSpace (Bundle.dual 𝕜 E x ⊗[𝕜] E x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E) E x
  letI : TopologicalSpace (TotalSpace ((F →L[𝕜] 𝕜) ⊗[𝕜] F) (fun x => Bundle.dual 𝕜 E x ⊗[𝕜] E x)) :=
    Bundle.TensorProduct.tensorTotalSpaceTop (𝕜 := 𝕜) (B := B)
      (F₁ := F →L[𝕜] 𝕜) (F₂ := F) (E₁ := Bundle.dual 𝕜 E) (E₂ := E)
  letI : FiberBundle ((F →L[𝕜] 𝕜) ⊗[𝕜] F) (fun x => Bundle.dual 𝕜 E x ⊗[𝕜] E x) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F →L[𝕜] 𝕜) (F₂ := F) (E₁ := Bundle.dual 𝕜 E) (E₂ := E)
  letI : VectorBundle 𝕜 ((F →L[𝕜] 𝕜) ⊗[𝕜] F) (fun x => Bundle.dual 𝕜 E x ⊗[𝕜] E x) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := F →L[𝕜] 𝕜) (F₂ := F) (E₁ := Bundle.dual 𝕜 E) (E₂ := E)
  -- ── Tensor product bundle instances: T⁰₁(E*) ⊗ T⁰₁(E) ───────────────────
  -- Must use `instDT*` from Product.lean for coherence with `mixedBundle_tensorBundle_equiv`.
  letI (x : B) : AddCommGroup     (ML1d x ⊗[𝕜] ML1 x) := instDTAddCommGroup 1 1 x
  letI (x : B) : TopologicalSpace (ML1d x ⊗[𝕜] ML1 x) := instDTTop 1 1 x
  letI : TopologicalSpace (TotalSpace _ (fun x => ML1d x ⊗[𝕜] ML1 x)) := instDTTotalTop 1 1
  letI : FiberBundle  _ (fun x => ML1d x ⊗[𝕜] ML1 x) := instDTFB 1 1
  letI : VectorBundle 𝕜 _ (fun x => ML1d x ⊗[𝕜] ML1 x) := instDTVB 1 1
  -- ── ContinuousAdd/ContinuousSMul for double dual ──────────────────────────
  -- Lean cannot synthesize these for nested `ContinuousLinearMap` types because the
  -- `NormedAddCommGroup` on the intermediate `E x →L[𝕜] 𝕜` is not found during
  -- unification of the `Add` instance.  Providing it explicitly resolves the diamond.
  haveI (x : B) : ContinuousAdd (Bundle.dual 𝕜 (Bundle.dual 𝕜 E) x) := by
    change ContinuousAdd ((E x →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    letI : NormedAddCommGroup (E x →L[𝕜] 𝕜) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace 𝕜 (E x →L[𝕜] 𝕜) := ContinuousLinearMap.toNormedSpace
    infer_instance
  haveI (x : B) : ContinuousSMul 𝕜 (Bundle.dual 𝕜 (Bundle.dual 𝕜 E) x) := by
    change ContinuousSMul 𝕜 ((E x →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    letI : NormedAddCommGroup (E x →L[𝕜] 𝕜) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace 𝕜 (E x →L[𝕜] 𝕜) := ContinuousLinearMap.toNormedSpace
    infer_instance
  -- ── ContMDiffVectorBundle for multilinear factor bundles ────────────────────
  haveI : ContMDiffVectorBundle n (MLF' 𝕜 (F →L[𝕜] 𝕜))
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) IB :=
    SmoothVectorBundle.continuousMultilinearMap 1 IB n
  haveI : ContMDiffVectorBundle n (MLF' 𝕜 F)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x) IB :=
    SmoothVectorBundle.continuousMultilinearMap 1 IB n
  -- ── Compose: T¹₁(E) ≃ T⁰₁(E*) ⊗ T⁰₁(E) ≃ E ⊗ T⁰₁(E) ≃ E ⊗ E* ≃ E* ⊗ E
  exact (mixedBundle_tensorBundle_equiv n (r := 1) (s := 1)).trans
    (((tensorProductMapLeft n
        ((Bundle.continuousMultilinearMap.covectorBundle_equiv (n := n)
            (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := Bundle.dual 𝕜 E)).trans
          doubleDualBundleEquiv) rfl).trans
      (tensorProductMapRight n
        (Bundle.continuousMultilinearMap.covectorBundle_equiv (n := n)) rfl)).trans
      (tensorProductComm n))

end Mixed11

end
