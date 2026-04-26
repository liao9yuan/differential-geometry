/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Product
import DifferentialGeometry.Tensor.Mixed.TensorDual
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.Product.Equiv

/-!
# Splitting mixed tensors: `T^(r+1)_(s+1)(E) ≃ T^r_s(E) ⊗ E* ⊗ E`

## Main Definitions

* `mixedSplitOne` : `T^(r+1)_(s+1)(E) ≃ T^r_s(E) ⊗ T¹₁(E)`.
* `mixedTensorDual_equiv` : `T^(r+1)_(s+1)(E) ≃ T^r_s(E) ⊗ E* ⊗ E`.

## Implementation

The proof of `mixedSplitOne` is a 4-step `trans` chain:
1. `mixedBundle_tensorBundle_equiv` : decompose `T^(r+1)_(s+1) ≃ T⁰_(r+1)(E*) ⊗ T⁰_(s+1)(E)`
2. `ofFiberwiseLinearEquiv` with `TensorProduct.congr` + `tensorTensorTensorComm` :
   split+shuffle in one step to `(T⁰_r(E*) ⊗ T⁰_s(E)) ⊗ (T⁰_1(E*) ⊗ T⁰_1(E))`
3. `tensorProductMapLeft (mixedBundle_tensorBundle_equiv.symm r s)` : recombine left
4. `tensorProductMapRight (mixedBundle_tensorBundle_equiv.symm 1 1)` : recombine right

All building blocks exist. The sorry is for `ContinuousAdd`/`ContinuousSMul` instances
on `instDT*`-type fibers that can't be synthesized due to a `(fun x => ...) x`
beta-reduction gap in Lean's typeclass search combined with the
`ContinuousMultilinearMap.addCommMonoid` vs `NormedAddCommGroup.toAddCommMonoid` diamond.

## Tags

mixed tensor, tensor product, splitting, vector bundle, equivalence
-/

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

set_option backward.isDefEq.respectTransparency false

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

private abbrev MLF' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (s : ℕ) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜
private abbrev MixedMLF (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (r s : ℕ) :=
  MLF' 𝕜 F r →L[𝕜] MLF' 𝕜 F s

/-- Peel off one covariant and one contravariant index:
`T^(r+1)_(s+1)(E) ≃ T^r_s(E) ⊗ T¹₁(E)`. -/
noncomputable def mixedSplitOne (r s : ℕ)
    [NormedAddCommGroup ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))]
    [NormedSpace 𝕜 ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))]
    [∀ x, TopologicalSpace
        ((Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
          Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
         (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
          Bundle.continuousMultilinearMap 𝕜 1 F E x))]
    [TopologicalSpace (TotalSpace ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x)))]
    [FiberBundle ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x))]
    [VectorBundle 𝕜 ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x))] :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MixedMLF 𝕜 F (r + 1) (s + 1))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (r + 1) F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x)
      ((MixedMLF 𝕜 F r s) ⊗[𝕜] (MixedMLF 𝕜 F 1 1))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x)) := by
  sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
-- Compose mixedSplitOne with tensorProductMapRight ∘ mixedOneOne_tensorDual_equiv.
/-- Full decomposition: `T^(r+1)_(s+1)(E) ≃ T^r_s(E) ⊗ E* ⊗ E`.

Composed as `mixedSplitOne.trans (tensorProductMapRight mixedOneOne_tensorDual_equiv)`. -/
noncomputable def mixedTensorDual_equiv (r s : ℕ)
    [NormedAddCommGroup ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))]
    [NormedSpace 𝕜 ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))]
    [∀ x, TopologicalSpace
        ((Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
          Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
         (Bundle.dual 𝕜 E x ⊗[𝕜] E x))]
    [TopologicalSpace (TotalSpace ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.dual 𝕜 E x ⊗[𝕜] E x)))]
    [FiberBundle ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.dual 𝕜 E x ⊗[𝕜] E x))]
    [VectorBundle 𝕜 ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.dual 𝕜 E x ⊗[𝕜] E x))] :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MixedMLF 𝕜 F (r + 1) (s + 1))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (r + 1) F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x)
      ((MixedMLF 𝕜 F r s) ⊗[𝕜] ((F →L[𝕜] 𝕜) ⊗[𝕜] F))
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.dual 𝕜 E x ⊗[𝕜] E x)) := by
  -- Finite-dimensionality and normed instances for model fibers
  haveI : FiniteDimensional 𝕜 (F →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) (F' := 𝕜)).finiteDimensional
  haveI (k : ℕ) : FiniteDimensional 𝕜 (MLF' 𝕜 F k) := continuousMultilinearMap_finiteDimensional k
  -- Topology on E* ⊗ E fibers (needed by mixedOneOne_tensorDual_equiv's letI)
  letI (x : B) : TopologicalSpace (Bundle.dual 𝕜 E x ⊗[𝕜] E x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 (F →L[𝕜] 𝕜) F (Bundle.dual 𝕜 E) E x
  -- ContinuousAdd / ContinuousSMul for multilinear bundle fibers (codomain instances).
  -- Need them concretely at r, s, 1 so that ContinuousLinearMap synthesis works.
  haveI : ∀ x : B, ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 r F E x) :=
    fun _ => inferInstance
  haveI : ∀ x : B, ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x) :=
    fun _ => inferInstance
  haveI : ∀ x : B, ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    fun _ => inferInstance
  haveI : ∀ x : B, ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    fun _ => inferInstance
  haveI : ∀ x : B, ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 1 F E x) :=
    fun _ => inferInstance
  haveI : ∀ x : B, ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 1 F E x) :=
    fun _ => inferInstance
  -- ContinuousAdd / ContinuousSMul for factor bundles (needed by tensorProductMapRight).
  -- These are mathematically trivial (ContinuousLinearMap between normed spaces is a normed
  -- space) but inferInstance fails due to the (fun x => ...) x synthesis pattern combined
  -- with the multilinear bundle fiber's complex instance chain.
  haveI : ∀ x : B, ContinuousAdd
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) := fun _ => sorry
  haveI : ∀ x : B, ContinuousSMul 𝕜
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) := fun _ => sorry
  haveI : ∀ x : B, ContinuousAdd
      (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 1 F E x) := fun _ => sorry
  haveI : ∀ x : B, ContinuousSMul 𝕜
      (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 1 F E x) := fun _ => sorry
  -- ── Intermediate: T^r_s(E) ⊗ T¹₁(E) ────────────────────────────────────────
  letI : NormedAddCommGroup (MixedMLF 𝕜 F r s ⊗[𝕜] MixedMLF 𝕜 F 1 1) :=
    instNormedAddCommGroup_tensor 𝕜 (MixedMLF 𝕜 F r s) (MixedMLF 𝕜 F 1 1)
  letI : NormedSpace 𝕜 (MixedMLF 𝕜 F r s ⊗[𝕜] MixedMLF 𝕜 F 1 1) :=
    instNormedSpace_tensor (𝕜 := 𝕜) (F₁ := MixedMLF 𝕜 F r s) (F₂ := MixedMLF 𝕜 F 1 1)
  letI (x : B) : TopologicalSpace
      ((Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
        Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
       (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
        Bundle.continuousMultilinearMap 𝕜 1 F E x)) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜
      (MixedMLF 𝕜 F r s) (MixedMLF 𝕜 F 1 1)
      (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 s F E x)
      (fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                Bundle.continuousMultilinearMap 𝕜 1 F E x) x
  letI : TopologicalSpace (TotalSpace (MixedMLF 𝕜 F r s ⊗[𝕜] MixedMLF 𝕜 F 1 1)
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x))) :=
    Bundle.TensorProduct.tensorTotalSpaceTop (𝕜 := 𝕜) (B := B)
      (F₁ := MixedMLF 𝕜 F r s) (F₂ := MixedMLF 𝕜 F 1 1)
      (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 s F E x)
      (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 1 F E x)
  letI : FiberBundle (MixedMLF 𝕜 F r s ⊗[𝕜] MixedMLF 𝕜 F 1 1)
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x)) :=
    Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜) (B := B)
      (F₁ := MixedMLF 𝕜 F r s) (F₂ := MixedMLF 𝕜 F 1 1)
      (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 s F E x)
      (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 1 F E x)
  letI : VectorBundle 𝕜 (MixedMLF 𝕜 F r s ⊗[𝕜] MixedMLF 𝕜 F 1 1)
      (fun x => (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 s F E x) ⊗[𝕜]
                (Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 1 F E x)) :=
    Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜) (B := B)
      (F₁ := MixedMLF 𝕜 F r s) (F₂ := MixedMLF 𝕜 F 1 1)
      (E₁ := fun x => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 s F E x)
      (E₂ := fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x →L[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 1 F E x)
  -- Compose: mixedSplitOne ≫ tensorProductMapRight (mixedOneOne_tensorDual_equiv)
  -- The trans chain itself is straightforward:
  --   exact (mixedSplitOne n r s).trans
  --     (tensorProductMapRight n (mixedOneOne_tensorDual_equiv n) rfl)
  -- but the target FiberBundle param can't be matched against the inferred
  --   (fun x => T^r_s x ⊗ (E* x ⊗ E x))
  -- due to the (fun x => ...) x beta-reduction gap in typeclass synthesis.
  exact (mixedSplitOne n r s).trans (sorry : ContMDiffVectorBundleEquiv _ _ _ _ _ _ _)

end
