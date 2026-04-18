/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.VectorBundle.Equiv

/-!
# The Scalar Equivalence `T⁰₀(E) ≃ B × 𝕜`

The 0-multilinear bundle `T⁰₀(E)` is `C^n`-equivalent to the trivial bundle `B × 𝕜`
as a `ContMDiffVectorBundleEquiv`. Fiberwise, a 0-multilinear map (which is just a
scalar) is identified with its value via evaluation at the empty tuple.

## Main Definitions

* `Bundle.continuousMultilinearMap.scalarEquivAt` : fiber-level `LinearEquiv` between
  `T⁰₀(E)ₓ` and `𝕜`.
* `Bundle.continuousMultilinearMap.modelScalarFwdCLM` : model-level CLM `MLF 0 →L[𝕜] 𝕜`.
* `Bundle.continuousMultilinearMap.modelScalarInvCLM` : model-level CLM `𝕜 →L[𝕜] MLF 0`.
* `Bundle.continuousMultilinearMap.scalarBundle_equiv` : the `C^n` vector bundle equivalence.
* `MultilinearSection.fromScalarField` : promote a `C^n` scalar function to a 0-multilinear
  section.
* `MultilinearSection.toScalarField` : extract a scalar function from a 0-multilinear section.

## Tags

multilinear map, scalar, trivial bundle, vector bundle, fiberwise equivalence
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Abbreviation for the model fiber of the `s`-multilinear bundle. -/
local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-!
## Fiber-level equivalence
-/

/-- Fiber-level `LinearEquiv` between the 0-multilinear bundle fiber at `x` and `𝕜`.
Forward: evaluate at the empty tuple. Backward: `constOfIsEmpty`. -/
noncomputable def scalarEquivAt (x : B) :
    Bundle.continuousMultilinearMap 𝕜 0 F E x ≃ₗ[𝕜] 𝕜 where
  toFun T := T Fin.elim0
  invFun c := ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) c
  left_inv T := by
    apply Bundle.continuousMultilinearMap.ext; intro v
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact congrArg T (Subsingleton.elim Fin.elim0 v)
  right_inv c := ContinuousMultilinearMap.constOfIsEmpty_apply _ _ _ _
  map_add' T₁ T₂ := ContinuousMultilinearMap.add_apply T₁ T₂ Fin.elim0
  map_smul' c T := by
    change (c • T) Fin.elim0 = c • T Fin.elim0
    exact ContinuousMultilinearMap.smul_apply T c Fin.elim0

/-!
## Model-level continuous linear maps
-/

variable (𝕜 F) in
/-- Model-level forward CLM: evaluate a 0-multilinear map at the empty tuple. -/
noncomputable def modelScalarFwdCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    (MLF 0) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (MLF 0) := continuousMultilinearMap_finiteDimensional 0
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M 0
      map_add' := fun M₁ M₂ => ContinuousMultilinearMap.add_apply M₁ M₂ 0
      map_smul' := fun c M => by
        change (c • M) 0 = c • M 0
        exact ContinuousMultilinearMap.smul_apply M c 0 }

variable (𝕜 F) in
/-- Model-level inverse CLM: wrap a scalar as a constant 0-multilinear map. -/
noncomputable def modelScalarInvCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] :
    𝕜 →L[𝕜] (MLF 0) :=
  haveI : FiniteDimensional 𝕜 (MLF 0) := continuousMultilinearMap_finiteDimensional 0
  LinearMap.toContinuousLinearMap
    { toFun := ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => F)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-!
## Trivialization compatibility
-/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

set_option linter.unusedVariables false in
/-- Trivialization compatibility for the forward direction. -/
theorem scalar_triv_fwd_eq (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀
      ⟨x, scalarEquivAt (F := F) (E := E) x T⟩).2 =
    modelScalarFwdCLM 𝕜 F
      ((trivializationAt (MLF 0)
        (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀ ⟨x, T⟩).2) := by
  -- LHS: trivial bundle trivialization is the identity, so .2 = T Fin.elim0
  -- RHS: modelScalarFwdCLM evaluates at 0, and by triv_zero_apply_eq this equals T Fin.elim0
  change T Fin.elim0 = _
  exact (triv_zero_apply_eq x₀ x T 0).symm

set_option linter.unusedVariables false in
/-- Trivialization compatibility for the inverse direction. -/
theorem scalar_triv_inv_eq (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (c : 𝕜) :
    (trivializationAt (MLF 0)
      (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) x₀
      ⟨x, (scalarEquivAt (F := F) (E := E) x).symm c⟩).2 =
    modelScalarInvCLM 𝕜 F
      ((trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x₀ ⟨x, c⟩).2) := by
  -- LHS: trivialization of constOfIsEmpty c; RHS: constOfIsEmpty c (trivial triv is id)
  apply ContinuousMultilinearMap.ext; intro w
  -- LHS unfolds to: (constOfIsEmpty c) (fun i => symmL (w i)) = constOfIsEmpty c (w)
  -- Both sides are c since constOfIsEmpty is constant
  change (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => E x) c)
    (fun i : Fin 0 => (trivializationAt F E x₀).symmL 𝕜 x (w i)) =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 => F) c) w
  simp only [ContinuousMultilinearMap.constOfIsEmpty_apply]

/-!
## Total-space smoothness
-/

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable [ChartedSpace HB B]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

/-- The forward total-space map induced by `scalarEquivAt` is `C^n`. -/
theorem scalarEquivAt_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, MLF 0))
      (IB.prod 𝓘(𝕜, 𝕜))
      n
      (fun p : TotalSpace (MLF 0)
          (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) =>
        (⟨p.1, scalarEquivAt (F := F) (E := E) p.1 p.2⟩ :
          TotalSpace 𝕜 (Bundle.Trivial B 𝕜))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, MLF 0))
        𝓘(𝕜, MLF 0) n
        (fun p => (trivializationAt (MLF 0)
          (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const (c := modelScalarFwdCLM 𝕜 F)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact scalar_triv_fwd_eq p₀.proj p.proj hp p.snd

/-- The inverse total-space map induced by `scalarEquivAt` is `C^n`. -/
theorem scalarEquivAt_symm_smooth :
    ContMDiff
      (IB.prod 𝓘(𝕜, 𝕜))
      (IB.prod 𝓘(𝕜, MLF 0))
      n
      (fun p : TotalSpace 𝕜 (Bundle.Trivial B 𝕜) =>
        (⟨p.1, (scalarEquivAt (F := F) (E := E) p.1).symm p.2⟩ :
          TotalSpace (MLF 0)
            (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj (Bundle.Trivial B 𝕜)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, 𝕜))
        𝓘(𝕜, 𝕜) n
        (fun p => (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const (c := modelScalarInvCLM 𝕜 F)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact scalar_triv_inv_eq p₀.proj p.proj hp p.snd

/-!
## The bundle equivalence
-/

/-- The `C^n` vector bundle equivalence `T⁰₀(E) ≃ B × 𝕜`. -/
noncomputable def scalarBundle_equiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF 0)
      (fun x => Bundle.continuousMultilinearMap 𝕜 0 F E x)
      𝕜
      (Bundle.Trivial B 𝕜) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => scalarEquivAt (F := F) (E := E) x)
    scalarEquivAt_smooth
    scalarEquivAt_symm_smooth

end Bundle.continuousMultilinearMap

end
