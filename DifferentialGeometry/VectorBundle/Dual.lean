/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.FiniteDimensional
import DifferentialGeometry.VectorBundle.Equiv
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# The dual bundle of a vector bundle

This file defines `Bundle.dual 𝕜 E`, the dual bundle of a vector bundle `E : B → Type*`,
whose fiber at `x : B` is the continuous dual `E x →L[𝕜] 𝕜`.

The construction is realized as a special case of the hom bundle (`Bundle.ContinuousLinearMap`)
where the codomain is the trivial `𝕜`-bundle `Bundle.Trivial B 𝕜`. This means all bundle
instances — `TopologicalSpace`, `FiberBundle`, `VectorBundle`, and `ContMDiffVectorBundle` —
are inherited automatically from the hom bundle and the trivial bundle's smooth structures
in Mathlib.

## Main Definitions

* `Bundle.dual 𝕜 E` : the dual bundle, with model fiber `F →L[𝕜] 𝕜`.

## Tags

dual bundle, vector bundle, cotangent
-/

noncomputable section

open Bundle

namespace Bundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*}
variable (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)]

/-- The dual bundle of a vector bundle `E`: at each point `x : B`, the fiber is the
continuous dual `E x →L[𝕜] 𝕜`. Realized as a special case of the hom bundle with the
trivial `𝕜`-bundle as the codomain. -/
abbrev dual : B → Type _ :=
  fun x => E x →L[𝕜] 𝕜

end Bundle

/-! ## Sanity check: the dual bundle inherits all the standard instances -/

section InstanceCheck

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

example (x : B) : Bundle.dual 𝕜 E x = (E x →L[𝕜] 𝕜) := rfl

-- The hom bundle topology applies (via the Trivial 𝕜-bundle as codomain).
example : TopologicalSpace (TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)) := inferInstance

example : FiberBundle (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

example : VectorBundle 𝕜 (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

end InstanceCheck

/-! ## Smooth structure -/

section Smooth

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

-- The smooth vector bundle instance for the dual bundle is inherited from the hom-bundle's
-- smoothness instance combined with the trivial bundle being a smooth vector bundle.
example : ContMDiffVectorBundle n (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) IB := inferInstance

end Smooth

/-! ## Double dual bundle equivalence -/

section DoubleDual

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

/-- The continuous double dual equivalence `V ≃ₗ[𝕜] (V →L[𝕜] 𝕜) →L[𝕜] 𝕜` via the
evaluation map `v ↦ (f ↦ f v)`, in finite dimensions. -/
private noncomputable def continuousDoubleDualEquiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] :
    V ≃ₗ[𝕜] (V →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  haveI : FiniteDimensional 𝕜 (V →L[𝕜] 𝕜) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := V) (F' := 𝕜)).finiteDimensional
  { toFun := fun v => LinearMap.toContinuousLinearMap
      { toFun := fun f => f v
        map_add' := fun f g => ContinuousLinearMap.add_apply f g v
        map_smul' := fun c f => ContinuousLinearMap.smul_apply c f v }
    invFun := fun Φ =>
      (Module.evalEquiv 𝕜 V).symm
        { toFun := fun g => Φ (LinearMap.toContinuousLinearMap g)
          map_add' := fun g₁ g₂ => by simp [map_add]
          map_smul' := fun c g => by simp [map_smul] }
    left_inv := fun v => by
      change (Module.evalEquiv 𝕜 V).symm _ = v
      rw [LinearEquiv.symm_apply_eq]
      ext g
      simp [Module.evalEquiv_apply, Module.Dual.eval_apply]
    right_inv := fun Φ => by
      ext f
      change (f : V →ₗ[𝕜] 𝕜) ((Module.evalEquiv 𝕜 V).symm _) = Φ f
      rw [Module.apply_evalEquiv_symm_apply]
      change Φ (LinearMap.toContinuousLinearMap (f : V →ₗ[𝕜] 𝕜)) = Φ f
      congr 1
    map_add' := fun v w => by ext f; simp [map_add]
    map_smul' := fun c v => by ext f; simp [map_smul] }

noncomputable def doubleDualBundleEquiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      ((F →L[𝕜] 𝕜) →L[𝕜] 𝕜) (Bundle.dual 𝕜 (Bundle.dual 𝕜 E))
      F E := by
  apply ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv (fun x => ?_) sorry sorry
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  unfold Bundle.dual
  exact (continuousDoubleDualEquiv (𝕜 := 𝕜) (V := E x)).symm

theorem doubleDualBundleEquiv_baseMap :
    (doubleDualBundleEquiv (𝕜 := 𝕜) (F := F) (E := E) (IB := IB) (n := n)).baseMap =
      _root_.id := rfl

end DoubleDual

end
