/-
Author: Yuan Liao
Coauthor: Jack McCarthy
-/

/- This file defines tensor bundle on a smooth manifold by the following

Let `M` be a manifold with model `I` on `(E, H),` whereas we assumed that `M` has finite dimension
The tangent space `TangentSpace I (x : M)` has already been defined as a type synonym for `E`,
and the tangent bundle `TangentBundle I M` as an abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

We define `Tensor0SSpace (s : ℕ)` by s-multilinear map from `TangentSpace` to the base field,
which in finite dimension is isomorphic to the (0,s) tensors (covariant tensors).
Consideration for Banach manifold is left for a future project.
`Tensor0SBundle` is the abbreviation Bundle.TotalSpace (Tensor0SModel 𝕜 E s) (Tensor0SSpace s I : M → Type _)

After some clearance of inference problem, we inductively construct a structure `tensor0SBundleData (s: ℕ)`
which stores four instances `topology` `fiber` `vector` `smooth,` that the (0,s) tensor bundle is
a topological space, a fibre bundle, a vector bundle, and a smooth vector bundle respectively.

We finally define (r,s) tensor bundle as the hom bundle from (0,r) tensor bundle to (0,s) tensor bundle,
then show the instance `tensorRSBundle_smooth (r s : ℕ)`
  ContMDiffVectorBundle n
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) I
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.VectorField

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]
variable {x' : M}
variable {r s : ℕ}

/-!
# Tensor Definition and Instances
-- TODO: Elaborate on this comment
-/

abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

-- Tensor0SSpace is multilinear maps from tangent spaces to the base field
-- These are (0,s) covariant tensors
@[reducible]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜

-- A cotangent vector is a (0,1)-tensor
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) (x : M) := Tensor0SSpace 1 I x

-- (r,s)-tensors as Hom((0,r), (0,s))
-- This uses the isomorphisms (V⊗W)⋆≅(V⋆)⊗(W⋆) and (V⋆)⊗W≅Hom(V,W) for finite-dimensional V,W.
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

instance (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hs : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hr : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  apply @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
     _ _ _ _ hr hs _ _

def tensor0S_curry
    (s : ℕ) (x : M) :
  Tensor0SSpace (s+1) I x
    ≃L[𝕜]
  (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) := by
  unfold TangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (s+1) => E) 𝕜).toContinuousLinearEquiv

-- Fiberwise instances for (0,s)-tensors
instance tensor0SSpace_normedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

-- Tensor0SSpace is finite-dimensional
instance tensor0SSpace_finiteDimensional (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  letI : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
    @Module.Finite.multilinearMap (Fin s) 𝕜 𝕜 (fun _ : Fin s => E) _ _ _ _ _ _ _ _ _ _
  let f : (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) →ₗ[𝕜]
      (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := ContinuousMultilinearMap.toMultilinearMapLinear
  have h : Function.Injective f := ContinuousMultilinearMap.toMultilinearMap_injective
  exact FiniteDimensional.of_injective f h

-- TensorRSSpace is finite-dimensional
instance tensorRSSpace_finiteDimensional (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  infer_instance

-- Tensor0SSpace is a normed linear space
instance tensor0SSpace_normedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

-- Tensor0SSpace is a normed additive commutitive group
instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

-- TensorRSSpace is a normed linear space
instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ _

-- TensorRSSpace has continuous scalar multiplication
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact @ContinuousLinearMap.continuousSMul 𝕜 𝕜 _ _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ _ _

-- TensorRSSpace is a topological space
instance tensorRSModel_topology (r s : ℕ) :
    TopologicalSpace
      (TensorRSModel r s 𝕜 E) :=
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  inferInstance

-- Tensor0SModel is a normed additive commutative group
instance tensor0SModel_normedAddCommGroup (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) :=
  inferInstance

-- Tensor0SModel is a normed linear space
instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

-- TensorRSModel is a normed additive commutative group
instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      (TensorRSModel r s 𝕜 E) :=
  inferInstance

-- TensorRSModel is a normed linear space
instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜
      (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

-- Topology instances for (0,0)-tensor bundle
-- TODO: Show that a (0,0)-tensor bundle is a function
instance tensor0S_topologicalSpace_zero :
    TopologicalSpace (TotalSpace
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x)) := by
  have h : (fun x : M => Tensor0SSpace 0 I x) =
           (fun x : M => Tensor0SModel 0 𝕜 E) := by
    ext x
    unfold Tensor0SSpace
    unfold TangentSpace
    rfl
  rw [h]
  infer_instance

instance tensor0S_fiberBundle_zero :
    FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) :=
    inferInstanceAs <| FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun _ : M => Tensor0SModel 0 𝕜 E)

instance tensor0S_vectorBundle_zero :
    @VectorBundle 𝕜 M (Tensor0SModel 0 𝕜 E) (fun x : M => Tensor0SSpace 0 I x) _ _ _ _
    (tensor0SModel_normedSpace 0) _ _ _ tensor0S_fiberBundle_zero :=
  inferInstanceAs <|
    @VectorBundle 𝕜 M (Tensor0SModel 0 𝕜 E) (fun _ : M => Tensor0SModel 0 𝕜 E) _ _ _ _
    (tensor0SModel_normedSpace 0) _ _ _ tensor0S_fiberBundle_zero

noncomputable instance tensor0S_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) I :=
    inferInstanceAs <| ContMDiffVectorBundle n
       (Tensor0SModel 0 𝕜 E)
       (fun _ : M => Tensor0SModel 0 𝕜 E) I

structure Tensor0SBundleData (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : WithTop ℕ∞) [IsManifold I n M]
    (s : ℕ) where
  topology : TopologicalSpace (TotalSpace
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x))
  fiber : FiberBundle
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x)
  vector : VectorBundle 𝕜
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x)
  smooth : ContMDiffVectorBundle n
    (Tensor0SModel s 𝕜 E)
    (fun x : M => Tensor0SSpace s I x) I

noncomputable def tensor0SBundleData_zero :
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensor0S_topologicalSpace_zero
  fiber := tensor0S_fiberBundle_zero
  vector := tensor0S_vectorBundle_zero
  smooth := inferInstanceAs <| ContMDiffVectorBundle n
    (Tensor0SModel 0 𝕜 E)
    (fun _ : M => Tensor0SModel 0 𝕜 E) I
}

noncomputable instance tensor0SBundleData : (s : ℕ) →
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
  | 0 => tensor0SBundleData_zero  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
  | s + 1 => by
    let prev := tensor0SBundleData s
    refine {
      topology := ?_,
      fiber := ?_,
      vector := ?_,
      smooth := ?_
    }
    · have h : (fun x : M => Tensor0SSpace (s+1) I x) =
              (fun x : M => Tensor0SModel (s+1) 𝕜 E) := by
        ext x
        unfold Tensor0SSpace
        unfold TangentSpace
        rfl
      rw [h]
      infer_instance
    · exact inferInstanceAs <| FiberBundle
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E)
    · exact inferInstanceAs <| VectorBundle 𝕜
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E)
    · haveI : ContMDiffVectorBundle n E
        (fun x : M => TangentSpace I x) I := inferInstance
      exact inferInstanceAs <| ContMDiffVectorBundle n
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E) I

instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace s I x)) :=
  (tensor0SBundleData n s).topology

@[simp]
noncomputable instance tensor0SBundle_fiber (s : ℕ) :
    @FiberBundle
      M
      (Tensor0SModel s 𝕜 E)
      _
      _
      (fun x : M => Tensor0SSpace s I x)
      (tensor0SBundle_topology (n := n) s)
      _
      :=
  (@tensor0SBundleData 𝕜 _ E _ _ _ H _ I M _ _ n _ s).fiber

@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    @VectorBundle
      𝕜
      M
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)
      _
      _
      _
      _
      (tensor0SModel_normedSpace s)
      _
      (tensor0SBundle_topology (n := n) s)
      _
      (tensor0SBundleData n s).fiber
      :=
  (tensor0SBundleData (n := n) s).vector

@[simp]
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensor0SBundle_topology (n := n) s)
      _
      (tensor0SBundleData n s).fiber
      (tensor0SBundleData n s).vector
      :=
  (tensor0SBundleData (n := n) s).smooth


-- Topology for (r,s)-tensor bundles as Hom((0,r), (0,s))
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    exact Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
      (Tensor0SModel r 𝕜 E)
      (fun (x : M) => Tensor0SSpace r I x)
      (Tensor0SModel s 𝕜 E)
      (fun (x : M) => Tensor0SSpace s I x)


-- Fiber bundle instance for (r,s)-tensors
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle
      M
      (TensorRSModel r s 𝕜 E)
      _
      (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
      (Tensor0SModel r 𝕜 E)
      (fun (x : M) => Tensor0SSpace r I x)
      (Tensor0SModel s 𝕜 E)
      (fun (x : M) => Tensor0SSpace s I x)

-- Vector bundle instance for (r,s)-tensors
noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle
      𝕜
      M
      (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)
      _  -- [NontriviallyNormedField 𝕜]
      (fun x => by infer_instance)  -- [∀ x, AddCommMonoid (E x)]
      (fun x => by infer_instance)  -- [∀ x, Module 𝕜 (E x)]
      (tensorRSModel_normedAddCommGroup r s)  -- [NormedAddCommGroup F]
      (tensorRSModel_normedSpace r s)         -- [NormedSpace 𝕜 F]
      _  -- [TopologicalSpace M]
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _  -- [∀ x, TopologicalSpace (E x)]
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
      fun _ => inferInstance
    exact Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
      (fun (x : M) => Tensor0SSpace r I x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun (x : M) => Tensor0SSpace s I x)

-- Smooth vector bundle instance for (r,s)-tensors
noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle
      n
      𝕜
      M
      (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)
      _
      E
      _
      _
      H
      _
      I
      _
      _
      _
      _
      _
      _
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      _
      (tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      (tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
      := by
    let := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
    letI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    letI : ∀ (x : M), IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜
        (fun _ : Fin s => TangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    letI : ∀ (x : M), ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜
        (fun _ : Fin s => TangentSpace I x) 𝕜) :=
      fun _ => inferInstance
    exact ContMDiffVectorBundle.continuousLinearMap

/-We did not specify the tensor field above, but that is just the smooth section-/

/- Product of (0,s) and (0,s') to a (0,s+s') tensor (and r,s and r',s')-/
/- Interior product -/
/- Contraction of (r,s) by a tangent vector to get (r,s-1), or a cotangent vector to get (r-1,s)
tensor-/
/- Lie derivatives based on contraction and Lie bracket on vector field (which is defined already)-/

-- Tensor fields as smooth sections of tensor bundles
def TensorRSField (r s : ℕ) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

instance tangentSpace_normedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

instance tangentSpace_normedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (NormedSpace 𝕜 E)


noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  -- E is finite-dimensional, hence Module.Finite and Module.Free
  haveI : Module.Finite 𝕜 E := inferInstance
  haveI : Module.Free 𝕜 E := inferInstance
  -- The target 𝕜 is also finite and free over itself
  haveI : Module.Finite 𝕜 𝕜 := inferInstance
  haveI : Module.Free 𝕜 𝕜 := inferInstance
  -- Now Module.Finite.multilinearMap applies
  infer_instance


-- Instance for ContinuousMultilinearMap via injection into MultilinearMap
noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) := by
  haveI : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

noncomputable instance continuousMultilinearMap_finiteDimensional_nested (r r' : ℕ) :
    FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜)) := by
  -- The nested type is isomorphic to ContinuousMultilinearMap (Fin (r + r') → E) 𝕜
  let e1 := ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 (finSumFinEquiv (m := r) (n := r')).symm
  let e2 := ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (r + r')
  exact LinearEquiv.finiteDimensional (e1.trans e2).toLinearEquiv


noncomputable def tensor0S_product_fun (s q : ℕ)
  (x : M) (α : Tensor0SSpace s I x) (β : Tensor0SSpace q I x) :
   Tensor0SSpace (s + q) I x :=
  (α.smulRight β).uncurrySum.domDomCongr (finSumFinEquiv)

/- TODO: Is this the correct implementation of bilinearity?
Note: Adding the following parenthesis breaks code:
  (Tensor0SSpace s I x →ₗ[𝕜] Tensor0SSpace q I x) →ₗ[𝕜] Tensor0SSpace (s + q) I x
TODO: Can we make this a continuous linear equivalence? I.e.
  (Tensor0SSpace s I x →L[𝕜] Tensor0SSpace q I x) ≃L Tensor0SSpace (s + q) I x -/
variable [CompleteSpace 𝕜]
noncomputable def tensor0S_product_bilinear (s q : ℕ) (x : M) :
    Tensor0SSpace s I x →ₗ[𝕜] Tensor0SSpace q I x →ₗ[𝕜] Tensor0SSpace (s + q) I x := {
  toFun := fun α => {
    toFun := fun β => tensor0S_product_fun s q x α β
    map_add' := fun β₁ β₂ => by
      unfold tensor0S_product_fun
      ext m
      simp [smul_add]
    map_smul' := fun c β => by
      unfold tensor0S_product_fun
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply,
                 smul_eq_mul, RingHom.id_apply]
      ring
  }
  map_add' := fun α₁ α₂ => by
    ext β m
    unfold tensor0S_product_fun
    simp [add_smul]
  map_smul' := fun c α => by
    ext β m
    unfold tensor0S_product_fun
    simp only [ContinuousMultilinearMap.domDomCongr_apply,
               ContinuousMultilinearMap.uncurrySum_apply,
               ContinuousMultilinearMap.smulRight_apply,
               ContinuousMultilinearMap.smul_apply,
               smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
               LinearMap.smul_apply]
    ring
}

-- Lift to TensorProduct via universal property
-- TODO: Implement the universal property using ``TensorProduct.lift``
noncomputable def tensor0S_fromTensor (s q : ℕ) (x : M) :
    TensorProduct 𝕜 (Tensor0SSpace s I x) (Tensor0SSpace q I x) →ₗ[𝕜] Tensor0SSpace (s + q) I x :=
  TensorProduct.lift (tensor0S_product_bilinear s q x)

/-!
# Tensor Product of (r,s) and (r',s') tensors
--TODO: Define tensor product on sections/bundles, not just pointwise
--TODO: Show that the product of smooth tensor fields is again smooth

The tensor product T ⊗ T' of tensors T : (0,r) →L (0,s) and T' : (0,r') →L (0,s')
is defined using the identification via tensor products.

For decomposable elements α ⊗ α' in (0,r) ⊗ (0,r'), we have:
  (T ⊗ T')(tensor0S_product(α, α')) = tensor0S_product(T(α), T'(α'))

Since (0,r+r') ≅ (0,r) ⊗ (0,r') in finite dimensions (via currying), we can extend linearly.
-/

-- Helper: curry a (0,r+r') tensor into a map from (Fin r → V) to (0,r')
-- Uses currySumEquiv composed with domDomCongr to handle Fin (r + r') ≃ Fin r ⊕ Fin r'
noncomputable def tensor0S_curryLeft (r r' : ℕ) (x : M) :
    Tensor0SSpace (r + r') I x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace r' I x) := by
  unfold Tensor0SSpace TangentSpace
  -- First convert Fin (r + r') to Fin r ⊕ Fin r' using domDomCongr
  -- Then apply currySumEquiv
  let e1 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 :=
    ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 finSumFinEquiv.symm
  let e2 : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
             (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜) :=
    ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  -- Compose: first apply e1 (reindex), then e2 (curry)
  let composed := e1.trans e2
  exact composed.toContinuousLinearMap

-- Helper: uncurry back from the curried form to (0,r+r')
noncomputable def tensor0S_uncurryLeft (r r' : ℕ) (x : M) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace r' I x) →L[𝕜]
    Tensor0SSpace (r + r') I x := by
  unfold Tensor0SSpace TangentSpace
  let e1 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 :=
    ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 finSumFinEquiv.symm
  let e2 : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
             (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜) :=
    ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  -- The inverse: first uncurry (e2.symm), then reindex back (e1.symm)
  let composed := e1.trans e2
  exact composed.symm.toContinuousLinearMap


-- First, add this helper lemma before tensor0S_equiv
omit [Module.Finite 𝕜 E] [IsManifold I ω M] in
lemma finrank_tensor0SSpace (n : ℕ) (x : M)
    [FiniteDimensional 𝕜 E] [Module.Finite 𝕜 E] :
    Module.finrank 𝕜 (Tensor0SSpace n I x) = (Module.finrank 𝕜 E) ^ n := by
  unfold Tensor0SSpace TangentSpace
  induction n with
  | zero =>
    have e := continuousMultilinearCurryFin0 𝕜 E 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    simp [pow_zero, Module.finrank_self]
  | succ n ih =>
    have e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) :=
      continuousMultilinearMap_finiteDimensional n
    haveI : Module.Free 𝕜 E := inferInstance
    let F := ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜
    haveI : Module.Free 𝕜 F := inferInstance
    -- In finite dimensions, E →L[𝕜] F ≃ₗ E →ₗ[𝕜] F
    have e2 : (E →L[𝕜] F) ≃ₗ[𝕜] (E →ₗ[𝕜] F) :=
      LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq]
    rw [Module.finrank_linearMap 𝕜 𝕜]  -- finrank 𝕜 (E →ₗ[𝕜] F) = finrank 𝕜 E * finrank 𝕜 F
    rw [ih]
    ring

noncomputable def tensor0S_equiv (r r' : ℕ) (x : M) :
    Tensor0SSpace (r + r') I x ≃ₗ[𝕜]
      TensorProduct 𝕜 (Tensor0SSpace r I x) (Tensor0SSpace r' I x) := by
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace r I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) r x
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace r' I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) r' x
  haveI : FiniteDimensional 𝕜 (Tensor0SSpace (r + r') I x) :=
    tensor0SSpace_finiteDimensional (𝕜 := 𝕜) (E := E) (I := I) (M := M) (r + r') x
  haveI : Module.Free 𝕜 (Tensor0SSpace r I x) := inferInstance
  haveI : Module.Free 𝕜 (Tensor0SSpace r' I x) := inferInstance
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜 (Tensor0SSpace r I x) (Tensor0SSpace r' I x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct]
    rw [finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r x]
    rw [finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r' x]
    rw [finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) (r + r') x]
    rw [pow_add])

/-- Given T : (r,s) and T' : (r',s'), we define T ⊗ T' : (r+r',s+s'). -/
-- TODO: Add notation for tensor product of tensors using ⊗ symbol
-- TODO: Combine with TensorProduct.lean
noncomputable def tensorRS_product (r s r' s' : ℕ) (x : M)
    (T : TensorRSSpace r s I x) (T' : TensorRSSpace r' s' I x) :
    TensorRSSpace (r + r') (s + s') I x :=
  LinearMap.toContinuousLinearMap <|
    (tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s s' x).symm.toLinearMap ∘ₗ
    TensorProduct.map T.toLinearMap T'.toLinearMap ∘ₗ
    (tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r r' x).toLinearMap

-- Helper: given α ∈ (0,r+r'), decompose using currying and apply T' to the "r'" part
private noncomputable def tensorRS_product_aux_right (r r' s' : ℕ) (x : M)
    (T' : TensorRSSpace r' s' I x)
    (α : Tensor0SSpace (r + r') I x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace s' I x) := by
  -- Curry α to get (Fin r → V) multilinear→ (0,r')
  let α_curried := (tensor0S_curryLeft (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r r' x) α
  -- Apply T' on the output
  exact T'.compContinuousMultilinearMap α_curried

/-!
# Interior Product and Contraction of Tensors
--TODO: Define tensor product on sections/bundles, not just pointwise
--TODO: Show that the contraction of a smooth vector field with a smooth tensor field is smooth

Interior product: contraction of a (0,s+1) tensor with a tangent vector to get (0,s).

Given v ∈ TangentSpace and α ∈ (0,s+1), we "feed" v into the first slot of α to get
an element of (0,s). This uses the curry-left isomorphism.
-/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x := by
  -- Use the curry-left equivalence: (0,s+1) ≃ V →L (0,s)
  -- Then evaluate at v
  unfold Tensor0SSpace TangentSpace
  -- continuousMultilinearCurryLeftEquiv gives us:
  -- ContinuousMultilinearMap (Fin (s+1) → E) 𝕜 ≃ₗᵢ E →L ContinuousMultilinearMap (Fin s → E) 𝕜
  let curry_equiv := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => E) 𝕜
  -- Compose: first curry, then evaluate at v
  exact ContinuousLinearMap.comp
    (ContinuousLinearMap.apply 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v)
    curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap


/-- Contraction of (r,s+1) tensor with tangent vector to get (r,s).

Given T : (r,s+1) and v ∈ TangentSpace, we compose T with interior_product(v).
-/
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    (TensorRSSpace r (s+1) I x) →L[𝕜] (TensorRSSpace r s I x) := by
  -- Given T : (0,r) →L (0,s+1), we want to produce (0,r) →L (0,s)
  -- This is just post-composition with interior_product v
  exact ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (s + 1) I x)
    (Tensor0SSpace s I x)
    (interior_product s x v)

/-- The map that tensors with a fixed 1-form: (0,r) → (0,r+1) given by α ↦ α ⊗ ω -/
noncomputable def tensorWithCovector (r : ℕ) (x : M)
    (u : CotangentSpace I x) :
    Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (r + 1) I x := by
  -- The bilinear map tensor0S_product_bilinear gives us:
  -- (0,r) →ₗ (0,1) →ₗ (0,r+1)
  -- We flip and apply ω to get: (0,r) →ₗ (0,r+1)
  exact LinearMap.toContinuousLinearMap <|
    (tensor0S_product_bilinear r 1 x).flip u

/-- Contraction of (r+1,s) tensor with a 1-form (cotangent vector) to get (r,s).

Given T : (0,r+1) →L (0,s) and ω ∈ (0,1), we produce T' : (0,r) →L (0,s)
by precomposing: T'(α) = T(α ⊗ ω).
-/
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (u : CotangentSpace I x) :
    (TensorRSSpace (r+1) s I x) →L[𝕜]
    (TensorRSSpace r s I x) :=
  (ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (r + 1) I x)
    (Tensor0SSpace s I x)).flip
    (tensorWithCovector r x u)

end
end Tensor0SBundle
