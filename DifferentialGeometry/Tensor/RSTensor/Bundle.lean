/-
Authors: Yuan Liao, Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Tensor Bundles on Smooth Manifolds

Let `M` be a smooth manifold modelled on a finite-dimensional normed space `E` over a
nontrivially normed field `𝕜`, with model with corners `I : ModelWithCorners 𝕜 E H`.

We define the bundle of (0,s) covariant tensors by taking the fiber over `x : M` to be
the space of continuous multilinear maps from `s` copies of `TangentSpace I x` to `𝕜`.
The (r,s) tensor bundle is then defined as the hom-bundle from the (0,r)- to the (0,s)-tensor
bundle, using the finite-dimensional isomorphisms `(V ⊗ W)* ≅ V* ⊗ W*` and
`V* ⊗ W ≅ Hom(V, W)`.

We show that these bundles carry all expected smooth vector bundle instances. The (0,s)
bundle instances are constructed inductively using the fact that a (0,s+1)-tensor is the
same as a continuous linear map from the tangent space to a (0,s)-tensor.

## Main Definitions

* `Tensor0SModel s 𝕜 E` : the model fiber for the (0,s) covariant tensor bundle;
  continuous multilinear maps from `s` copies of `E` to `𝕜`.
* `TensorRSModel r s 𝕜 E` : the model fiber for the (r,s) tensor bundle;
  continuous linear maps from `Tensor0SModel r` to `Tensor0SModel s`.
* `Tensor0SSpace s I x` : the fiber of the (0,s) covariant tensor bundle at `x ∈ M`;
  the space of continuous `s`-multilinear maps `TangentSpace I x × ⋯ → 𝕜`.
* `CotangentSpace I x` : the cotangent space at `x`, i.e. `Tensor0SSpace 1 I x`.
* `TensorRSSpace r s I x` : the fiber of the (r,s) tensor bundle at `x`;
  continuous linear maps from (0,r)-tensors to (0,s)-tensors.
* `tensor0S_curry s x` : the currying equivalence
  `Tensor0SSpace (s+1) I x ≃L[𝕜] (TangentSpace I x →L[𝕜] Tensor0SSpace s I x)`.
* `Tensor0SBundleData s` : a structure packaging the four smooth vector bundle instances
  (topological space, fiber bundle, vector bundle, smooth vector bundle) for `Tensor0SSpace s`.

## Main Results

* `tensor0SBundle_smooth s` : the (0,s) covariant tensor bundle is a smooth vector bundle.
* `tensorRSBundle_smooth r s` : the (r,s) tensor bundle is a smooth vector bundle.

## Tags

tensor bundle, covariant tensor, smooth manifold, vector bundle, differential geometry
-/

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

/-- The trivial line bundle over `M` with constant fiber `𝕜`. -/
abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

/-- The model fiber for the bundle of (0,s) covariant tensors:
continuous multilinear maps from `s` copies of `E` to `𝕜`. -/
@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

/-- The model fiber for the (r,s)-tensor bundle: continuous linear maps from (0,r)-tensors
to (0,s)-tensors, realizing `V* ⊗ W ≅ Hom(V, W)` for finite-dimensional `V`. -/
@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

/-- The fiber of the (0,s) covariant tensor bundle at `x ∈ M`: continuous multilinear maps
from `s` copies of `TangentSpace I x` to `𝕜`. -/
@[reducible]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜

/-- The cotangent space at `x ∈ M`: linear functionals on the tangent space,
realized as (0,1)-tensors. -/
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) (x : M) := Tensor0SSpace 1 I x

/-- The fiber of the (r,s)-tensor bundle at `x ∈ M`: continuous linear maps from
(0,r)-tensors to (0,s)-tensors, using `(V⊗W)* ≅ V*⊗W*` and `V*⊗W ≅ Hom(V,W)`. -/
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) (x : M) :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

/-- `Tensor0SModel s 𝕜 E` is a normed additive commutative group, inherited from
`ContinuousMultilinearMap`. -/
instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group, inherited from
the space of continuous linear maps. -/
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

/-- Currying isomorphism: a (0,s+1)-tensor is equivalent to a continuous linear map
from the tangent space to the space of (0,s)-tensors. -/
def tensor0S_curry
    (s : ℕ) (x : M) :
  Tensor0SSpace (s+1) I x
    ≃L[𝕜]
  (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) := by
  unfold TangentSpace
  exact (continuousMultilinearCurryLeftEquiv 𝕜
    (fun _ : Fin (s+1) => E) 𝕜).toContinuousLinearEquiv

/-- The fiber `Tensor0SSpace s I x` is a normed additive commutative group. -/
instance tensor0SSpace_normedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

/-- The fiber `Tensor0SSpace s I x` is finite-dimensional, since it injects into the
space of multilinear maps on a finite-dimensional space. -/
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

/-- The fiber `TensorRSSpace r s I x` is finite-dimensional, as a space of continuous
linear maps between finite-dimensional spaces. -/
instance tensorRSSpace_finiteDimensional (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  infer_instance

/-- The fiber `Tensor0SSpace s I x` is a normed `𝕜`-module. -/
instance tensor0SSpace_normedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

/-- The fiber `TensorRSSpace r s I x` is a normed additive commutative group. -/
instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  unfold Tensor0SSpace
  unfold TangentSpace
  infer_instance

/-- The fiber `TensorRSSpace r s I x` is a normed `𝕜`-module. -/
instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ _

/-- Scalar multiplication on `TensorRSSpace r s I x` is continuous. -/
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact @ContinuousLinearMap.continuousSMul 𝕜 𝕜 _ _ _
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ _ _

/-- The model fiber `TensorRSModel r s 𝕜 E` carries a topology as a normed space. -/
instance tensorRSModel_topology (r s : ℕ) :
    TopologicalSpace
      (TensorRSModel r s 𝕜 E) :=
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  inferInstance

/-- `Tensor0SModel s 𝕜 E` is a normed additive commutative group. -/
instance tensor0SModel_normedAddCommGroup (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) :=
  inferInstance

/-- `Tensor0SModel s 𝕜 E` is a normed `𝕜`-module. -/
instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      (TensorRSModel r s 𝕜 E) :=
  inferInstance

/-- `TensorRSModel r s 𝕜 E` is a normed `𝕜`-module. -/
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

/-- The total space of the (0,0)-tensor bundle carries a topology; a (0,0)-tensor is
a scalar function, so the fiber is constantly `𝕜`. -/
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

/-- The (0,0)-tensor bundle is a fiber bundle with fiber `𝕜`. -/
instance tensor0S_fiberBundle_zero :
    FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) :=
    inferInstanceAs <| FiberBundle
      (Tensor0SModel 0 𝕜 E)
      (fun _ : M => Tensor0SModel 0 𝕜 E)

/-- The (0,0)-tensor bundle is a vector bundle with model fiber `𝕜`. -/
instance tensor0S_vectorBundle_zero :
    @VectorBundle 𝕜 M (Tensor0SModel 0 𝕜 E) (fun x : M => Tensor0SSpace 0 I x) _ _ _ _
    (tensor0SModel_normedSpace 0) _ _ _ tensor0S_fiberBundle_zero :=
  inferInstanceAs <|
    @VectorBundle 𝕜 M (Tensor0SModel 0 𝕜 E) (fun _ : M => Tensor0SModel 0 𝕜 E) _ _ _ _
    (tensor0SModel_normedSpace 0) _ _ _ tensor0S_fiberBundle_zero

/-- The (0,0)-tensor bundle is a smooth vector bundle. -/
noncomputable instance tensor0S_contMDiffVectorBundle_zero :
    ContMDiffVectorBundle n
      (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) I :=
    inferInstanceAs <| ContMDiffVectorBundle n
       (Tensor0SModel 0 𝕜 E)
       (fun _ : M => Tensor0SModel 0 𝕜 E) I

/-- A data structure packaging the four bundle instances (topological space, fiber bundle,
vector bundle, smooth vector bundle) for the (0,s)-tensor bundle. -/
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

/-- The base case `s = 0` of the `Tensor0SBundleData` induction: all four bundle instances
for the trivial `𝕜`-bundle. -/
noncomputable def tensor0SBundleData_zero :
    Tensor0SBundleData (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 0 := {
  topology := tensor0S_topologicalSpace_zero
  fiber := tensor0S_fiberBundle_zero
  vector := tensor0S_vectorBundle_zero
  smooth := inferInstanceAs <| ContMDiffVectorBundle n
    (Tensor0SModel 0 𝕜 E)
    (fun _ : M => Tensor0SModel 0 𝕜 E) I
}

/-- All four bundle instances for the (0,s)-tensor bundle, constructed inductively by
currying: a (0,s+1)-tensor bundle is the hom bundle from `TM` to the (0,s)-tensor bundle. -/
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
    · exact inferInstanceAs <| ContMDiffVectorBundle n
        (Tensor0SModel (s+1) 𝕜 E)
        (fun x : M => Tensor0SModel (s+1) 𝕜 E) I

/-- The total space of the (0,s)-tensor bundle carries a topology derived from
`Tensor0SBundleData`. -/
instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
      (fun x : M => Tensor0SSpace s I x)) :=
  (tensor0SBundleData n s).topology

/-- The (0,s)-tensor bundle is a fiber bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
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

/-- The (0,s)-tensor bundle is a vector bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
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

/-- The (0,s)-tensor bundle is a smooth vector bundle over `M`. -/
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


/-- The total space of the (r,s)-tensor bundle carries a topology, induced by viewing it
as the hom bundle from the (0,r)- to the (0,s)-tensor bundle. -/
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


/-- The (r,s)-tensor bundle is a fiber bundle, as a hom bundle between two fiber bundles. -/
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

/-- The (r,s)-tensor bundle is a vector bundle with model fiber `TensorRSModel r s 𝕜 E`. -/
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

/-- The (r,s)-tensor bundle is a smooth vector bundle over `M`. -/
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

/-- The tangent space at any point is a normed additive commutative group, inherited from `E`. -/
instance tangentSpace_normedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- The tangent space at any point is a normed `𝕜`-module, inherited from `E`. -/
instance tangentSpace_normedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (NormedSpace 𝕜 E)

end
end Tensor0SBundle
