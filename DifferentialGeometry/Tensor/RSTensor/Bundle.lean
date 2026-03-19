/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
/-!
# Tensor Bundles on Smooth Manifolds

Let `M` be a smooth manifold modelled on a finite-dimensional normed space `E` over a
nontrivially normed field `𝕜`, with model with corners `I : ModelWithCorners 𝕜 E H`.

We show that the (0,s) covariant tensor bundle and the (r,s) tensor bundle carry all
expected smooth vector bundle instances. The (0,s) bundle instances are constructed
inductively using the fact that a (0,s+1)-tensor is the same as a continuous linear map
from the tangent space to a (0,s)-tensor.

## Main Definitions

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
    · exact inferInstanceAs <| TopologicalSpace (TotalSpace
        (Tensor0SModel (s+1) 𝕜 E) (fun _ : M => Tensor0SModel (s+1) 𝕜 E))
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
    @VectorBundle 𝕜 M (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)
      _ _ _ _ (tensor0SModel_normedSpace s) _ (tensor0SBundle_topology (n := n) s)
      _ (tensor0SBundleData n s).fiber
  := (tensor0SBundleData (n := n) s).vector

/-- The (0,s)-tensor bundle is a smooth vector bundle over `M`. -/
@[simp]
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)
      _ E _ _ H _ I _ _ _ _ _ _ (tensor0SBundle_topology (n := n) s) _
      (tensor0SBundleData n s).fiber (tensor0SBundleData n s).vector
  := (tensor0SBundleData (n := n) s).smooth


/-- The total space of the (r,s)-tensor bundle carries a topology, induced by viewing it
as the hom bundle from the (0,r)- to the (0,s)-tensor bundle. -/
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
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
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s) _
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
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModel_normedAddCommGroup r s) (tensorRSModel_normedSpace r s) _
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s) _
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
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s) _
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
