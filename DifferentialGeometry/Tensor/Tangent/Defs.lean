/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Tensor Fibers and Bundle Instances over the Tangent Bundle

We define the point-wise fibers for covariant and mixed tensor bundles on smooth manifolds,
specializing the general `Bundle.continuousMultilinearMap` and `Bundle.ContinuousLinearMap`
constructions to the tangent bundle.

The (0,s) covariant tensor bundle has model fiber
`ContinuousMultilinearMap 𝕜 (Fin s → E) 𝕜` and the (r,s) tensor bundle has model fiber
`ContinuousMultilinearMap 𝕜 (Fin r → E) 𝕜 →L[𝕜] ContinuousMultilinearMap 𝕜 (Fin s → E) 𝕜`.

## Main Definitions

* `Tensor0SSpace s I x` : the fiber of the (0,s) covariant tensor bundle at `x ∈ M`;
  defined as `Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`.
* `CotangentSpace I x` : the cotangent space at `x`, i.e. `Tensor0SSpace 1 I x`.
* `TensorRSSpace r s I x` : the fiber of the (r,s) tensor bundle at `x`;
  continuous linear maps from (0,r)-tensors to (0,s)-tensors.
* `tensor0SSpace_continuousLinearEquiv` : the identity CLE witnessing that the bundle and
  norm topologies on `Tensor0SSpace s I x` agree (since `TangentSpace I x = E`).
* `tensorRSSpace_continuousLinearEquiv` : the analogous CLE for `TensorRSSpace r s I x`.
Bundle instances (topology, fiber bundle, vector bundle, smooth vector bundle) are inherited
from `Bundle.continuousMultilinearMap` (for the (0,s) case) and from
`Bundle.continuousMultilinearMap.mixedTopology` et al. (for the (r,s) case) via
`Multilinear/Bundle.lean` and `Mixed/Bundle.lean`.

## Tags

tensor, covariant tensor, smooth manifold, differential geometry, vector bundle
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x' : M}
variable {r s : ℕ}

/-- The trivial line bundle over `M` with constant fiber `𝕜`. -/
abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

/-!
## Point-wise Fibers
-/

/-- The fiber of the (0,s) covariant tensor bundle at `x ∈ M`, defined as
`Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`. -/
abbrev Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x

/-- The cotangent space at `x ∈ M`: linear functionals on the tangent space,
realized as (0,1)-tensors. -/
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace 1 I x

/-- The fiber of the (r,s)-tensor bundle at `x ∈ M`: continuous linear maps from
(0,r)-tensors to (0,s)-tensors, using `(V⊗W)* ≅ V*⊗W*` and `V*⊗W ≅ Hom(V,W)`. -/
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

/-!
## Point-wise Fiber Instances

The bundle and norm topologies on `Tensor0SSpace s I x` agree because the trivialization at
each point gives a continuous linear equivalence to the model fiber, and all Hausdorff
locally convex topologies on a finite-dimensional space agree.
-/

/-- The tangent space at any point is a normed additive commutative group, inherited from `E`. -/
instance tangentSpace_normedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- The tangent space at any point is a normed `𝕜`-module, inherited from `E`. -/
instance tangentSpace_normedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (NormedSpace 𝕜 E)

instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional 𝕜 E)

instance tangentSpace_moduleFree (x : M) :
    Module.Free 𝕜 (TangentSpace I x) :=
  inferInstanceAs (Module.Free 𝕜 E)

omit [FiniteDimensional 𝕜 E] in
/-- Alias for the general `Bundle.continuousMultilinearMap.topology_eq`, specialized to the
tangent bundle. Used internally by `tensor0SSpace_continuousLinearEquiv`. -/
private theorem tensor0SSpace_topology_eq (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) :=
  Bundle.continuousMultilinearMap.topology_eq s x

noncomputable instance tensor0SSpace_finiteDimensional [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.instFiniteDimensional s x

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  Bundle.continuousMultilinearMap.finrank_eq s x

omit [FiniteDimensional 𝕜 E] in
/-- `Tensor0SSpace s I x` is definitionally equal to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`, since `TangentSpace I x = E`. -/
private theorem tensor0SSpace_type_eq (s : ℕ) (x : M) :
    Tensor0SSpace s I x =
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 := by
  unfold Tensor0SSpace Bundle.continuousMultilinearMap
  rfl

/-- The fiber `Tensor0SSpace s I x` is continuously linearly isomorphic to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`: the underlying types are definitionally
equal and the topologies agree by `tensor0SSpace_topology_eq`. -/
def tensor0SSpace_continuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Tensor0SSpace s I x) (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜) (Tensor0SSpace s I x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

/-- The fiber `TensorRSSpace r s I x` is continuously linearly isomorphic to
`ContinuousMultilinearMap 𝕜 (Fin r → E) 𝕜 →L[𝕜] ContinuousMultilinearMap 𝕜 (Fin s → E) 𝕜`:
this follows from `arrowCongr` applied to `tensor0SSpace_continuousLinearEquiv` on both the
domain and codomain. -/
def tensorRSSpace_continuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
  (tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpace_continuousLinearEquiv (I := I) s x)

omit [FiniteDimensional 𝕜 E] in
/-- The `→L[𝕜]` between `Tensor0SSpace` fibers (with the bundle topology) is the
same type as `→L[𝕜]` between `ContinuousMultilinearMap` fibers (with the norm topology),
since the topologies agree by `tensor0SSpace_topology_eq`. -/
private theorem tensorRSSpace_type_eq (r s : ℕ) (x : M) :
    TensorRSSpace r s I x =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  unfold TensorRSSpace Tensor0SSpace Bundle.continuousMultilinearMap
  congr 1 <;> exact tensor0SSpace_topology_eq (I := I) _ x

/-- Transport `NormedAddCommGroup` and `NormedSpace` together from the norm-topology type. -/
private def tensorRSSpace_normedInstances (r s : ℕ) (x : M) :
    Σ' (ng : NormedAddCommGroup (TensorRSSpace r s I x)),
      @NormedSpace 𝕜 (TensorRSSpace r s I x) _ ng.toSeminormedAddCommGroup :=
  (tensorRSSpace_type_eq (I := I) r s x) ▸ ⟨inferInstance, inferInstance⟩

/-- The fiber `TensorRSSpace r s I x` is a normed additive commutative group. -/
instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).1

/-- The fiber `TensorRSSpace r s I x` is a normed `𝕜`-module. -/
instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).2

/-- Scalar multiplication on `TensorRSSpace r s I x` is continuous. -/
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TensorRSSpace r s I x))

end
end Tensor0SBundle
