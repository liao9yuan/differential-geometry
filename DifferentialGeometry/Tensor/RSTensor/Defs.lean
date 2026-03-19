/-
Authors: Yuan Liao, Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Tensor Definitions and Instances

We define the model fibers and point-wise fibers for covariant and mixed tensor bundles
on smooth manifolds, together with their algebraic and topological instances.

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

## Tags

tensor, covariant tensor, smooth manifold, differential geometry
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
      (fun x : M => Tensor0SSpace 0 I x)) :=
  inferInstanceAs <| TopologicalSpace (TotalSpace
    (Tensor0SModel 0 𝕜 E)
    (fun _ : M => Tensor0SModel 0 𝕜 E))

end
end Tensor0SBundle
