/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Tensor Definitions and Bundle Instances

We define the model fibers and point-wise fibers for covariant and mixed tensor bundles
on smooth manifolds. The (0,s) covariant tensor bundle is defined as a
`Bundle.continuousMultilinearMap` applied to the tangent bundle, inheriting its smooth
vector bundle structure. The (r,s) tensor bundle is defined using
`Bundle.ContinuousLinearMap` between (0,r)- and (0,s)-tensor bundles.

## Main Definitions

* `Tensor0SModel s 𝕜 E` : the model fiber for the (0,s) covariant tensor bundle;
  continuous multilinear maps from `s` copies of `E` to `𝕜`.
* `TensorRSModel r s 𝕜 E` : the model fiber for the (r,s) tensor bundle;
  continuous linear maps from `Tensor0SModel r` to `Tensor0SModel s`.
* `Tensor0SSpace s I x` : the fiber of the (0,s) covariant tensor bundle at `x ∈ M`;
  defined as `Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`.
* `CotangentSpace I x` : the cotangent space at `x`, i.e. `Tensor0SSpace 1 I x`.
* `TensorRSSpace r s I x` : the fiber of the (r,s) tensor bundle at `x`;
  continuous linear maps from (0,r)-tensors to (0,s)-tensors.
* `tensor0S_curry s x` : the currying equivalence
  `Tensor0SSpace (s+1) I x ≃L[𝕜] (TangentSpace I x →L[𝕜] Tensor0SSpace s I x)`.

## Bundle Instances

* `tensor0SBundle_fiber s` : the (0,s)-tensor bundle is a fiber bundle.
* `tensor0SBundle_vector s` : the (0,s)-tensor bundle is a vector bundle.
* `tensor0SBundle_smooth s` : the (0,s)-tensor bundle is a smooth vector bundle.
* `tensorRSBundle_topology r s` : topology on the (r,s)-tensor bundle total space.
* `tensorRSBundle_fiber r s` : the (r,s)-tensor bundle is a fiber bundle.
* `tensorRSBundle_vector r s` : the (r,s)-tensor bundle is a vector bundle.
* `tensorRSBundle_smooth r s` : the (r,s)-tensor bundle is a smooth vector bundle.

## Tags

tensor, covariant tensor, smooth manifold, differential geometry, vector bundle
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
variable [IsManifold I 1 M]
variable {x' : M}
variable {r s : ℕ}

/-!
## Model Fibers
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

/-!
## Point-wise Fibers
-/

/-- The fiber of the (0,s) covariant tensor bundle at `x ∈ M`, defined as
`Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`. -/
@[reducible]
def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
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
## Model Fiber Instances
-/

/-- `Tensor0SModel s 𝕜 E` is a normed additive commutative group. -/
instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

/-- `Tensor0SModel s 𝕜 E` is a normed `𝕜`-module. -/
instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
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

/-- `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) :=
  inferInstance

/-- `TensorRSModel r s 𝕜 E` is a normed `𝕜`-module. -/
instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

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

/-- The bundle and norm topologies on `Tensor0SSpace s I x` agree. The bundle topology is
induced from the pretrivialization (a continuous linear equivalence to the model fiber),
and this coincides with the norm topology since the composition map is a homeomorphism. -/
private theorem tensor0SSpace_topology_eq (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) := by
  change instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x = _
  simp only [instTopologicalSpaceContinuousMultilinearMap]
  -- Step 1: Factor pretriv ∘ mk' = Prod.mk x ∘ g where g is the fiber map
  set e := trivializationAt E (TangentSpace I) x
  set g := ContinuousMultilinearMap.compContinuousLinearMapL
    (E₁ := fun _ : Fin s => TangentSpace I x) (E := fun _ : Fin s => E) (G := 𝕜)
    (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  -- Step 2: Decompose via induced_compose and isInducing_prodMkRight
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  -- Goal: induced g τ_norm = τ_norm
  -- Step 3: g is a homeomorphism (continuous with continuous inverse), hence inducing
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL
    (E₁ := fun _ : Fin s => E) (E := fun _ : Fin s => TangentSpace I x) (G := 𝕜)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hleft : Function.LeftInverse g' g := by
    intro L; ext v; dsimp [g, g']
    congr 1; funext i; exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M; ext v; dsimp [g, g']
    congr 1; funext i; exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩ g.continuous g'.continuous).isInducing.eq_induced.symm

/-- The fiber `Tensor0SSpace s I x` is a normed additive commutative group. -/
instance tensor0SSpace_normedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))

/-- The fiber `Tensor0SSpace s I x` is a normed `𝕜`-module. -/
instance tensor0SSpace_normedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))

instance tensor0SSpace_t2Space (s : ℕ) (x : M) :
    T2Space (Tensor0SSpace s I x) := by
  rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x =
        ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
  infer_instance

noncomputable instance tensor0SSpace_finiteDimensional [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  continuousMultilinearMap_finiteDimensional s

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  finrank_continuousMultilinearMap s

/-- With the bundle topology, addition on `Tensor0SSpace` fibers is continuous. -/
instance tensor0SSpace_isTopologicalAddGroup (s : ℕ) (x : M) :
    @IsTopologicalAddGroup (Tensor0SSpace s I x) inferInstance _ := by
  rw [tensor0SSpace_topology_eq (I := I) s x]
  infer_instance

/-- With the bundle topology, scalar multiplication on `Tensor0SSpace` fibers is continuous. -/
instance tensor0SSpace_continuousSMul (s : ℕ) (x : M) :
    @ContinuousSMul 𝕜 (Tensor0SSpace s I x) _ _ inferInstance := by
  rw [tensor0SSpace_topology_eq (I := I) s x]
  infer_instance

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

@[ext]
theorem tensor0SSpace_ext {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x)
    (h : ∀ m, (tensor0SSpace_continuousLinearEquiv s x T₁) m =
      (tensor0SSpace_continuousLinearEquiv s x T₂) m) :
    T₁ = T₂ := by
  have h1 : (tensor0SSpace_continuousLinearEquiv s x T₁) =
      (tensor0SSpace_continuousLinearEquiv s x T₂) := by
    ext m; exact h m
  exact (tensor0SSpace_continuousLinearEquiv s x).injective h1

/-- The fiber `TensorRSSpace r s I x` is continuously linearly isomorphic to
`TensorRSModel r s 𝕜 E`: this follows from `arrowCongr` applied to the
`tensor0SSpace_continuousLinearEquiv` on both the domain and codomain. -/
def tensorRSSpace_continuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpace_continuousLinearEquiv (I := I) s x)

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

/-!
## Currying
-/

/-- Currying isomorphism: a (0,s+1)-tensor is equivalent to a continuous linear map
from the tangent space to the space of (0,s)-tensors.

The proof composes three continuous linear equivalences:
1. `tensor0SSpace_continuousLinearEquiv` bridges the bundle/norm topology diamond.
2. `continuousMultilinearCurryLeftEquiv` curries the first argument of the multilinear map.
3. `arrowCongr` with the inverse of `tensor0SSpace_continuousLinearEquiv` converts
   the codomain back from norm to bundle topology. -/
noncomputable def tensor0S_curry (s : ℕ) (x : M) :
    Tensor0SSpace (s+1) I x ≃L[𝕜]
    (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) :=
  (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl 𝕜 E).arrowCongr
          (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm))

/-!
## (0,s)-Tensor Bundle Instances

The (0,s) covariant tensor bundle inherits its fiber bundle, vector bundle, and smooth
vector bundle structure from `Bundle.continuousMultilinearMap` applied to the tangent bundle.
-/

/-- The total space of the (0,s)-tensor bundle carries a topology from the
multilinear bundle construction. -/
instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Bundle.continuousMultilinearMap.topologicalSpace_totalSpace 𝕜 s E (TangentSpace I)

/-- The (0,s)-tensor bundle is a fiber bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_fiber (s : ℕ) :
    FiberBundle
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.fiberBundle 𝕜 s E (TangentSpace I)

/-- The (0,s)-tensor bundle is a vector bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    VectorBundle 𝕜
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.vectorBundle 𝕜 s E (TangentSpace I)

/-!
## Smooth Bundle Instances

The smooth bundle instances require `IsManifold I (n + 1) M` to get
`ContMDiffVectorBundle n` for the tangent bundle via `TangentBundle.contMDiffVectorBundle`.
-/

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-- The (0,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
@[simp]
noncomputable instance tensor0SBundle_smooth [CompleteSpace 𝕜] (s : ℕ) :
    ContMDiffVectorBundle n
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) I := by
  haveI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  haveI : (Bundle.continuousMultilinearMap.vectorPrebundle
      𝕜 s E (TangentSpace I : M → Type _)).IsContMDiff I n :=
    Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth s I n
  exact (Bundle.continuousMultilinearMap.vectorPrebundle
    𝕜 s E (TangentSpace I : M → Type _)).contMDiffVectorBundle I

/-!
## (r,s)-Tensor Bundle Instances

The (r,s) tensor bundle is defined as the hom bundle from the (0,r)- to the (0,s)-tensor
bundle, using `Bundle.ContinuousLinearMap`.
-/

/-- The total space of the (r,s)-tensor bundle carries a topology, induced by viewing it
as the hom bundle from the (0,r)- to the (0,s)-tensor bundle. -/
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a fiber bundle, as a hom bundle between two fiber bundles. -/
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundle_topology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a vector bundle with model fiber `TensorRSModel r s 𝕜 E`. -/
noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModel_normedAddCommGroup r s) (tensorRSModel_normedSpace r s) _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (fun (x : M) => Tensor0SSpace r I x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun (x : M) => Tensor0SSpace s I x)

/-- The (r,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
noncomputable instance tensorRSBundle_smooth [CompleteSpace 𝕜] (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s)
      (tensorRSBundle_vector r s) :=
  ContMDiffVectorBundle.continuousLinearMap

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
