/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.DualFiber
import DifferentialGeometry.VectorBundle.Dual
import Mathlib.Geometry.Manifold.VectorBundle.Hom
/-!
# Bundle instances for `Bundle.dual` of the multilinear bundle

This file establishes the topological, fiber bundle, vector bundle, and smooth vector bundle
instances for `Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`, the dual bundle
of the `r`-multilinear bundle. The fiber at `x : B` is

  `Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜`.

The bundle is constructed via `Bundle.ContinuousLinearMap` (the hom bundle from the
multilinear bundle into the trivial `𝕜`-bundle). We provide the bundle instances
explicitly (rather than relying on instance synthesis) to disambiguate the topology
diamond on `Bundle.continuousMultilinearMap` fibers.

This file mirrors the pattern of `Tensor/Mixed/Bundle.lean`.

## Main Definitions

* `Bundle.continuousMultilinearMap.dualBundleTopology`: topology on the total space.
* `Bundle.continuousMultilinearMap.dualBundleFiberBundle`: fiber bundle instance.
* `Bundle.continuousMultilinearMap.dualBundleVectorBundle`: vector bundle instance.
* `Bundle.continuousMultilinearMap.dualBundleSmoothVectorBundle`: smooth vector bundle.

## Tags

multilinear map, dual bundle, vector bundle, hom bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r : ℕ}

/-!
## Bundle instances

The dual bundle of the multilinear bundle is the hom bundle from the multilinear bundle to
the trivial `𝕜`-bundle, using `Bundle.ContinuousLinearMap`.
-/

/-- Topology on the total space of `Bundle.dual 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E)`,
induced by viewing it as the hom bundle from the multilinear bundle to the trivial `𝕜`-bundle. -/
noncomputable instance dualBundleTopology (r : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

/-- The dual bundle of the multilinear bundle is a fiber bundle. -/
noncomputable instance dualBundleFiberBundle (r : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      (dualBundleTopology r) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

/-- The dual bundle of the multilinear bundle is a vector bundle. -/
noncomputable instance dualBundleVectorBundle (r : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    𝕜
    (fun _ : B => 𝕜)

/-!
## Smooth bundle instance
-/

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

/-- The dual bundle of the multilinear bundle is a `C^n` vector bundle. -/
noncomputable instance dualBundleSmoothVectorBundle (r : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (dualBundleTopology r) _
      (dualBundleFiberBundle r)
      (dualBundleVectorBundle r) :=
  ContMDiffVectorBundle.continuousLinearMap

end smooth

/-!
## Fiber normed instances

The fiber type `Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜` inherits normed
structure via the topology equality `topology_eq` (from `Multilinear/Fiber.lean`), which
shows that the bundle and norm topologies on each multilinear fiber agree. -/

/-- The CLM from the multilinear bundle fiber (with bundle topology) to `𝕜` is the same type
as the CLM from `ContinuousMultilinearMap` (with norm topology) to `𝕜`, since the topologies
agree by `topology_eq`. -/
private theorem dualBundleFiber_type_eq (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜 →L[𝕜] 𝕜) := by
  unfold Bundle.continuousMultilinearMap
  congr 1
  exact topology_eq (𝕜 := 𝕜) (F := F) (E := E) _ x

/-- Transport `NormedAddCommGroup` and `NormedSpace` from the norm-topology type. -/
private def dualBundleFiber_normedInstances (r : ℕ) (x : B) :
    Σ' (ng : NormedAddCommGroup
          (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)),
      @NormedSpace 𝕜
        (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜)
        _ ng.toSeminormedAddCommGroup :=
  (dualBundleFiber_type_eq (𝕜 := 𝕜) (F := F) (E := E) r x) ▸ ⟨inferInstance, inferInstance⟩

/-- The dual-of-multilinear fiber is a normed additive commutative group. -/
instance dualBundleFiber_instNormedAddCommGroup (r : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).1

/-- The dual-of-multilinear fiber is a normed `𝕜`-module. -/
instance dualBundleFiber_instNormedSpace (r : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  (dualBundleFiber_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r x).2

/-- Scalar multiplication on the dual-of-multilinear fiber is continuous. -/
instance dualBundleFiber_instContinuousSMul (r : ℕ) (x : B) :
    ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜))

/-!
## Continuous linear equivalence to model fiber

The CLE from the dual-of-multilinear fiber to its model fiber is constructed via
`ContinuousLinearEquiv.arrowCongr` applied to `continuousLinearEquivAt` for the source
multilinear bundle and the identity on the codomain `𝕜`. -/

/-- The continuous linear equivalence from the dual-of-multilinear fiber at `x` to the
model fiber `MLF →L[𝕜] 𝕜`, constructed via `arrowCongr` of the multilinear CLE and the
identity on `𝕜`. -/
def dualBundleContinuousLinearEquivAt (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).arrowCongr
    (ContinuousLinearEquiv.refl 𝕜 𝕜)

/-!
## Coercion to model fiber
-/

/-- Coerce a dual-of-multilinear fiber element to the model fiber.
This is the forward direction of `dualBundleContinuousLinearEquivAt`. -/
def dualBundleToModel {r : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜 :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).toContinuousLinearMap T

/-- `dualBundleToModel` as a bundled `ContinuousLinearMap`. -/
def dualBundleToModelL (r : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).toContinuousLinearMap

/-- Construct a dual-of-multilinear fiber element from a model fiber element.
This is the inverse of `dualBundleToModel`. -/
def dualBundleOfModel {r : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜] 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜] 𝕜 :=
  (dualBundleContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).symm.toContinuousLinearMap f

/-!
## Inverse trivialization formula for the dual bundle

The inverse trivialization `(trivAt (F*) (dual E) x₀).symmL 𝕜 x ζ` (for `ζ : F →L[𝕜] 𝕜`
and `x ∈ baseSet`) equals `ζ.comp ((trivAt F E x₀).continuousLinearMapAt 𝕜 x)`, following
from the hom bundle's pretrivialization formula (with trivial target). -/

/-- The inverse trivialization of `Bundle.dual 𝕜 E` at `x₀`, applied to a model-fiber
element `ζ : F →L[𝕜] 𝕜` at point `x ∈ baseSet`, equals `ζ.comp ((trivAt F E x₀).cLMA x)`.
This is the analog of `triv_symmL_eq_compContinuousLinearMap` for the dual bundle. -/
theorem dualBundle_triv_symmL_eq_comp (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (ζ : F →L[𝕜] 𝕜) (v : E x) :
    ((trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀).symmL 𝕜 x ζ) v =
      ζ ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) := by
  set e := trivializationAt (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x₀ with he_def
  have hbase : x ∈ e.baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp [trivializationAt, FiberBundle.trivializationAt']⟩
  have hsymmL : (e.symmL 𝕜 x ζ : Bundle.dual 𝕜 E x) = e.symm x ζ := by
    simp [Trivialization.symmL_apply]
  rw [hsymmL]
  have h_rt : (e ⟨x, e.symm x ζ⟩ : B × _) = (x, ζ) := e.apply_mk_symm hbase ζ
  have h_snd : (e ⟨x, e.symm x ζ⟩ : B × _).2 = ζ := congrArg Prod.snd h_rt
  have hxTriv : x ∈ (trivializationAt 𝕜 (fun _ : B => 𝕜) x₀).baseSet := by
    show x ∈ Set.univ; trivial
  have h_fwd : (e ⟨x, e.symm x ζ⟩).2
      ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) =
    ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv)
      ((e.symm x ζ)
        ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt F E x₀) x hx).symm
          ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v)))) := by
    rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates_eq hx hxTriv]
    rfl
  rw [h_snd] at h_fwd
  have h_triv : ∀ (z : 𝕜),
      ((Trivialization.continuousLinearEquivAt 𝕜 (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv
        : 𝕜 →L[𝕜] 𝕜) : 𝕜 → 𝕜) z = z := by intro z; rfl
  conv at h_fwd => rhs; rw [show (Trivialization.continuousLinearEquivAt 𝕜
    (trivializationAt 𝕜 (Trivial B 𝕜) x₀) x hxTriv) _ = _ from h_triv _]
  conv_lhs => rw [show v = ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm
    ((trivializationAt F E x₀).continuousLinearMapAt 𝕜 x v) from
    ((trivializationAt F E x₀).symmL_continuousLinearMapAt hx v).symm]
  exact h_fwd.symm

end Bundle.continuousMultilinearMap

end
