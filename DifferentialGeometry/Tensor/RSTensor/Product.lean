/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Bundle
import DifferentialGeometry.Tensor.Product
/-!
# Tensor Products of (r,s)-Tensors

This file defines pointwise tensor products of covariant and mixed tensors at each
point of a smooth manifold.

## Main Definitions

* `multilinearMap_finiteDimensional s` : `MultilinearMap 𝕜 (Fin s → E) 𝕜` is
  finite-dimensional.
* `continuousMultilinearMap_finiteDimensional s` : `Tensor0SModel s 𝕜 E` is
  finite-dimensional.
* `tensor0S_product_fun s q x α β` : the explicit (0,s+q)-tensor formed by concatenating
  the inputs of `α : Tensor0SSpace s` and `β : Tensor0SSpace q`.
* `tensor0S_product_bilinear s q x` : bilinear map
  `Tensor0SSpace s ⊗ Tensor0SSpace q →ₗ Tensor0SSpace (s+q)`.
* `tensor0S_fromTensor s q x` : the induced linear map
  `Tensor0SSpace s ⊗[𝕜] Tensor0SSpace q →ₗ Tensor0SSpace (s+q)` via
  `TensorProduct.lift`.
* `tensor0S_curryLeft r r' x` : CLM currying a (0,r+r')-tensor along `Fin r ⊕ Fin r'`.
* `tensor0S_uncurryLeft r r' x` : inverse of `tensor0S_curryLeft`.
* `finrank_tensor0SSpace n x` : `finrank 𝕜 (Tensor0SSpace n I x) = (finrank 𝕜 E) ^ n`.
* `tensor0S_equiv r r' x` : linear equivalence
  `Tensor0SSpace (r+r') ≃ₗ[𝕜] Tensor0SSpace r ⊗[𝕜] Tensor0SSpace r'`.
* `tensorRS_product r s r' s' x T T'` : the (r+r',s+s')-tensor `T ⊗ T'`.

## Tags

tensor product, covariant tensor, mixed tensor, smooth manifold
-/

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-!
## Finite-dimensionality instances
-/

/-- The space of multilinear maps from `s` copies of a finite-dimensional space `E` to `𝕜`
is finite-dimensional. -/
noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  haveI : Module.Finite 𝕜 E := inferInstance
  haveI : Module.Free 𝕜 E := inferInstance
  haveI : Module.Finite 𝕜 𝕜 := inferInstance
  haveI : Module.Free 𝕜 𝕜 := inferInstance
  infer_instance

/-- The model fiber `Tensor0SModel s 𝕜 E` is finite-dimensional, by injecting into the
space of (not necessarily continuous) multilinear maps. -/
noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) := by
  haveI : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- The nested space of continuous multilinear maps `(Fin r → E) → (Fin r' → E) → 𝕜`
is finite-dimensional, via the currying isomorphism with `Fin (r + r') → E → 𝕜`. -/
noncomputable instance continuousMultilinearMap_finiteDimensional_nested (r r' : ℕ) :
    FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜)) := by
  let e1 := ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 (finSumFinEquiv (m := r) (n := r')).symm
  let e2 := ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜) :=
    continuousMultilinearMap_finiteDimensional (r + r')
  exact LinearEquiv.finiteDimensional (e1.trans e2).toLinearEquiv

/-!
## Tensor product of (0,s)- and (0,q)-tensors
-/

/-- The pointwise tensor product of a (0,s)-tensor `α` and a (0,q)-tensor `β`,
yielding a (0,s+q)-tensor by concatenating their inputs. -/
noncomputable def tensor0S_product_fun (s q : ℕ)
    (x : M) (α : Tensor0SSpace s I x) (β : Tensor0SSpace q I x) :
    Tensor0SSpace (s + q) I x :=
  (α.smulRight β).uncurrySum.domDomCongr finSumFinEquiv

/-- The tensor product of (0,s)- and (0,q)-tensors is bilinear in both factors,
giving a bilinear map `Tensor0SSpace s ⊗ Tensor0SSpace q →ₗ Tensor0SSpace (s+q)`.

Equivalently, this is `(tensor0S_equiv s q x).symm ∘ₗ TensorProduct.mk 𝕜 _ _`: the
abstract bilinear map from the universal property of tensor products, transported
back to the concrete (0,s+q)-tensor space via `tensor0S_equiv`. -/
noncomputable def tensor0S_product_bilinear (s q : ℕ) (x : M) :
    Tensor0SSpace s I x →ₗ[𝕜] Tensor0SSpace q I x →ₗ[𝕜] Tensor0SSpace (s + q) I x :=
  LinearMap.mk₂ 𝕜 (tensor0S_product_fun s q x)
    (fun α₁ α₂ β => by unfold tensor0S_product_fun; ext m; simp [add_smul])
    (fun c α β => by
      unfold tensor0S_product_fun; ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by unfold tensor0S_product_fun; ext m; simp [smul_add])
    (fun c α β => by
      unfold tensor0S_product_fun; ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)

/-- The tensor product map lifted to the abstract tensor product via the universal property:
`Tensor0SSpace s ⊗[𝕜] Tensor0SSpace q →ₗ Tensor0SSpace (s+q)`. -/
noncomputable def tensor0S_fromTensor (s q : ℕ) (x : M) :
    TensorProduct 𝕜 (Tensor0SSpace s I x) (Tensor0SSpace q I x) →ₗ[𝕜]
    Tensor0SSpace (s + q) I x :=
  TensorProduct.lift (tensor0S_product_bilinear s q x)

/-!
## Currying and dimension results
-/

/-- Curry a (0,r+r')-tensor into a multilinear map from `r` tangent vectors to (0,r')-tensors,
using the decomposition `Fin (r+r') ≃ Fin r ⊕ Fin r'`. -/
noncomputable def tensor0S_curryLeft (r r' : ℕ) (x : M) :
    Tensor0SSpace (r + r') I x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => TangentSpace I x)
      (Tensor0SSpace r' I x) := by
  unfold Tensor0SSpace TangentSpace
  let e1 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 :=
    ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 finSumFinEquiv.symm
  let e2 : ContinuousMultilinearMap 𝕜 (fun _ : Fin r ⊕ Fin r' => E) 𝕜 ≃ₗᵢ[𝕜]
           ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E)
             (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => E) 𝕜) :=
    ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') E 𝕜
  exact (e1.trans e2).toContinuousLinearMap

/-- Uncurry a multilinear map from `r` tangent vectors to (0,r')-tensors back into
a (0,r+r')-tensor, the inverse of `tensor0S_curryLeft`. -/
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
  exact (e1.trans e2).symm.toContinuousLinearMap

/-- The dimension of the space of (0,n)-tensors at any point equals `(dim E)^n`. -/
lemma finrank_tensor0SSpace (n : ℕ) (x : M) :
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
    have e2 : (E →L[𝕜] F) ≃ₗ[𝕜] (E →ₗ[𝕜] F) := LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq, Module.finrank_linearMap 𝕜 𝕜, ih]
    ring

/-- Linear equivalence `Tensor0SSpace (r+r') ≃ₗ[𝕜] Tensor0SSpace r ⊗[𝕜] Tensor0SSpace r'`
at each point, obtained by dimension counting:
both sides have dimension `(finrank 𝕜 E)^r · (finrank 𝕜 E)^r'`. -/
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
    rw [Module.finrank_tensorProduct,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r x,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) r' x,
        finrank_tensor0SSpace (𝕜 := 𝕜) (E := E) (I := I) (M := M) (r + r') x,
        pow_add])

/-!
## Tensor product of (r,s)- and (r',s')-tensors
-/

/-- Given T : (r,s) and T' : (r',s'), we define T ⊗ T' : (r+r',s+s').

Concretely, via `tensor0S_equiv`, the (0,r+r')-tensor space is identified with
`(0,r) ⊗[𝕜] (0,r')`, and we transport `TensorProduct.mapL T T'` (from
`DifferentialGeometry.Tensor.Product`) along these isomorphisms:

  `tensorRS_product T T' =
    (tensor0S_equiv s s').symm ∘ₗ TensorProduct.map T T' ∘ₗ tensor0S_equiv r r'`

We use the algebraic `TensorProduct.map` with a single outer `LinearMap.toContinuousLinearMap`,
since composing algebraic linear maps avoids synthesizing `TopologicalSpace` instances on the
intermediate tensor products `(0,r) ⊗[𝕜] (0,r')` and `(0,s) ⊗[𝕜] (0,s')`.
-/
-- TODO: Add notation for tensor product of tensors using ⊗ symbol
-- TODO: Define tensor product on sections/bundles, not just pointwise
-- TODO: Show that the product of smooth tensor fields is again smooth
noncomputable def tensorRS_product (r s r' s' : ℕ) (x : M)
    (T : TensorRSSpace r s I x) (T' : TensorRSSpace r' s' I x) :
    TensorRSSpace (r + r') (s + s') I x :=
  LinearMap.toContinuousLinearMap
    ((tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s s' x).symm.toLinearMap ∘ₗ
     TensorProduct.map T.toLinearMap T'.toLinearMap ∘ₗ
     (tensor0S_equiv (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r r' x).toLinearMap)

end
end Tensor0SBundle
