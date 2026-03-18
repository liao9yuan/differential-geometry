/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# Finite-Dimensionality, Dimension, and Basis of Tensor Spaces

This file establishes finite-dimensionality results for the multilinear map spaces underlying
(0,s)-tensors, computes their dimension as `(finrank 𝕜 E) ^ s`, and constructs an explicit
basis indexed by `Fin s → Fin d` from any basis of `E`.

## Main Definitions

* `multilinearMap_finiteDimensional s` : `MultilinearMap 𝕜 (Fin s → E) 𝕜` is finite-dimensional.
* `continuousMultilinearMap_finiteDimensional s` : `Tensor0SModel s 𝕜 E` is finite-dimensional.
* `continuousMultilinearMap_finiteDimensional_nested r r'` : the nested continuous multilinear
  map space is finite-dimensional.
* `tensor0SModel_finiteDimensional s` : alias for `continuousMultilinearMap_finiteDimensional`.
* `finrank_tensor0SModel s` : `finrank 𝕜 (Tensor0SModel s 𝕜 E) = (finrank 𝕜 E) ^ s`.
* `finrank_tensor0SSpace n x` : `finrank 𝕜 (Tensor0SSpace n I x) = (finrank 𝕜 E) ^ n`.
* `tensor0SModel_basisElem b s σ` : the basis element at `σ : Fin s → Fin d`, defined as
  `v ↦ ∏ j, b.coord (σ j) (v j)`.
* `tensor0SModel_basis b s` : the explicit basis for `Tensor0SModel s 𝕜 E`.

## Tags

tensor, basis, finite-dimensional, multilinear map, coordinate functional
-/

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

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

/-- Alias for `continuousMultilinearMap_finiteDimensional`. -/
noncomputable instance tensor0SModel_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
  continuousMultilinearMap_finiteDimensional s

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
## Dimension results
-/

/-- The dimension of `Tensor0SModel s 𝕜 E` is `(finrank 𝕜 E) ^ s`. -/
theorem finrank_tensor0SModel (s : ℕ) :
    Module.finrank 𝕜 (Tensor0SModel s 𝕜 E) = (Module.finrank 𝕜 E) ^ s := by
  induction s with
  | zero =>
    have e := continuousMultilinearCurryFin0 𝕜 E 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    simp [pow_zero, Module.finrank_self]
  | succ s ih =>
    have e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => E) 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    haveI : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) := tensor0SModel_finiteDimensional s
    haveI : Module.Free 𝕜 E := inferInstance
    let F := Tensor0SModel s 𝕜 E
    haveI : Module.Free 𝕜 F := inferInstance
    have e2 : (E →L[𝕜] F) ≃ₗ[𝕜] (E →ₗ[𝕜] F) := LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq, Module.finrank_linearMap 𝕜 𝕜, ih]
    ring

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The fiber `Tensor0SSpace s I x` is finite-dimensional, since it injects into the
space of multilinear maps on a finite-dimensional space. -/
instance tensor0SSpace_finiteDimensional (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) := by
  unfold Tensor0SSpace
  unfold TangentSpace
  exact continuousMultilinearMap_finiteDimensional s

/-- The fiber `TensorRSSpace r s I x` is finite-dimensional, as a space of continuous
linear maps between finite-dimensional spaces. -/
instance tensorRSSpace_finiteDimensional (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  infer_instance

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

/-!
## Explicit basis construction
-/

/-- The tensor product basis element of `Tensor0SModel s 𝕜 E` at index `σ : Fin s → Fin d`.
Given a basis `b` for `E`, this is the continuous multilinear map
`v ↦ ∏ j, b.coord (σ j) (v j)`, i.e. the tensor product of coordinate functionals
`b.coord(σ 0) ⊗ ⋯ ⊗ b.coord(σ (s-1))`. -/
noncomputable def tensor0SModel_basisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 E) (s : ℕ)
    (σ : Fin s → Fin d) : Tensor0SModel s 𝕜 E :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j)))

/-- Evaluating the basis element `σ` at the basis vectors `(b (σ' j))_j` gives the
Kronecker delta: `1` if `σ = σ'` and `0` otherwise. -/
theorem tensor0SModel_basisElem_apply {d : ℕ} (b : Module.Basis (Fin d) 𝕜 E) (s : ℕ)
    (σ σ' : Fin s → Fin d) :
    tensor0SModel_basisElem b s σ (fun j => b (σ' j)) =
    if σ = σ' then 1 else 0 := by
  simp_rw [tensor0SModel_basisElem, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : σ = σ'
  · subst h; simp
  · simp only [h, ite_false]
    have ⟨j, hj⟩ : ∃ j, σ j ≠ σ' j := by contrapose! h; exact funext h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj))

/-- The tensor product basis elements are linearly independent. -/
theorem tensor0SModel_basisElem_linearIndependent {d : ℕ} (b : Module.Basis (Fin d) 𝕜 E) (s : ℕ) :
    LinearIndependent 𝕜 (tensor0SModel_basisElem b s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ'
  have h1 : (∑ σ : Fin s → Fin d, c σ • tensor0SModel_basisElem b s σ)
      (fun j => b (σ' j)) = 0 := by rw [hc]; rfl
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    tensor0SModel_basisElem_apply] at h1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rwa [smul_eq_mul, mul_one] at h1

/-- An explicit basis for `Tensor0SModel s 𝕜 E` indexed by `Fin s → Fin d`, where
`b : Module.Basis (Fin d) 𝕜 E`. The basis element at `σ` is the tensor product of coordinate
functionals `b.coord(σ 0) ⊗ ⋯ ⊗ b.coord(σ (s-1))`, i.e. the continuous multilinear map
`v ↦ ∏ j, b.coord (σ j) (v j)`. -/
noncomputable def tensor0SModel_basis {d : ℕ} (b : Module.Basis (Fin d) 𝕜 E) (s : ℕ) :
    Module.Basis (Fin s → Fin d) 𝕜 (Tensor0SModel s 𝕜 E) :=
  Module.Basis.mk (tensor0SModel_basisElem_linearIndependent b s)
    ((tensor0SModel_basisElem_linearIndependent b s).span_eq_top_of_card_eq_finrank' (by
      have hd : Module.finrank 𝕜 E = d := by
        rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, finrank_tensor0SModel, hd])).ge

end
end Tensor0SBundle
