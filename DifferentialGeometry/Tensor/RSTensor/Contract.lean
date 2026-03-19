/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Bundle
import DifferentialGeometry.Tensor.RSTensor.Curry
import DifferentialGeometry.Tensor.RSTensor.Field
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
/-!
# Interior Product and Contraction of Tensors

This file defines the interior product (contraction with a tangent vector) and contraction
with a cotangent vector (1-form) for mixed tensors at a point of a smooth manifold.

## Main Definitions

* `interior_product s x v` : contraction of a (0,s+1)-tensor with a tangent vector `v`,
  giving a (0,s)-tensor by feeding `v` into the first slot.
* `contract_covariant r s x v` : contraction of an (r,s+1)-tensor with a tangent vector,
  giving an (r,s)-tensor by post-composing with `interior_product`.
* `tensorWithCovector r x u` : the map `(0,r) →L (0,r+1)` given by `α ↦ α ⊗ u`.
* `contract_contravariant r s x u` : contraction of an (r+1,s)-tensor with a cotangent
  vector `u`, giving an (r,s)-tensor by pre-composing with `tensorWithCovector`.
* `contract_Tensor0SField_fun s α X` : pointwise contraction of a (0,s+1)-tensor field
  with a vector field, giving a (0,s)-tensor field.
* `contract_Tensor0SField s α X` : contraction of a smooth (0,s+1)-tensor field
  with a smooth vector field (a `ContMDiffSection` of the tangent bundle),
  yielding a smooth (0,s)-tensor field.

## Tags

interior product, contraction, cotangent, tensor, smooth manifold
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
## Interior product
-/

/-- Contraction of a (0,s+1)-tensor with a tangent vector `v`, giving a (0,s)-tensor
by feeding `v` into the first slot via the curry-left isomorphism. -/
noncomputable def interior_product (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x := by
  unfold Tensor0SSpace TangentSpace
  let curry_equiv := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => E) 𝕜
  exact ContinuousLinearMap.comp
    (ContinuousLinearMap.apply 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v)
    curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap

/-!
## Contraction of mixed tensors
-/

/-- Contraction of an (r,s+1)-tensor with a tangent vector `v`, giving an (r,s)-tensor
by post-composing with `interior_product s x v`. -/
noncomputable def contract_covariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (s + 1) I x)
    (Tensor0SSpace s I x)
    (interior_product s x v)

/-- The map that tensors a covariant tensor with a fixed 1-form `u`:
`(0,r) →L (0,r+1)` given by `α ↦ α ⊗ u`. -/
noncomputable def tensorWithCovector (r : ℕ) (x : M)
    (u : CotangentSpace I x) :
    Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (r + 1) I x :=
  LinearMap.toContinuousLinearMap ((tensor0S_product_bilinear r 1 x).flip u)

/-- Contraction of an (r+1,s)-tensor with a 1-form (cotangent vector) `u`,
giving an (r,s)-tensor by pre-composing with `tensorWithCovector r x u`.

Concretely, `contract_contravariant T u` sends `α : (0,r)` to `T (α ⊗ u)`. -/
noncomputable def contract_contravariant (r s : ℕ) (x : M)
    (u : CotangentSpace I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  (ContinuousLinearMap.compL 𝕜
    (Tensor0SSpace r I x)
    (Tensor0SSpace (r + 1) I x)
    (Tensor0SSpace s I x)).flip
    (tensorWithCovector r x u)

/-!
## Contraction of smooth tensor fields

We lift the pointwise `interior_product` to tensor fields: contracting a smooth
(0,s+1)-tensor field with a smooth vector field produces a smooth (0,s)-tensor field.
This corresponds to the standard result that contraction of a (0,s)-tensor field with
a smooth vector field yields a (0,s−1)-tensor field, using the Lean indexing
convention `s + 1 → s`.
-/

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]

/-- Pointwise contraction of a (0,s+1)-tensor field with a vector field,
giving a (0,s)-tensor field. At each point `x`, this feeds `X(x)` into the first
slot of the (0,s+1)-tensor `α(x)` via the currying isomorphism. -/
noncomputable def contract_Tensor0SField_fun (s : ℕ)
    (α : (x : M) → Tensor0SSpace (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → Tensor0SSpace s I x :=
  fun x => interior_product s x (X x) (α x)

/-- Contraction of a smooth (0,s+1)-tensor field with a smooth vector field
yields a smooth (0,s)-tensor field.

If `α` is a smooth section of `T⁰_{s+1}M` and `X` is a smooth section of `TM`,
then the interior product `ι_X α`, defined pointwise by `(ι_X α)_x = ι_{X(x)} α_x`,
is a smooth section of `T⁰_s M`. -/
noncomputable def contract_Tensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1)
  unfold Tensor0SField
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
  exact ⟨contract_Tensor0SField_fun s α.toFun X, by
    haveI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
    haveI := tensor0SBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1)
    intro x₀
    rw [contMDiffAt_section]
    -- The (0,s)-tensor bundle is trivial, so its trivialization is the identity.
    have triv_s : ∀ (x : M) (f : Tensor0SSpace s I x),
        (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, f⟩).2 = f := by
      intro x f
      cases s with
      | zero =>
        simp only [trivializationAt, FiberBundle.trivializationAt',
          tensor0SBundle_fiber, tensor0SBundleData, tensor0SBundleData_zero,
          tensor0S_fiberBundle_zero]
        rfl
      | succ s =>
        simp only [trivializationAt, FiberBundle.trivializationAt',
          tensor0SBundle_fiber, tensor0SBundleData]
        rfl
    simp_rw [triv_s]
    -- Goal: ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
    --   (fun x => contract_Tensor0SField_fun s α.toFun X x) x₀
    -- i.e. fun x => interior_product s x (X x) (α x) = curryLeftEquiv (α x) (X x)
    -- Following Bridge.lean VectorField.action pattern:
    set e₀ := trivializationAt E (TangentSpace I) x₀
    -- Step 1: The (0,s+1)-tensor bundle is also trivial, so α.toFun is smooth
    -- as a model-fiber-valued function.
    have triv_s1 : ∀ (x : M) (f : Tensor0SSpace (s + 1) I x),
        (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
          (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, f⟩).2 = f := by
      intro x f
      cases s with
      | zero =>
        simp only [trivializationAt, FiberBundle.trivializationAt',
          tensor0SBundle_fiber, tensor0SBundleData, tensor0SBundleData_zero]
        rfl
      | succ s =>
        simp only [trivializationAt, FiberBundle.trivializationAt']
        rfl
    -- Give α.toFun an explicit non-dependent type annotation (cf. LieDerivative.lean).
    let αFun : M → Tensor0SModel (s + 1) 𝕜 E := α.toFun
    have hα : ContMDiffAt I 𝓘(𝕜, Tensor0SModel (s + 1) 𝕜 E) n αFun x₀ := by
      have h := (contMDiffAt_section (s := α.toFun) x₀).mp (α.contMDiff x₀)
      simp_rw [triv_s1] at h
      exact h
    -- Step 2: curryLeftEquiv ∘ α gives a smooth CLM-valued map M → (E →L[𝕜] F).
    let curry_equiv := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => E) 𝕜
    have hCLM : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] Tensor0SModel s 𝕜 E) n
        (fun x => curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap (αFun x)) x₀ :=
      curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.contMDiffAt.comp x₀ hα
    -- Give e₀.symmL an explicit non-dependent type annotation (TangentSpace I x =ᵈ E).
    let symmLFun : M → (E →L[𝕜] E) := fun x => e₀.symmL 𝕜 x
    -- Step 3: e₀.symmL 𝕜 is smooth as a CLM-valued function M → (E →L[𝕜] E).
    -- By TangentBundle.symmL_trivializationAt, e₀.symmL 𝕜 x equals the manifold derivative
    -- of (extChartAt I x₀).symm evaluated at (extChartAt I x₀ x). Since the chart inverse
    -- is C^ω (from [IsManifold I ω M]), the derivative is C^n for any n.
    have hSymmL : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E) n symmLFun x₀ := by
      -- TODO: This requires either a new Mathlib lemma (Trivialization.contMDiffAt_symmL)
      -- or a proof via contDiffWithinAt_fderivWithin at the chart level.
      sorry
    -- Step 4: Compose the CLM-valued maps via clm_comp.
    -- The result: x ↦ curryLeftEquiv(α x) ∘ e₀.symmL 𝕜 x is smooth.
    have hCoord : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] Tensor0SModel s 𝕜 E) n
        (fun x => (curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap (αFun x)).comp
          (symmLFun x)) x₀ :=
      hCLM.clm_comp hSymmL
    -- Step 5: The trivialized vector field X is smooth as an E-valued map.
    have hX : ContMDiffAt I 𝓘(𝕜, E) n (fun x => (e₀ ⟨x, X x⟩).2) x₀ :=
      (Bundle.contMDiffAt_section x₀).mp X.contMDiff.contMDiffAt
    -- Step 6: Apply the smooth CLM to the smooth trivialized vector field.
    have hSmooth : ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x => (curry_equiv.toContinuousLinearEquiv.toContinuousLinearMap (αFun x)).comp
          (symmLFun x) ((e₀ ⟨x, X x⟩).2)) x₀ :=
      hCoord.clm_apply hX
    -- Step 7: Show the result equals our contraction on a neighborhood of x₀.
    -- On e₀.baseSet: e₀.symmL 𝕜 x ((e₀ ⟨x, X x⟩).2) = X x by symm_apply_apply_mk.
    apply hSmooth.congr_of_eventuallyEq
    filter_upwards
      [e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)]
    intro x hx
    dsimp only [symmLFun, αFun]
    -- LHS = curry_equiv (α x) (X x) by definition.
    -- RHS = curry_equiv (α x) (symmL x (trivialized X x)).
    -- These are equal because symmL x (trivialized X x) = X x on the base set.
    unfold contract_Tensor0SField_fun interior_product
    simp only [ContinuousLinearMap.comp_apply]
    erw [Trivialization.symm_apply_apply_mk e₀ hx]⟩

end FieldContraction

end
end Tensor0SBundle
