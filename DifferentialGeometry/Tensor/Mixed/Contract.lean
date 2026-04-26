/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Mixed.Product
import DifferentialGeometry.Tensor.Product.Contract
import DifferentialGeometry.Tensor.Multilinear.Dual

/-!
# Contraction of Mixed `(1,1)`-Tensor Fields

This file defines the contraction (trace) of a mixed `(1,1)`-tensor field via the
model-fiber trace. The key steps are:

1. Define `modelTraceCLM : (F_MLF →L[𝕜] F_MLF) →L[𝕜] 𝕜`, the trace on the model fiber.
2. At each point `x`, conjugate `T(x)` into the model fiber using the trivialization CLE:
   `contract(T)(x) := modelTraceCLM (CLE_x ∘ T(x) ∘ CLE_x⁻¹)`.
3. Conjugation invariance of the trace (`tr(ΦAΦ⁻¹) = tr(A)`) makes this
   trivialization-independent.
4. Smoothness follows from `contMDiffAt_const.clm_apply` applied to the coordinate
   representation of `T`, transferred via `congr_of_eventuallyEq`.

This approach works entirely within the hom bundle (direct `FiberBundle`/`VectorBundle`
instances), avoiding tensor product bundles and their associated instance diamonds.

## Tags

contraction, trace, mixed tensor, tensor field, vector bundle
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

/-!
## Model-fiber trace

Defined in a minimal section to avoid pulling in bundle variables.
-/

section ModelTrace

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

-- Abbreviation for readability (not a notation to avoid quotPrecheck issues)
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The trace on a finite-dimensional endomorphism space `(V →L[𝕜] V) →L[𝕜] 𝕜`.

Defined as `contractLeft ∘ dualTensorHomEquiv.symm` (the evaluation pairing composed
with the inverse of the canonical isomorphism `M* ⊗ M ≃ End(M)`), promoted to a CLM
via finite-dimensionality. -/
noncomputable def modelTraceCLM :
    (V →L[𝕜] V) →L[𝕜] 𝕜 := sorry

/-- Conjugation invariance of the trace: `tr(Φ A Φ⁻¹) = tr(A)`. -/
theorem modelTraceCLM_conj
    (Φ : V ≃L[𝕜] V) (A : V →L[𝕜] V) :
    modelTraceCLM 𝕜 V
      (Φ.toContinuousLinearMap.comp (A.comp Φ.symm.toContinuousLinearMap)) =
    modelTraceCLM 𝕜 V A := sorry

end ModelTrace

/-!
## Contraction of mixed `(1,1)`-sections
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

namespace MixedSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

local notation "MLF" => fun x => Bundle.continuousMultilinearMap 𝕜 1 F E x
local notation "F_MLF" => ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => F) 𝕜

local instance : FiniteDimensional 𝕜 F_MLF :=
  continuousMultilinearMap_finiteDimensional 1

/-- Contraction of a smooth `(1,1)`-mixed section to a smooth scalar function.

At each point `x`, the section value `T(x) : MLF(x) →L MLF(x)` is conjugated into
the model fiber by the trivialization CLE, and the model-fiber trace is applied.
Conjugation invariance ensures the result is independent of the trivialization.
Smoothness follows from `contMDiffAt_const.clm_apply` on the coordinate representation,
transferred by `congr_of_eventuallyEq`. -/
noncomputable def contract_MixedSection_11
    (T : MixedSection 𝕜 F IB E n 1 1) :
    C^n⟮IB, B; 𝓘(𝕜), 𝕜⟯ :=
  ⟨fun x =>
    let e := (trivializationAt F_MLF MLF x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F_MLF MLF x)
    modelTraceCLM 𝕜 F_MLF (e.toContinuousLinearMap.comp
      ((T x).comp e.symm.toContinuousLinearMap)),
   by
    intro x₀
    -- The coordinate representation of T in the trivialization at x₀ is smooth:
    --   x ↦ (triv_{x₀} ⟨x, T x⟩).2 : F_MLF →L F_MLF
    -- which equals CLE_{x₀,x} ∘ T(x) ∘ CLE_{x₀,x}⁻¹ (the hom bundle inCoordinates).
    -- Applying the constant CLM `modelTraceCLM` gives a smooth function.
    -- By conjugation invariance, this equals our definition near x₀.
    sorry⟩

end MixedSection

end
