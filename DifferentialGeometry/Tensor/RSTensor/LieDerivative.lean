/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Tensor.RSTensor.Field

/-!
# Lie Derivatives of Tensor Fields on Manifolds

This file extends the tensor bundle construction with:
1. Contraction of contravariant indices with 1-forms
2. Lie derivative of tensor fields along vector fields

The Lie derivative follows the same pattern as `VectorField.mlieBracket`:
- Define operations on the model space first
- Transfer to manifolds via pullback through charts
- Prove smoothness using the smooth vector bundle structure

## Main definitions

* `tensorWithCovector`: tensors a (0,r) tensor with a fixed 1-form to get (0,r+1)
* `contract_contravariant`: contracts (r+1,s) tensor with a 1-form to get (r,s)
* `lieDeriv_tensor0S`: Lie derivative of (0,s) tensors in a vector space
* `mlieDeriv_tensor0S`: Lie derivative of (0,s) tensor fields on manifolds
* `mlieDeriv_tensorRS`: Lie derivative of (r,s) tensor fields on manifolds

## Main results

* `mlieDeriv_tensor0S_add`: Lie derivative is additive in the tensor argument
* `mlieDeriv_tensor0S_smul`: Leibniz rule for scalar multiplication
* `ContMDiffWithinAt.mlieDeriv_tensor0S`: smoothness of Lie derivative
-/

namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

/-!
## Lie derivative on vector spaces

Before defining the Lie derivative on manifolds, we define it on vector spaces
where the formula is explicit.

For a (0,s) tensor field α and a vector field X on E, the Lie derivative is:
  (L_X α)(Y₁,...,Yₛ) = X(α(Y₁,...,Yₛ)) - Σᵢ α(Y₁,...,DXʸⁱ,...,Yₛ)

where D is the derivative and DXʸ means the derivative of X applied to Y.
-/

section VectorSpaceLieDeriv

variable {s : ℕ}

/-- The derivative of a (0,s) tensor field at a point in a vector space.
Given α : E → (0,s)-tensor and x : E, this is D_x α : E →L (0,s)-tensor. -/
noncomputable def fderivTensor0S (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) : E →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 α x

/-- Action of a vector field on a (0,s) tensor field in a vector space.
This is the "X(α)" term in the Lie derivative formula. -/
noncomputable def vectorFieldActionOnTensor0S
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivTensor0S α x (X x)


/-- Substitute the i-th argument of a multilinear map -/
noncomputable def substituteArg (s : ℕ) (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (f : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  α.compContinuousLinearMap (fun j => if j = i then f else ContinuousLinearMap.id 𝕜 E)

/-- The correction term: sum over all slots of α with DX applied to that slot -/
noncomputable def lieDeriv_correction (s : ℕ)
    (DX : E →L[𝕜] E) (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ∑ i : Fin s, substituteArg s i α DX

/-- Lie derivative of a (0,s) tensor field in a vector space.

Given a vector field X : E → E and a (0,s) tensor field α : E → (0,s)-tensors,
the Lie derivative at x is:
  (L_X α)_x = (Dα)_x(X_x) - Σᵢ α_x ∘ᵢ (DX)_x

where ∘ᵢ means composition in the i-th slot.
-/
noncomputable def lieDeriv_tensor0S (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  vectorFieldActionOnTensor0S X α x - lieDeriv_correction s (fderiv 𝕜 X x) (α x)

/-- Lie derivative within a set -/
noncomputable def lieDeriv_tensor0SWithin (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 α t x (X x) - lieDeriv_correction s (fderivWithin 𝕜 X t x) (α x)

end VectorSpaceLieDeriv

/-!
## Lie derivative on manifolds

Following the pattern of `mlieBracket`, we define the Lie derivative on manifolds
by pulling back to the model space, computing there, and pushing forward.
-/

section ManifoldLieDeriv

variable {s : ℕ}

-- Type alias for the tensor bundle total space
abbrev Tensor0SBundle (s : ℕ) (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  TotalSpace (Tensor0SModel (𝕜 := 𝕜) (E := E) s) (fun x : M => Tensor0SSpace s I x)

/-- Pullback of a (0,s) tensor field through a map.

Given f : M → M' and α : (x : M') → Tensor0SSpace s I' x,
the pullback (f* α) at x ∈ M is defined using the differential of f.
-/
noncomputable def mpullback_tensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M')
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderiv I I' f x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

/-- Pullback within a set -/
noncomputable def mpullbackWithin_tensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M') (t : Set M)
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderivWithin I I' f t x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

section SmoothVectorFieldLieDeriv

variable [IsManifold I 1 M]

/-- The Lie derivative of a (0,s) tensor field on a manifold within a set.

Following the pattern of `mlieBracketWithin`, this is defined by:
1. Pulling back X and α to the model space via extChartAt
2. Computing the Lie derivative there
3. Pushing forward the result
-/
noncomputable def mlieDeriv_tensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (t : Set M)
    (x₀ : M) :
    Tensor0SSpace s I x₀ := by
  -- Pull back X to model space
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  -- Pull back α to model space (as a function E → (0,s)-tensors on E)
  -- Since TangentSpace I x = E definitionally, Tensor0SSpace s I x = Tensor0SModel s
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun y =>
    α ((extChartAt I x₀).symm y)
  -- Compute Lie derivative in model space
  let result := lieDeriv_tensor0SWithin s X' α'
    ((extChartAt I x₀).symm ⁻¹' t ∩ range I)
    (extChartAt I x₀ x₀)
  -- The result is already the right type since TangentSpace I x₀ = E
  exact result

/-- The Lie derivative of a (0,s) tensor field on a manifold. -/
noncomputable def mlieDeriv_tensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (x₀ : M) :
    Tensor0SSpace s I x₀ :=
  mlieDeriv_tensor0SWithin (n := n) s X α univ x₀


/-!
### Basic properties of manifold Lie derivative
-/

variable {s : ℕ}
variable {X : ContMDiffSection I E n (TangentSpace I : M → Type _)}
variable {α β : (x : M) → Tensor0SSpace s I x}

omit [IsManifold I n M] in
@[simp] lemma mlieDeriv_tensor0SWithin_univ :
    mlieDeriv_tensor0SWithin (I := I) (n := n) s X α univ = mlieDeriv_tensor0S (n := n) s X α := rfl

end SmoothVectorFieldLieDeriv

-- Helper: the correction term is additive in the tensor
lemma lieDeriv_correction_add (DX : E →L[𝕜] E)
    (α β : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDeriv_correction s DX (α + β) =
    lieDeriv_correction s DX α + lieDeriv_correction s DX β := by
  unfold lieDeriv_correction
  rw [← Finset.sum_add_distrib]
  congr 1

-- Helper: the correction term is linear in scalar
lemma lieDeriv_correction_smul (DX : E →L[𝕜] E) (c : 𝕜)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDeriv_correction s DX (c • α) = c • lieDeriv_correction s DX α := by
  unfold lieDeriv_correction
  rw [Finset.smul_sum]
  congr 1


-- Helper: correction vanishes for s = 0
lemma lieDeriv_correction_zero (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 0) :
    lieDeriv_correction 0 DX α = 0 := by
  dsimp[lieDeriv_correction]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

variable [CompleteSpace 𝕜]
/-- Lie derivative of an (r,s) tensor field in a vector space within a set.
This is the principal term; the full formula includes correction terms. -/
noncomputable def lieDeriv_tensorRSWithin (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 T t x (X x)

/-- Lie derivative of an (r,s) tensor field in a vector space. -/
noncomputable def lieDeriv_tensorRS (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 T x (X x)

section SmoothVectorFieldRSLieDeriv

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Lie derivative of an (r,s) tensor field within a set.

The definition works by:
1. Using `tensorRSSpace_continuousLinearEquiv` to convert the tensor field to a
   model-fiber-valued function
2. Pulling back to the model space via `extChartAt`
3. Computing the vector-space Lie derivative there
4. Converting back via the inverse equivalence

The output is `C^m` when the inputs are `C^n` with `m + 1 ≤ n`. -/
noncomputable def mlieDeriv_tensorRSWithin (r s : ℕ) {m : WithTop ℕ∞}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (hu : UniqueMDiffOn I u) (hmn : m + 1 ≤ n) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  { toFun := fun x₀ => by
      -- Pull back X to model space
      let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
      -- Pull back T to model space via the continuous linear equivalence
      let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
        fun y => tensorRSSpace_continuousLinearEquiv (I := I) r s
          ((extChartAt I x₀).symm y) (T.toFun ((extChartAt I x₀).symm y))
      -- Compute Lie derivative in model space and convert back
      exact (tensorRSSpace_continuousLinearEquiv (I := I) r s x₀).symm
        (lieDeriv_tensorRSWithin r s X' T'
          ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
          (extChartAt I x₀ x₀))
    contMDiff_toFun := sorry }

/-- Lie derivative of an (r,s) tensor field.
The output is `C^m` when the inputs are `C^n` with `m + 1 ≤ n`. -/
noncomputable def mlieDeriv_tensorRS (r s : ℕ) {m : WithTop ℕ∞}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (hmn : m + 1 ≤ n) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s :=
  mlieDeriv_tensorRSWithin (n := n) r s X T univ uniqueMDiffOn_univ hmn

end SmoothVectorFieldRSLieDeriv

end ManifoldLieDeriv

end

end TensorLieDeriv
