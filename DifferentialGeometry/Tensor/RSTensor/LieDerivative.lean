/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Tensor.RSTensor.Bundle
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
    [TopologicalSpace M] [ChartedSpace H M] :=
  TotalSpace (Tensor0SModel (𝕜 := 𝕜) (E := E) s) (fun x : M => Tensor0SSpace s I x)

/-- Pullback of a (0,s) tensor field through a map.

Given f : M → M' and α : (x : M') → Tensor0SSpace s I' x,
the pullback (f* α) at x ∈ M is defined using the differential of f.
-/
noncomputable def mpullback_tensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
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
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
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

variable [IsManifold I ω M]

/-- Lie derivative of an (r,s) tensor field within a set.
The output is `C^m` when the inputs are `C^n` with `m + 1 ≤ n` (one derivative is lost). -/
noncomputable def mlieDeriv_tensorRSWithin (r s : ℕ) {m : WithTop ℕ∞}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (hu : UniqueMDiffOn I u) (hmn : m + 1 ≤ n) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s :=
  -- Introduce RS-tensor bundle instances at level m (the output smoothness)
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s
  letI := tensorRSBundle_fiber    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s
  letI := tensorRSBundle_vector   (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s
  { toFun := fun x₀ => by
      haveI : FiniteDimensional 𝕜 (TangentSpace I x₀) := by
        unfold TangentSpace; infer_instance
      -- Pull back X to model space
      let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
      -- Pull back T to model space
      let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
        fun y => T.toFun ((extChartAt I x₀).symm y)
      -- Compute Lie derivative in model space
      exact lieDeriv_tensorRSWithin r s X' T'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀)
    contMDiff_toFun := by
      have hm_le_n : m ≤ n := le_of_add_le_left hmn
      haveI := tensorRSBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r s
      intro x₀'
      rw [contMDiffAt_section]
      -- Introduce sub-bundle instances needed for trivialization reasoning
      letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r
      letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) s
      letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) r
      letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := m) s
      -- For Hom bundles of trivial sub-bundles, the trivialization is the identity.
      have triv_id : ∀ (x : M) (f : TensorRSSpace r s I x),
          (trivializationAt (TensorRSModel r s 𝕜 E)
            (fun x => TensorRSSpace r s I x) x₀' ⟨x, f⟩).2 = f := by
        intro x f
        simp only [hom_trivializationAt_apply, inCoordinates]
        cases r <;> cases s <;>
          simp only [trivializationAt, FiberBundle.trivializationAt',
            tensor0SBundle_fiber, tensor0SBundleData, tensor0SBundleData_zero,
            tensor0S_fiberBundle_zero,
            Bundle.Trivial.symmL_trivialization,
            Bundle.Trivial.continuousLinearMapAt_trivialization,
            ContinuousLinearMap.comp_id] <;>
          exact ContinuousLinearMap.id_comp _
      simp_rw [triv_id]
      let F := TensorRSModel r s 𝕜 E
      let Tf : M → F := T.toFun
      let g₂ : M → E := fun x =>
        (trivializationAt E (TangentSpace I) x₀').continuousLinearMapAt 𝕜 x (X.toFun x)
      -- T.toFun is C^n as a map M → F (smooth section of trivial bundle)
      have hTf : ContMDiff I 𝓘(𝕜, F) n Tf := by
        intro x₀''
        haveI := tensorRSBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s
        letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
        letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
        letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r
        letI := tensor0SBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s
        have h := (contMDiffAt_section (s := T.toFun) x₀'').mp (T.contMDiff x₀'')
        have triv_gen : ∀ (z₀ : M) (x : M) (f : TensorRSSpace r s I x),
            (trivializationAt (TensorRSModel r s 𝕜 E)
              (fun x => TensorRSSpace r s I x) z₀ ⟨x, f⟩).2 = f := by
          intro z₀ x f
          simp only [hom_trivializationAt_apply, inCoordinates]
          cases r <;> cases s <;>
            simp only [trivializationAt, FiberBundle.trivializationAt',
              tensor0SBundle_fiber, tensor0SBundleData, tensor0SBundleData_zero,
              tensor0S_fiberBundle_zero,
              Bundle.Trivial.symmL_trivialization,
              Bundle.Trivial.continuousLinearMapAt_trivialization,
              ContinuousLinearMap.comp_id] <;>
            exact ContinuousLinearMap.id_comp _
        simp_rw [triv_gen] at h
        exact h
      -- mfderiv_const: the derivative of Tf as a CLM-valued function is C^m
      have hDeriv : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) m
          (inTangentCoordinates I 𝓘(𝕜, F) id Tf (mfderiv I 𝓘(𝕜, F) Tf) x₀') x₀' :=
        (hTf x₀').mfderiv_const hmn
      -- g₂ is C^m (trivialized smooth section of tangent bundle)
      have hg₂ : ContMDiffAt I 𝓘(𝕜, E) m g₂ x₀' := by
        have h := ((contMDiffAt_section (s := X.toFun) x₀').mp
          (X.contMDiff x₀')).of_le hm_le_n
        refine h.congr_of_eventuallyEq ?_
        have hbs := (trivializationAt E (TangentSpace I) x₀').open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I) x₀')
        filter_upwards [hbs] with x hx
        simp only [g₂, Trivialization.continuousLinearMapAt]
        erw [Pretrivialization.linearMapAt_apply, if_pos hx]; rfl
      -- Combine: (derivative applied to g₂) is C^m
      have hSmooth : ContMDiffAt I 𝓘(𝕜, F) m
          (fun x => inTangentCoordinates I 𝓘(𝕜, F) id Tf
            (mfderiv I 𝓘(𝕜, F) Tf) x₀' x (g₂ x)) x₀' :=
        hDeriv.clm_apply hg₂
      -- Show toFun =ᶠ[𝓝 x₀'] the inTangentCoordinates expression.
      -- Both sides equal mfderiv I 𝓘(𝕜,F) Tf x (X.toFun x) near x₀'.
      apply hSmooth.congr_of_eventuallyEq
      sorry }

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
