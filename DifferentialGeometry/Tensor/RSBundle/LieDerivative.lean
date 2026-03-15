/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/

-- TODO: Check this whole file for correctness of definitions)
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.VectorField
import DifferentialGeometry.Tensor.RSBundle.Basic

-- Import the tensor bundle definitions (adjust path as needed)
-- import TensorBundle

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

/-- The Lie derivative of a (0,s) tensor field on a manifold within a set.

Following the pattern of `mlieBracketWithin`, this is defined by:
1. Pulling back X and α to the model space via extChartAt
2. Computing the Lie derivative there
3. Pushing forward the result
-/
noncomputable def mlieDeriv_tensor0SWithin (s : ℕ)
    (X : (x : M) → TangentSpace I x)
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
    (X : (x : M) → TangentSpace I x)
    (α : (x : M) → Tensor0SSpace s I x)
    (x₀ : M) :
    Tensor0SSpace s I x₀ :=
  mlieDeriv_tensor0SWithin s X α univ x₀


/-!
### Basic properties of manifold Lie derivative
-/

variable {s : ℕ}
variable {X : (x : M) → TangentSpace I x}
variable {α β : (x : M) → Tensor0SSpace s I x}

@[simp] lemma mlieDeriv_tensor0SWithin_univ :
    mlieDeriv_tensor0SWithin (I := I) s X α univ = mlieDeriv_tensor0S s X α := rfl

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

/-- Lie derivative of an (r,s) tensor field within a set -/
noncomputable def mlieDeriv_tensorRSWithin (r s : ℕ)
    (X : (x : M) → TangentSpace I x)
    (T : (x : M) → Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)
    (u : Set M)
    (x₀ : M) :
    Tensor0SSpace r I x₀ →L[𝕜] Tensor0SSpace s I x₀ := by
  haveI : FiniteDimensional 𝕜 (TangentSpace I x₀) := by
    unfold TangentSpace
    infer_instance
  -- Pull back X to model space
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  -- Pull back T to model space
  let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => T ((extChartAt I x₀).symm y)
  -- Compute Lie derivative in model space
  exact lieDeriv_tensorRSWithin r s X' T'
    ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
    (extChartAt I x₀ x₀)

/-- Lie derivative of an (r,s) tensor field -/
noncomputable def mlieDeriv_tensorRS (r s : ℕ)
    (X : (x : M) → TangentSpace I x)
    (T : (x : M) → Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x)
    (x₀ : M) :
    Tensor0SSpace r I x₀ →L[𝕜] Tensor0SSpace s I x₀ :=
  mlieDeriv_tensorRSWithin r s X T univ x₀

/-!
### Cartan's magic formula for 1-forms

For a 1-form ω and vector field X, we have:
  L_X ω = i_X (dω) + d(i_X ω)

where i_X is interior product and d is exterior derivative.
-/

-- AI-generated code begins here! --

/-- Interior product of a vector field with a 1-form: i_X ω = ω(X) -/
noncomputable def interior_product_1form
    (X : (x : M) → TangentSpace I x)
    (u : (x : M) → Tensor0SSpace 1 I x)
    (x : M) : 𝕜 :=
  u x (fun _ => X x)

/-!
### Cartan's magic formula for k-forms

We package an abstract exterior derivative `d` on covariant tensor fields and use Cartan's
formula `L_X ω = ι_X (dω) + d (ι_X ω)` to define the Lie derivative of a k-form.
-/

/-- Abstract exterior derivative on covariant tensor fields. -/
structure ExteriorDerivative
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  d :
    ∀ k,
      ((x : M) → Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) k x) →
      (x : M) → Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (k + 1) x

variable (D : ExteriorDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))

/-- Interior product of a vector field with a (k+1)-form, pointwise. -/
noncomputable def interiorProductForm (k : ℕ)
    (X : (x : M) → TangentSpace I x)
    (omega : (x : M) → Tensor0SSpace (k + 1) I x) :
    (x : M) → Tensor0SSpace k I x :=
  fun x =>
    (Tensor0SBundle.interior_product (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) k x (X x))
      (omega x)

/-- Lie derivative of a k-form along a vector field via Cartan's magic formula:
`L_X ω = ι_X (dω) + d (ι_X ω)`.

For `k = 0`, the second term vanishes as the interior product lowers degree. -/
noncomputable def lieDeriv_form (k : ℕ)
    (X : (x : M) → TangentSpace I x)
    (omega : (x : M) → Tensor0SSpace k I x) :
    (x : M) → Tensor0SSpace k I x :=
  match k with
  | 0 =>
      interiorProductForm (k := 0) X (D.d 0 omega)
  | k + 1 =>
      fun x =>
        let term₁ :=
          interiorProductForm (k := k + 1) X (D.d (k + 1) omega) x
        let term₂ :=
          D.d k (interiorProductForm (k := k) X omega) x
        term₁ + term₂

end ManifoldLieDeriv

end

end TensorLieDeriv

open scoped Manifold

section VectorFieldDefinition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

/-- A (not necessarily smooth) vector field assigns to each point a tangent vector at that point. -/
abbrev vectorField : Type _ :=
  ∀ x : M, TangentSpace I x

/-!
Smooth vector fields are vector fields with a global `C^∞` proof.
We keep the underlying type `vectorField` for algebraic constructions and use
`IsSmoothVectorField` when smoothness is required.
-/

/-- Smoothness predicate for vector fields. -/
def IsSmoothVectorField
    (X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ContMDiff I I.tangent ⊤ (fun x => (X x : TangentBundle I M))

/-- Bundled smooth vector fields. -/
structure SmoothVectorField where
  toFun : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
  smooth_toFun : IsSmoothVectorField (I := I) (M := M) toFun

instance : CoeFun (SmoothVectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (fun _ => ∀ x : M, TangentSpace I x) :=
  ⟨SmoothVectorField.toFun⟩

lemma SmoothVectorField.isSmooth
    (X : SmoothVectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    IsSmoothVectorField (I := I) (M := M) (X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M)) :=
  X.smooth_toFun

lemma IsSmoothVectorField.contMDiff_minSmoothness
    {X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (hX : IsSmoothVectorField (I := I) (M := M) X) :
    ContMDiff I I.tangent (minSmoothness 𝕜 2)
      (fun x => (X x : TangentBundle I M)) := by
  exact hX.of_le le_top

lemma IsSmoothVectorField.mdifferentiableAt
    {X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (hX : IsSmoothVectorField (I := I) (M := M) X) (x : M) :
    MDifferentiableAt I I.tangent (fun x => (X x : TangentBundle I M)) x := by
  have hX_at :
      ContMDiffAt I I.tangent ⊤ (fun x => (X x : TangentBundle I M)) x :=
    hX x
  exact hX_at.mdifferentiableAt (by simp)

lemma IsSmoothVectorField.mlieBracket_mdifferentiableAt
    [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E]
    {X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (hX : IsSmoothVectorField (I := I) (M := M) X)
    (hY : IsSmoothVectorField (I := I) (M := M) Y) (x : M) :
    MDifferentiableAt I I.tangent
      (fun x => (VectorField.mlieBracket I X Y x : TangentBundle I M)) x := by
  let n : ℕ∞ := 1 + 1
  have hX_at :
      ContMDiffAt I I.tangent ⊤ (fun x => (X x : TangentBundle I M)) x := hX x
  have hY_at :
      ContMDiffAt I I.tangent ⊤ (fun x => (Y x : TangentBundle I M)) x := hY x
  have hX' :
      ContMDiffAt I I.tangent (n : WithTop ℕ∞)
        (fun x => (X x : TangentBundle I M)) x :=
    hX_at.of_le le_top
  have hY' :
      ContMDiffAt I I.tangent (n : WithTop ℕ∞)
        (fun x => (Y x : TangentBundle I M)) x :=
    hY_at.of_le le_top
  have hbr :
      ContMDiffAt I I.tangent 1
        (fun x => (VectorField.mlieBracket I X Y x : TangentBundle I M)) x := by
    have hmn :
        minSmoothness 𝕜 (1 + 1) ≤ (n : WithTop ℕ∞) := by
      simp [n, minSmoothness_of_isRCLikeNormedField]
    exact (ContMDiffAt.mlieBracket_vectorField (I := I) (U := X) (V := Y)
      (x := x) (m := 1) (n := n) hX' hY' hmn)
  exact hbr.mdifferentiableAt (x := x) (by simp)

lemma mlieBracket_jacobi
    [CompleteSpace 𝕜] [CompleteSpace E]
    {X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (hX : IsSmoothVectorField (I := I) (M := M) X)
    (hY : IsSmoothVectorField (I := I) (M := M) Y)
    (hZ : IsSmoothVectorField (I := I) (M := M) Z) :
    VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) =
      VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) := by
  exact VectorField.leibniz_identity_mlieBracket
    (IsSmoothVectorField.contMDiff_minSmoothness (I := I) (M := M) hX)
    (IsSmoothVectorField.contMDiff_minSmoothness (I := I) (M := M) hY)
    (IsSmoothVectorField.contMDiff_minSmoothness (I := I) (M := M) hZ)

lemma mlieBracket_neg_right_apply
    [CompleteSpace E]
    {V W : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)} {x : M}
    (hW : MDifferentiableAt I I.tangent (fun x => (W x : TangentBundle I M)) x) :
    VectorField.mlieBracket I V (-W) x = - VectorField.mlieBracket I V W x := by
  simpa [neg_one_smul] using
    (VectorField.mlieBracket_const_smul_right (I := I) (V := V) (W := W) (c := (-1 : 𝕜)) hW)

lemma mlieBracket_jacobi_cyclic
    [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E]
    {X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (hX : IsSmoothVectorField (I := I) (M := M) X)
    (hY : IsSmoothVectorField (I := I) (M := M) Y)
    (hZ : IsSmoothVectorField (I := I) (M := M) Z) :
    VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) = 0 := by
  ext x
  have hJacobi := mlieBracket_jacobi (I := I) (M := M) hX hY hZ
  have hJacobi_x :
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x =
        VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x +
          VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x := by
    simpa using congrArg (fun f => f x) hJacobi
  have hZX :
      VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x =
        - VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x := by
    simpa using
      (VectorField.mlieBracket_swap_apply (I := I) (V := Z)
        (W := VectorField.mlieBracket I X Y) (x := x))
  have hXZ :
      MDifferentiableAt I I.tangent
        (fun x => (VectorField.mlieBracket I X Z x : TangentBundle I M)) x :=
    IsSmoothVectorField.mlieBracket_mdifferentiableAt (I := I) (M := M) hX hZ x
  have hYX :
      VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x := by
    have h := mlieBracket_neg_right_apply (I := I) (V := Y)
      (W := VectorField.mlieBracket I X Z) hXZ
    calc
      VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x =
          VectorField.mlieBracket I Y (- VectorField.mlieBracket I X Z) x := by
            rw [VectorField.mlieBracket_swap (I := I) (V := Z) (W := X)]
      _ = - VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x := h
  -- Substitute the Jacobi identity and cancel with antisymmetry.
  simp [Pi.add_apply, hJacobi_x, hYX, hZX]

/-- A smooth scalar field. -/
abbrev smoothScalarField : Type _ :=
  M → 𝕜

/-- Smoothness predicate for scalar fields. -/
def IsSmoothScalarField (f : smoothScalarField (𝕜 := 𝕜) (M := M)) : Prop :=
  ContMDiff I 𝓘(𝕜) ⊤ f

/-- Pointwise scalar multiplication of a vector field by a scalar field. -/
def scalarSmul
    (f : smoothScalarField (𝕜 := 𝕜) (M := M))
    (X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  fun x => f x • X x

end VectorFieldDefinition

/-!
## Riemannian geometry
-/

section RiemannianGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

section
variable [FiniteDimensional 𝕜 E] [Module.Finite 𝕜 E]

instance tangentSpace_moduleFinite (x : M) : Module.Finite 𝕜 (TangentSpace I x) := by
  simpa [TangentSpace] using (inferInstance : Module.Finite 𝕜 E)

end

/-- Directional derivative of a scalar function along a vector field. -/
noncomputable def directionalDerivScalar (f : M → 𝕜)
    (X : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    M → 𝕜 :=
  fun x => (mfderiv I 𝓘(𝕜) f x) (X x)

/-- A Riemannian metric given by a field of bilinear forms on tangent spaces. -/
structure SmoothRiemannianMetric where
  g : ∀ x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜
  symmetric : ∀ x v w, g x v w = g x w v
  nondegenerate : ∀ x v, (∀ w, g x v w = 0) → v = 0
  smooth :
    ∀ X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M),
      ContMDiff I 𝓘(𝕜) ⊤ (fun x => g x (X x) (Y x))

/-- Levi-Civita connection data: covariant derivative compatible with a metric and torsion-free. -/
structure LeviCivitaConnection where
  metric : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
  covDeriv :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
  covDeriv_add_left :
    ∀ X X' Y x,
      covDeriv (X + X') Y x = covDeriv X Y x + covDeriv X' Y x
  covDeriv_smul_left :
    ∀ (c : 𝕜) X Y x,
      covDeriv (c • X) Y x = c • covDeriv X Y x
  covDeriv_add_right :
    ∀ X Y Y' x,
      covDeriv X (Y + Y') x = covDeriv X Y x + covDeriv X Y' x
  covDeriv_smul_right :
    ∀ (c : 𝕜) X Y x,
      covDeriv X (c • Y) x = c • covDeriv X Y x
  covDeriv_smul_left_smooth :
    ∀ (f : smoothScalarField (𝕜 := 𝕜) (M := M)) (_hf : IsSmoothScalarField (I := I) (M := M) f)
      X Y x,
      covDeriv (scalarSmul f X) Y x = f x • covDeriv X Y x
  covDeriv_smul_right_smooth :
    ∀ (f : smoothScalarField (𝕜 := 𝕜) (M := M)) (_hf : IsSmoothScalarField (I := I) (M := M) f)
      X Y x,
      covDeriv X (scalarSmul f Y) x =
        directionalDerivScalar (fun y => f y) X x • Y x + f x • covDeriv X Y x
  torsionFree :
    ∀ X Y x,
      covDeriv X Y x - covDeriv Y X x =
        VectorField.mlieBracket I X Y x
  metricCompatible :
    ∀ X Y Z x,
      directionalDerivScalar
        (fun y => metric.g y (Y y) (Z y)) X x =
        metric.g x (covDeriv X Y x) (Z x) +
          metric.g x (Y x) (covDeriv X Z x)
-- Put in a theorem that the set of LeviCivitaConnections contains a unique element.
-- Somehow use Yuan's Koszul formula definition to prove existence and uniqueness
-- Reference 2DRicciFlow, subsection 9.3 to 9.6 for the mathematics of the LC connection

/-- Scalar product of vector fields using a Riemannian metric. -/
noncomputable def metricProduct
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    M → 𝕜 :=
  fun x => g.g x (X x) (Y x)

notation "⟪" X ", " Y "⟫[" g "]" => metricProduct g X Y

omit [IsManifold I ⊤ M] in
@[simp] lemma metricProduct_apply
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    (⟪X, Y⟫[g]) x = g.g x (X x) (Y x) :=
  rfl

omit [IsManifold I ⊤ M] in
lemma SmoothRiemannianMetric.metricProduct_smooth
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) ⊤ (⟪X, Y⟫[g]) := by
  exact g.smooth X Y

omit [IsManifold I ⊤ M] in
lemma metricProduct_swap
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ⟪X, Y⟫[g] = ⟪Y, X⟫[g] := by
  funext x
  simpa [metricProduct] using g.symmetric x (X x) (Y x)

omit [IsManifold I ⊤ M] in
lemma metricProduct_add_left
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X X' Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ⟪X + X', Y⟫[g] = ⟪X, Y⟫[g] + ⟪X', Y⟫[g] := by
  funext x
  simp [metricProduct, ContinuousLinearMap.add_apply]

omit [IsManifold I ⊤ M] in
lemma metricProduct_add_right
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Y' : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ⟪X, Y + Y'⟫[g] = ⟪X, Y⟫[g] + ⟪X, Y'⟫[g] := by
  funext x
  simp [metricProduct]

omit [IsManifold I ⊤ M] in
lemma metricProduct_zero_left
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ⟪0, Y⟫[g] = 0 := by
  funext x
  simp [metricProduct]

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.covDeriv_neg_left
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    nabla.covDeriv (-X) Y x = - nabla.covDeriv X Y x := by
  simpa [neg_one_smul] using nabla.covDeriv_smul_left (-1) X Y x

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.covDeriv_neg_right
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    nabla.covDeriv X (-Y) x = - nabla.covDeriv X Y x := by
  simpa [neg_one_smul] using nabla.covDeriv_smul_right (-1) X Y x

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.covDeriv_sub_left
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X X' Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    nabla.covDeriv (X - X') Y x = nabla.covDeriv X Y x - nabla.covDeriv X' Y x := by
  simp [sub_eq_add_neg, nabla.covDeriv_add_left, nabla.covDeriv_neg_left]

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.covDeriv_sub_right
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Y' : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    nabla.covDeriv X (Y - Y') x = nabla.covDeriv X Y x - nabla.covDeriv X Y' x := by
  simp [sub_eq_add_neg, nabla.covDeriv_add_right, nabla.covDeriv_neg_right]

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.mlieBracket_eq_covDeriv_sub
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    VectorField.mlieBracket I X Y =
      nabla.covDeriv X Y - nabla.covDeriv Y X := by
  funext x
  symm
  simpa using nabla.torsionFree X Y x

/-- Compatibility condition between a covariant derivative and its metric, matching the
`product` identity from the reference code. -/
def LeviCivitaConnection.IsCompatible
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ X Y Z x,
    directionalDerivScalar
      (fun y => nabla.metric.g y (Y y) (Z y)) X x =
      nabla.metric.g x (nabla.covDeriv X Y x) (Z x) +
        nabla.metric.g x (Y x) (nabla.covDeriv X Z x)

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.isCompatible
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    nabla.IsCompatible :=
  nabla.metricCompatible

/-- Bundled predicate expressing that a connection is Levi-Civita, mirroring the reference
`IsLeviCivitaConnection` definition. -/
def LeviCivitaConnection.IsLeviCivita
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  nabla.IsCompatible ∧
    (∀ X Y x,
      nabla.covDeriv X Y x - nabla.covDeriv Y X x =
        VectorField.mlieBracket I X Y x)

omit [IsManifold I ⊤ M] in
lemma LeviCivitaConnection.isLeviCivita
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    nabla.IsLeviCivita :=
  ⟨nabla.metricCompatible, nabla.torsionFree⟩

/-- A covariant derivative, given by a bilinear operation on vector fields. -/
structure CovariantDerivative where
  cov :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)

namespace CovariantDerivative

/-- Metric compatibility for a covariant derivative, modeled on the reference code. -/
def IsCompatible
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ X Y Z x,
    directionalDerivScalar (fun y => g.g y (Y y) (Z y)) X x =
      g.g x (cov.cov X Y x) (Z x) +
        g.g x (Y x) (cov.cov X Z x)

/-- Torsion-free condition for a covariant derivative. -/
def IsTorsionFree
    (cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ X Y x, cov.cov X Y x - cov.cov Y X x = VectorField.mlieBracket I X Y x

/-- Levi-Civita condition for a covariant derivative: compatible and torsion-free. -/
def IsLeviCivitaConnection
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  IsCompatible (I := I) g cov ∧ IsTorsionFree (I := I) cov

/-- Auxiliary expression mirroring the reference `rhs_aux`, using our directional derivative. -/
noncomputable def rhsAux
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (_cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  fun x =>
    directionalDerivScalar (fun y => g.g y (Y y) (Z y)) X x

/-- Symmetric combination that features in uniqueness formulas for the Levi-Civita connection. -/
noncomputable def leviCivitaRhs'
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  rhsAux (g := g) cov X Y Z
    + rhsAux (g := g) cov Y Z X
    - rhsAux (g := g) cov Z X Y
    - ⟪Y, VectorField.mlieBracket I X Z⟫[g]
    - ⟪Z, VectorField.mlieBracket I X Y⟫[g]
    + ⟪X, VectorField.mlieBracket I Z Y⟫[g]

/-- Averaged version of the `leviCivitaRhs'` expression. -/
noncomputable def leviCivitaRhs
    (g : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (cov : CovariantDerivative (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  (2 : 𝕜)⁻¹ • leviCivitaRhs' (g := g) (cov := cov) X Y Z

end CovariantDerivative

section FiniteDimensionalCoordinates
variable [FiniteDimensional 𝕜 E] [Module.Finite 𝕜 E]

/-- A choice of local coordinates together with the coordinate frame they induce. -/
structure LocalCoordinates where
  chart : M → PartialEquiv M E := fun x => extChartAt I x
  coordBasis :
    ∀ x : M,
      Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 (TangentSpace I x)
  coordBasis_is_differential :
    ∀ x, coordBasis x = Module.finBasis 𝕜 (TangentSpace I x)

/-- The coordinate vector field `∂_i` associated to the `i`-th coordinate. -/
noncomputable def LocalCoordinates.coordVectorField
    (coords : LocalCoordinates (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (i : Fin (Module.finrank 𝕜 E)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  fun x => coords.coordBasis x i

/-- Christoffel symbols associated to a connection, given as coefficients of the covariant
derivative in a coordinate basis. -/
structure ChristoffelSymbols
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  coords : LocalCoordinates (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
  Γ :
    M →
      Fin (Module.finrank 𝕜 E) →
      Fin (Module.finrank 𝕜 E) →
      Fin (Module.finrank 𝕜 E) → 𝕜
  coord_connection :
    ∀ x i j,
      nabla.covDeriv (coords.coordVectorField i) (coords.coordVectorField j) x =
        ∑ k, Γ x i j k • coords.coordVectorField k x

end FiniteDimensionalCoordinates

/-- Riemann curvature tensor: R(X,Y)Z. -/
structure RiemannCurvatureTensor where
  R :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)

/-- Curvature built from a Levi-Civita connection via the usual formula. -/
noncomputable def curvatureTensor
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    RiemannCurvatureTensor (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  { R := fun X Y Z =>
      fun x =>
        nabla.covDeriv X (nabla.covDeriv Y Z) x
          - nabla.covDeriv Y (nabla.covDeriv X Z) x
          - nabla.covDeriv (VectorField.mlieBracket I X Y) Z x }

/-- The (0,4) curvature tensor `R(X,Y,Z,W) = g(R(X,Y)Z, W)`. -/
noncomputable def curvatureTensor4
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) → M → 𝕜 :=
  fun X Y Z W => ⟪(curvatureTensor nabla).R X Y Z, W⟫[nabla.metric]

/-- Torsion tensor `T(X,Y)`. -/
noncomputable def torsionTensor
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  fun X Y =>
    fun x =>
      nabla.covDeriv X Y x - nabla.covDeriv Y X x -
        VectorField.mlieBracket I X Y x

/-- Covariant derivative of curvature: `(∇_X R)(Y,Z)W`. -/
noncomputable def covDerivCurvature
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  fun X Y Z W =>
    fun x =>
      nabla.covDeriv X ((curvatureTensor nabla).R Y Z W) x
        - (curvatureTensor nabla).R (nabla.covDeriv X Y) Z W x
        - (curvatureTensor nabla).R Y (nabla.covDeriv X Z) W x
        - (curvatureTensor nabla).R Y Z (nabla.covDeriv X W) x

/-- Covariant derivative of the (0,4) curvature tensor. -/
noncomputable def covDerivCurvature4
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) →
    vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) → M → 𝕜 :=
  fun X Y Z W V => ⟪covDerivCurvature nabla X Y Z W, V⟫[nabla.metric]

/-
Swapping the first two inputs of curvature flips the sign. This is the standard identity
R(X,Y) = -R(Y,X) (see any Riemannian geometry text, e.g. Lee), proved by expanding the
definition and using antisymmetry of the Lie bracket and linearity in the first slot of ∇.
-/
omit [IsManifold I ⊤ M] in
lemma curvatureTensor_swap
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (curvatureTensor nabla).R X Y Z = - (curvatureTensor nabla).R Y X Z := by
  ext x
  have hcov_neg :
      ∀ X Y x, nabla.covDeriv (-X) Y x = - nabla.covDeriv X Y x := by
    intro X Y x
    simpa [neg_one_smul] using (nabla.covDeriv_smul_left (-1) X Y x)
  have hbr :
      VectorField.mlieBracket I Y X = - VectorField.mlieBracket I X Y :=
    VectorField.mlieBracket_swap (I := I) (V := Y) (W := X)
  simp [curvatureTensor, hcov_neg, hbr, sub_eq_add_neg]
  abel

omit [IsManifold I ⊤ M] in
lemma curvatureTensor_cyclic_eq_mlieBracket
    [CompleteSpace 𝕜] [CompleteSpace E]
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (curvatureTensor nabla).R X Y Z +
        (curvatureTensor nabla).R Y Z X +
        (curvatureTensor nabla).R Z X Y =
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) := by
  ext x
  simp [curvatureTensor, nabla.mlieBracket_eq_covDeriv_sub,
    nabla.covDeriv_sub_left, nabla.covDeriv_sub_right]
  simp [sub_eq_add_neg]
  abel

--Prove general symmetries
    -- a Anti-symmetric in first two components
    -- b Define the Riemann curvature 4 tensor
    -- c Anti-symmetric in the last two components
    -- d Symmetric in the switch of first two and last two components
/-! ### Bianchi identities (as properties) -/

/-- First (algebraic) Bianchi identity as a property of a connection. -/
def firstBianchiIdentity
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ (X Y Z : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)),
    IsSmoothVectorField (I := I) (M := M) X →
    IsSmoothVectorField (I := I) (M := M) Y →
    IsSmoothVectorField (I := I) (M := M) Z →
      (curvatureTensor nabla).R X Y Z +
        (curvatureTensor nabla).R Y Z X +
        (curvatureTensor nabla).R Z X Y = 0

/-- Second (differential) Bianchi identity as a property of a connection. -/
def secondBianchiIdentity
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ (X Y Z W : vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)),
    IsSmoothVectorField (I := I) (M := M) X →
    IsSmoothVectorField (I := I) (M := M) Y →
    IsSmoothVectorField (I := I) (M := M) Z →
    IsSmoothVectorField (I := I) (M := M) W →
      covDerivCurvature nabla X Y Z W +
        covDerivCurvature nabla Y Z X W +
        covDerivCurvature nabla Z X Y W = 0
  -- Requires definition of covariant differentiation of tensors
-- Note: Use Lee's Riemannian Geometry, Petersen and Chow-Chow (2024) as references.

lemma firstBianchiIdentity_of_torsionFree
    [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] [CompleteSpace E]
    (nabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    firstBianchiIdentity (I := I) (M := M) nabla := by
  intro X Y Z hX hY hZ
  have hJacobi := mlieBracket_jacobi_cyclic (I := I) (M := M) hX hY hZ
  calc
    (curvatureTensor nabla).R X Y Z +
        (curvatureTensor nabla).R Y Z X +
        (curvatureTensor nabla).R Z X Y =
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) := by
          simpa using curvatureTensor_cyclic_eq_mlieBracket (nabla := nabla) X Y Z
    _ = 0 := hJacobi

section FiniteDimensionalCoordinates
variable [FiniteDimensional 𝕜 E] [Module.Finite 𝕜 E]

/-- Coordinate expression `R^l_{kij}` in terms of Christoffel symbols, relating directional
derivatives of Γ with quadratic terms in Γ. -/
def curvatureComponentsFormula
    {g : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)}
    (Γ : ChristoffelSymbols g) : Prop :=
  ∀ (x : M) (i j k : Fin (Module.finrank 𝕜 E)),
    (curvatureTensor g).R
        (Γ.coords.coordVectorField i)
        (Γ.coords.coordVectorField j)
        (Γ.coords.coordVectorField k) x =
      ∑ l : Fin (Module.finrank 𝕜 E),
        (directionalDerivScalar
            (fun y => Γ.Γ y j k l)
            (Γ.coords.coordVectorField i) x -
          directionalDerivScalar
            (fun y => Γ.Γ y i k l)
            (Γ.coords.coordVectorField j) x +
          ∑ m : Fin (Module.finrank 𝕜 E),
            (Γ.Γ x j k m * Γ.Γ x i m l -
              Γ.Γ x i k m * Γ.Γ x j m l)) •
          Γ.coords.coordVectorField l x

end FiniteDimensionalCoordinates

end RiemannianGeometry

--Use e.g. ChatGPT 5.2 Pro extended thinking to compare the Massot--Rothgang
--LC connection code with ours. Tell the chatbot our minimalist philosophy, yet at the same time,
--we need our code to be foundational for differential geometry. With these values,
--how best can we improve our code to be correct and complete?
