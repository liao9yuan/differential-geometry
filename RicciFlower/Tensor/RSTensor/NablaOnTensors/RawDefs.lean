import RicciFlower.Tensor.RSTensor.NablaOnTensors.FixedChart
import RicciFlower.Tensor.Multilinear.BundleSmoothEval

/-!
# Raw tensor covariant derivative APIs

This module contains the public pointwise APIs `nabla0SFun` / `nablaRSFun`, bundled wrappers, and
their explicit regularity predicates.  Proofs of those regularity predicates live in
`NablaOnTensors.Regularity`.
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This is the covariant-tensor analogue of `mcovariantDeriv_tensorRSWithin`. It uses the
model formula `D_X alpha - correction_Gamma alpha` and then transports the result back
to the tensor fiber at `x0`. -/
noncomputable def mcovariantDeriv_tensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s x₀ (fun x => α x)
  exact
    (trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).symm
        x₀
      (covariantDeriv_tensor0SModelWithin s X' ΓX α'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

theorem mcovariantDeriv_tensor0SWithin_one_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 1)
    (u : Set M) (x₀ : M) (j : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 1 X ΓX α u x₀))
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 1 x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun _ : Fin 1 => basis j) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              1 x₀ x₀ (α x₀)) (fun _ : Fin 1 => basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_one_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

theorem mcovariantDeriv_tensor0SWithin_two_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 2)
    (u : Set M) (x₀ : M) (j l : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 2 X ΓX A u x₀))
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 2 x₀ (fun x => A x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) l k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_two_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Arbitrary-valence coordinate-basis formula for the chart-level covariant
derivative of a covariant tensor.

This is the transported version of
`covariantDeriv_tensor0SModelAt_apply_basis_slots`; the one- and two-slot
component lemmas are special cases of this statement. -/
theorem mcovariantDeriv_tensor0SWithin_apply_basis_slots
    {Idx : Type*} [Fintype Idx] {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) (slots a) k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              s x₀ x₀ (α x₀))
              (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_basis_slots (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Arbitrary-slot formula for the chart-level covariant derivative of a
covariant tensor. -/
theorem mcovariantDeriv_tensor0SWithin_apply_slots {s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → E) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        slots =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          slots -
        ∑ a : Fin s,
          (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x₀ (α x₀))
            (Function.update slots a (ΓX (extChartAt I x₀ x₀) (slots a))) := by
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X ΓX α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This mirrors `mlieDeriv_tensorRSWithin`, but the model formula uses a supplied
`ΓX : E → E →L[𝕜] E` instead of `fderivWithin X'`. For a genuine connection,
`ΓX y` should be the chart representative of `v ↦ ∇_X(constant v)` at the
model point `y`. The wrappers below use `connectionEndomorphismInChart` to extract
this endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => tensorRSSpace_continuousLinearEquiv (I := I) r s
      ((extChartAt I x₀).symm y) (T.toFun ((extChartAt I x₀).symm y))
  exact (tensorRSSpace_continuousLinearEquiv (I := I) r s x₀).symm
    (covariantDeriv_tensorRSModelWithin r s X' ΓX T'
      ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
      (extChartAt I x₀ x₀))

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X ΓX T univ x₀

section ExtractedConnection

variable [IsManifold I 2 M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SWithinFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) α u x₀

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithinFromConnection (n := n) s cov X α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithinFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) T u x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithinFromConnection (n := n) r s cov X T univ x₀

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Canonical raw pointwise covariant derivative of a covariant tensor field
along a smooth vector field, using a realized connection.

Use this in downstream geometry.  It is implemented by trivializing to the
model-space tensor formula and extracting the local connection endomorphism from
mathlib's `CovariantDerivative`.  The bundled section version is `nabla0S`. -/
noncomputable def nabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x : M) : Tensor0SSpace s I x :=
  TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) s cov X α x

/-- Canonical raw pointwise covariant derivative of a mixed tensor field along a
smooth vector field, using a realized connection.

Use this in downstream geometry.  The lower-level model and chart declarations
above are implementation bridges.  The bundled section version is `nablaRS`. -/
noncomputable def nablaRSFun (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (x : M) : TensorRSSpace r s I x :=
  TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) r s cov X T x

set_option linter.unusedSectionVars false in
@[simp] theorem nabla0SFun_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x =
      TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (⊤ : WithTop ℕ∞)) s cov X α x := rfl

/-- Self-chart arbitrary-slot evaluation formula for `nabla0SFun`.

This is the direct formula supplied by the raw definition when the output point
`x` is also the center of the tensor and tangent trivializations. The remaining
fixed-chart regularity bridge is exactly the step that replaces these self-chart
constant slots by slots constant in a different chart centered at `x₀`. -/
theorem nabla0SFun_apply_selfChart_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slots a) x) =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (⊤ : WithTop ℕ∞)) s cov X α x
        (extChartAt I x x) slots := by
  unfold tangentConstInChart
  rw [← tensor0SModelAt_apply (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) s x x
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x) slots]
  unfold nabla0SFun TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection
  rw [TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots]
  rw [fixedChartNabla0SModel_apply_slots]
  simp only [Set.preimage_univ, Set.univ_inter, tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

set_option linter.unusedSectionVars false in
@[simp] theorem nablaRSFun_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x =
      TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (⊤ : WithTop ℕ∞)) r s cov X T x := rfl

/-- Regularity predicate for the raw covariant derivative of a covariant tensor field.

This is kept explicit so `nabla0S` never hides the analytic smoothness proof. -/
abbrev Nabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x⟩ :
        TotalSpace (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)))

/-- Regularity predicate for the raw covariant derivative of a mixed tensor field.

This is kept explicit so `nablaRS` never hides the analytic smoothness proof. -/
abbrev NablaRSRegular (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s) : Prop :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiff I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x⟩ :
        TotalSpace (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)))

/-- Bundled covariant derivative of a covariant tensor field. The smoothness proof is an
explicit argument; use `nabla0S_reg` once the analytic regularity bridge is available. -/
noncomputable def nabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := 
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α, hreg⟩

/-- Bundled covariant derivative of a mixed tensor field. The smoothness proof is an
explicit argument; use `nablaRS_reg` once the analytic regularity bridge is available. -/
noncomputable def nablaRS (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T, hreg⟩

set_option linter.unusedSectionVars false in
@[simp] theorem nabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α)
    (x : M) :
    nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α hreg x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem nablaRS_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T)
    (x : M) :
    nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T hreg x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x := rfl

end

noncomputable section RealDerivationSmoothness

open Bundle
open scoped Manifold Topology Bundle ContDiff BigOperators

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace Real E₀]
variable [Module.Finite Real E₀] [FiniteDimensional Real E₀]
variable {H₀ : Type*} [TopologicalSpace H₀]
variable {I₀ : ModelWithCorners Real E₀ H₀}
variable {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable [IsManifold I₀ ∞ M₀]

/-- Smoothness of one correction term in the tensor derivation formula.

If `α` is a smooth `(0,s)` tensor field, `X` and all `Yᵢ` are smooth vector
fields, and `cov` is a smooth tangent-bundle connection, then the scalar
function

`p ↦ α_p(Y₁(p), ..., (∇_X Y_a)(p), ..., Y_s(p))`

is smooth.  This is the direct `(0,s)` analogue of the vector-field smoothness
lemma `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply`; it
uses that tensor evaluation on smooth vector fields is smooth. -/
theorem tensor0S_eval_covariantDerivative_slot_contMDiff {s : ℕ}
    (cov : CovariantDerivative I₀ E₀ (TangentSpace I₀ : M₀ → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E₀) (H := H₀) (I := I₀) (M := M₀)
      (n := ∞) s)
    (Y : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (a : Fin s) :
    ContMDiff I₀ 𝓘(Real, Real) ∞
      (fun p : M₀ =>
        α p
          (Function.update (fun b : Fin s => Y b p) a
            ((cov (fun q : M₀ => Y a q) p) (X p)))) := by
  let W : (p : M₀) → TangentSpace I₀ p :=
    fun p => (cov (fun q : M₀ => Y a q) p) (X p)
  have hW :
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, W p⟩ : TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    simpa [W] using
      (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
        (𝕜 := Real) (I := I₀) (M := M₀) cov hcov X (Y a))
  let V : Fin s → (p : M₀) → TangentSpace I₀ p :=
    Function.update (fun b : Fin s => fun p : M₀ => Y b p) a W
  have hV : ∀ i : Fin s,
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, V i p⟩ : TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa [V] using hW
    · simpa [V, Function.update, hi] using (Y i).contMDiff
  let Vsec : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _) :=
    fun i => ⟨V i, hV i⟩
  have hev' := TensorMultilinear.contMDiff_tensor0SField_apply
    (E := E₀) (H := H₀) (I := I₀) (M := M₀) (n := s) α Vsec
  refine hev'.congr ?_
  intro p
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi
    simp [Vsec, V, W]
  · simp [Vsec, V, Function.update, hi]

end RealDerivationSmoothness

end Tensor0SBundle
