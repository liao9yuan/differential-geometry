/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Multilinear.Basis

/-!
# Smooth Tensor Fields on Manifolds

This file defines smooth tensor fields on a smooth manifold `M`.

## Main Definitions

* `TensorRSField r s` : `C^n` (r,s)-tensor fields on `M`, i.e. `C^n` sections of the
  (r,s)-tensor bundle `TensorRSSpace r s I`.
* `Tensor0SField s` : `C^n` (0,s)-tensor fields on `M`, i.e. `C^n` sections of the
  (0,s)-tensor bundle `Tensor0SSpace s I`.

## Tags

tensor field, smooth section, smooth manifold, vector space
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
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-!
## Manifold tensor fields (sections of the bundle)
-/

/-- A `C^n` (r,s)-tensor field on `M`: a `C^n` section of the (r,s)-tensor bundle. -/
abbrev TensorRSField (r s : ℕ) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

/-- A `C^n` (0,s)-tensor field on `M`: a `C^n` section of the (0,s)-tensor bundle. -/
abbrev Tensor0SField (s : ℕ) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiffSection I
    (Tensor0SModel s 𝕜 E)
    n
    (fun x : M => Tensor0SSpace s I x)

/-!
## Manifold tensor fields: addition and smooth-function scalar multiplication

Addition and constant-scalar smul are inherited directly from `ContMDiffSection` (which is an
`AddCommGroup` and a `𝕜`-module).  We additionally provide pointwise smul by a smooth function
`φ : M → 𝕜`.
-/

variable {r s : ℕ} [CompleteSpace 𝕜]

/-- Pointwise scalar multiplication of a `C^n` (r,s)-tensor field by a `C^n` scalar function
`φ : M → 𝕜` is again a `C^n` (r,s)-tensor field.

This extends the constant-scalar `Module 𝕜` action on `ContMDiffSection` to the case of a
non-constant smooth multiplier. The smoothness of `φ x • α x` follows from
`ContMDiff.smul_section`. -/
def tensorRSField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

@[simp]
theorem tensorRSField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensorRSField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

/-- Pointwise scalar multiplication of a `C^n` (0,s)-tensor field by a `C^n` scalar function
`φ : M → 𝕜` is again a `C^n` (0,s)-tensor field. -/
def tensor0SField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

@[simp]
theorem tensor0SField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensor0SField_smulByFun n φ hφ α x = φ x • α x :=
  rfl

end
end Tensor0SBundle

/-!
## Tensor product of (0,s)-tensor fields
-/

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
variable {s q : ℕ}

variable (n : WithTop ℕ∞)

/-- The tensor product of a `C^n` (0,s)-tensor field `α` and a `C^n` (0,q)-tensor field `β`
is a `C^n` (0,s+q)-tensor field, defined pointwise by `tensor0S_product_fun`.

Smoothness is proved by reducing to basis coordinates via
`contMDiff_multilinearSection_iff_coord`: the trivialized coordinate of `α ⊗ β` at
`σ : Fin (s+q) → Fin d` equals the product of the coordinate of `α` at `σ ∘ Fin.castAdd q`
and the coordinate of `β` at `σ ∘ Fin.natAdd s`, both of which are smooth. -/
noncomputable def tensor0SField_product
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (β : Tensor0SField n q (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n (s + q) (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + q)
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) q
  ⟨fun x => tensor0S_product_fun s q x (α x) (β x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    rw [contMDiff_multilinearSection_iff_coord (TangentSpace I) n b]
    intro σ x₀
    -- Extract coordinate smoothness of α and β
    have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (α x : Tensor0SSpace s I x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
      (fun x => (β x : Tensor0SSpace q I x))).mp β.contMDiff)
    -- Rewrite the coordinate of the product as a product of coordinates
    simp_rw [triv_coord_tensor0S_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

end
end Tensor0SBundle
