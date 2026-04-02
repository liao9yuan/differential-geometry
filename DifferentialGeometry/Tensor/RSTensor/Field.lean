/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
/-!
# Smooth Tensor Fields on Manifolds and Vector Spaces

This file defines smooth (r,s)-tensor fields in two settings:

1. On a smooth manifold `M`: smooth sections of the (r,s)-tensor bundle.
2. On a normed vector space `E` (flat setting): smooth functions into the model fiber.

## Main Definitions

* `TensorRSField r s` : smooth (r,s)-tensor fields on `M`, i.e. smooth sections of the
  (r,s)-tensor bundle `TensorRSSpace r s I`.
* `TensorRSVecField r s` : smooth (r,s)-tensor fields on `E`, i.e. smooth functions
  `E → TensorRSModel r s 𝕜 E`.
* `Tensor0SVecField s` : smooth (0,s)-tensor fields on `E`, i.e. smooth functions
  `E → Tensor0SModel s 𝕜 E`.

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

/-- A `C^n` (r,s)-tensor field on the normed vector space `E` over `𝕜`: a `C^n` function
`E → TensorRSModel r s 𝕜 E`. -/
structure TensorRSVecField (r s : ℕ) where
  /-- The underlying function -/
  toFun : E → TensorRSModel r s 𝕜 E
  /-- The underlying function is `C^n` -/
  smooth : ContDiff 𝕜 n toFun

/-- A `C^n` (0,s)-tensor field on the normed vector space `E` over `𝕜`: a `C^n` function
`E → Tensor0SModel s 𝕜 E`. -/
structure Tensor0SVecField (s : ℕ) where
  /-- The underlying function -/
  toFun : E → Tensor0SModel s 𝕜 E
  /-- The underlying function is `C^n` -/
  smooth : ContDiff 𝕜 n toFun

end
end Tensor0SBundle
