/-
Authors: Yuan Liao, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Bundle
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
/-!
# Smooth Tensor Fields on Manifolds

This file defines smooth (r,s)-tensor fields as smooth sections of the (r,s)-tensor bundle.

## Main Definitions

* `TensorRSField r s` : smooth (r,s)-tensor fields on `M`, i.e. smooth sections of the
  (r,s)-tensor bundle `TensorRSSpace r s I`.

## Tags

tensor field, smooth section, smooth manifold
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
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]

/-- A smooth (r,s)-tensor field on `M`: a smooth section of the (r,s)-tensor bundle. -/
def TensorRSField (r s : ℕ) :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

end
end Tensor0SBundle
