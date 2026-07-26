import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical curvature-tower bridge

This file identifies the static curvature-derivative tower used by the HCG
bounded-geometry API with the intrinsic solution tower used by the
Bernstein--Shi estimates.  The only representation difference is the
definitionally different slot count `k + 4` versus `4 + k`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- On a Ricci-flow solution, the HCG squared curvature-derivative norm is the
intrinsic squared norm controlled by the Bernstein--Shi tower. -/
theorem curvNormSq_eq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    curvDerivNormSq (I := I) (M := M) k (S.base.metric t) x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  sorry

end HCGCompactness
end DifferentialGeometry
