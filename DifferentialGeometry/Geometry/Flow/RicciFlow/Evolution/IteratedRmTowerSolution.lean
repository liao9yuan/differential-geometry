import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The arbitrary-dimensional curvature-derivative tower of a Ricci-flow solution

This file is the solution-facing owner of the variable-rank
`IteratedRmTowerOn` route.  The tower uses the intrinsic squared norms
`|nabla^k Rm|^2` and their intrinsic scalar Laplacians.  Its component fields
are indexed by `Fin (Module.finrank Real E)`, so the generic tower consumer has
coefficient `2 * (Module.finrank Real E : Real) ^ (6 + k)` in every finite
dimension.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- A Ricci-flow solution supplies the variable-rank component tower whose
scalar fields are the intrinsic norms `|nabla^k Rm|^2` and their intrinsic
Laplacians. -/
theorem exists_rmTowerSol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∃
      (level : (k : Nat) → Real → M →
        (Fin (4 + k) → Fin (Module.finrank Real E)) → Real)
      (star : (k : Nat) → Real → M → Nat →
        (Fin (4 + k) → Fin (Module.finrank Real E)) → Real),
      IteratedRmTowerOn (D := D) level star
        (nablaKRm04NormSqIntrinsic (I := I) S)
        (nablaKNormLap (I := I) S) := by
  sorry

/-- On every strictly positive-time tail of an arbitrary-dimensional
Ricci-flow solution, the intrinsic curvature-derivative norm satisfies the
Bernstein tower heat inequality. -/
theorem towerHeatSol_any
    {alpha t0 omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (k : Nat) :
    let D' := RealTimeInterval.closedOpen t0 omega ht0omega
    let S' := S.timeRestrict D'
    TowerHeatBoundOn (D := D')
      (nablaKRm04NormSqIntrinsic (I := I) S')
      (nablaKNormLap (I := I) S')
      (2 * (Module.finrank Real E : Real) ^ (6 + k)) k := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega ht0omega
  let S' := S.timeRestrict D'
  change TowerHeatBoundOn (D := D')
    (nablaKRm04NormSqIntrinsic (I := I) S')
    (nablaKNormLap (I := I) S')
    (2 * (Module.finrank Real E : Real) ^ (6 + k)) k
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using
      isSoln_tailRestrict (I := I) hS halphat0 ht0omega
  obtain ⟨level, star, htower⟩ := exists_rmTowerSol (I := I) S' hS'
  simpa only [Fintype.card_fin] using
    (iteratedRmTower_heatBound
      (Idx := Fin (Module.finrank Real E)) htower k)

end DifferentialGeometry.PDE.RicciFlow
