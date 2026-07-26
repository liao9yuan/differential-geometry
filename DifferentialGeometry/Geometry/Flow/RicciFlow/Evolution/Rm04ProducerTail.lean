import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Producer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TailFrameRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Uhlenbeck curvature evolution on positive-time tails

`Evolution/Rm04Producer.lean` proves the Uhlenbeck evolution
`∂ₜ Rm = Δ Rm − 2(B − B + B − B) − drift` from a Ricci-flow solution together with
one remaining input: a time-derivative field `gInvDt` for the coordinate inverse
metric, packaged as `MetricFrameSpacetimeRegularityInFrameOnLocal`.

On a strictly positive-time tail that input is not an assumption.  The canonical
chart inverse `coordInv` has the required frame-local time regularity
(`coordInvDerivLocal`), and the inverse-independent fields of the package come
from `tailFrameSpaceReg`; `tailCoordFrameReg` assembles the two.  This module
feeds that package to the two `Rm04Producer` endpoints, leaving theorems whose
only inputs are the ambient solution, its regularity, and the tail parameters.

The tail is described by a solution `St` on `[t₀, ω)` together with a proof that
it restricts an ambient solution on a strictly larger `(α, ω)`.  That ambient
room is what makes the closed left endpoint `t₀` an interior time of the original
solution, hence a point of metric smoothness.

This is a separate module because `SolutionOn.timeRestrict` and the tail
producers are stated in the `InnerProductSpace ℝ E` model-space context, while
`Rm04Producer` carries a separate `NormedSpace ℝ E` instance; mixing the two in
one file makes the two `SolutionOn` instance spines disagree.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The Uhlenbeck curvature evolution at the frame centre, on a positive-time
tail.**  Unconditional: `gInvDt` is the canonical `coordInvDt`, and the metric
regularity package comes from `tailCoordFrameReg`. -/
theorem rm04EvolTail_at
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega} {hT0Omega : t0 < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    {St : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen t0 omega hT0Omega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0)
    (hSt : St = S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
    (x₀ : M)
    (t : RealTimeInterval.RegularTime (RealTimeInterval.closedOpen t0 omega hT0Omega))
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real ↦ realizedRmBase (I := I) St x₀ s x₀ m)
      (rmLap (coordInv (I := I) St x₀ (t : Real) x₀)
            (nab2RmComp (I := I) St x₀ (t : Real) x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame
            (ricciOneUpCompInFrame (I := I) St (coordInv (I := I) St x₀)
              (coordinateFrameAt (I := I) x₀))
            (rmComp (I := I) St x₀) (t : Real) x₀ (m 0) (m 1) (m 2) (m 3))
      (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real) := by
  subst hSt
  exact rm04Evol_at (I := I) _ (isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega) x₀
    (coordInvDt (I := I) _ x₀)
    (tailCoordFrameReg (I := I) hS hAlphaT0 hT0Omega x₀) t m

/-- **`hev` for the forward-uniqueness lane on a positive-time tail —
unconditional.**  The per-point-centred families of a tail-restricted Ricci-flow
solution satisfy the Uhlenbeck reaction–diffusion evolution with the Ricci drift,
with no remaining hypothesis beyond the ambient solution and the tail. -/
theorem rm04EvolFamTail
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega} {hT0Omega : t0 < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    {St : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen t0 omega hT0Omega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0)
    (hSt : St = S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := RealTimeInterval.closedOpen t0 omega hT0Omega)
      (rm04Fam (I := I) St) (rm04LapFam (I := I) St) (rm04BFam (I := I) St)
      (ricUpFam (I := I) St) := by
  subst hSt
  exact rm04EvolFam (I := I) _ (isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega)
    (fun y => coordInvDt (I := I) _ y)
    (fun y => tailCoordFrameReg (I := I) hS hAlphaT0 hT0Omega y)

end DifferentialGeometry.PDE.RicciFlow
