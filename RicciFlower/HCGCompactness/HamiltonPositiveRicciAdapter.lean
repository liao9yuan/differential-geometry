import RicciFlower.HCGCompactness.HamiltonCompactness
import RicciFlower.HamiltonPositiveRicci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Adapter To The Hamilton Positive Ricci Endpoint

This file does not change `HamiltonPositiveRicci.lean`.  It only explains how a
new HCG compactness conclusion supplies the existing `Ham3CGHLimitExists`
black-box output used by `ham3_cgh_limit`.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff
open HamiltonPositiveRicci

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

namespace LimitFlowData

/-- Forget the new HCG convergence fields down to the current Section 12 limit
data record. -/
def toHam3
    {D : Realized.RealTimeInterval}
    (L : LimitFlowData.{u, uE, uH} I D) (subseq : Nat -> Nat) :
    Ham3CGHLimitData (I := I) M where
  N := L.M
  topology := L.topology
  charted := L.charted
  smooth := L.smooth
  smooth_plus := L.smoothPlus
  sigmaCompact := L.sigmaCompact
  t2 := L.t2
  basepoint := L.basepoint
  D := D
  S := L.S
  subseq := subseq

end LimitFlowData

/-- A compactness conclusion from the new HCG interface supplies the old
Hamilton Section 12 black-box conclusion.

The current `Ham3CGHLimitExists` proposition stores limit-flow data,
subsequence monotonicity, the fixed time window, regularity on the open fixed
window, connectedness, boundarylessness, the Ricci-flow predicate, the Ricci
nonnegativity transfer datum, the narrow scalar convergence at the selected
basepoints, and the pinching-transfer datum. Connectedness, boundarylessness,
Ricci transfer, base-scalar convergence, and pinching transfer are explicit
adapter inputs because they are not currently fields of the generic
`LimitFlowData` record. -/
theorem toHam3Exists
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hwindow : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier)
    (hreg : Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ X.D.regular)
    (hconnected :
      forall (L : LimitFlowData.{u, uE, uH} I X.D) (subseq : Nat -> Nat),
        Ham3LimitConnected (I := I) (M := M)
          (LimitFlowData.toHam3 (I := I) (M := M) L subseq))
    (hboundaryless :
      forall (L : LimitFlowData.{u, uE, uH} I X.D) (subseq : Nat -> Nat),
        Ham3LimitBoundaryless (I := I) (M := M)
          (LimitFlowData.toHam3 (I := I) (M := M) L subseq))
    (hricTransfer :
      forall (L : LimitFlowData.{u, uE, uH} I X.D) (subseq : Nat -> Nat),
        Ham3RicNonnegTransfer (I := I) (M := M) P Q
          (LimitFlowData.toHam3 (I := I) (M := M) L subseq))
    (hbaseScalar :
      forall (L : LimitFlowData.{u, uE, uH} I X.D) (subseq : Nat -> Nat),
        Ham3LimitBaseScalarConv (I := I) (M := M) P Q
          (LimitFlowData.toHam3 (I := I) (M := M) L subseq))
    (hpinchTransfer :
      forall (L : LimitFlowData.{u, uE, uH} I X.D) (subseq : Nat -> Nat),
        Ham3PinchTransfer (I := I) (M := M) P Q
          (LimitFlowData.toHam3 (I := I) (M := M) L subseq))
    (hcompact : CompactnessConclusion (I := I) X) :
    Ham3CGHLimitExists (I := I) P Q := by
  rcases hcompact with ⟨L, subseq, hsubseq, _hconv⟩
  refine
    ⟨LimitFlowData.toHam3 (I := I) (M := M) L subseq, hsubseq,
      hwindow, hreg, hconnected L subseq, hboundaryless L subseq, ?_,
      hricTransfer L subseq, hbaseScalar L subseq, hpinchTransfer L subseq⟩
  simpa [HamiltonPositiveRicci.Ham3LimitFlow, LimitFlowData.toHam3] using
    L.isSolution

end HCGCompactness
end RicciFlower
