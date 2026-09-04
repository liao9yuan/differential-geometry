import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Hamilton

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- Conditional P5-D assembly: a common-window sequence of complete pointed
flows with uniform curvature and basepoint injectivity bounds has a smooth,
complete pointed Ricci-flow limit.  The hypotheses are exactly the native
Hamilton compactness inputs and do not assume the conclusion. -/
theorem std_limit_of_bounds
    {a b : Real} (h0 : (0 : Real) ∈ Ioo a b)
    (X : DifferentialGeometry.HCGCompactness.PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = RealTimeInterval.openInterval a b 0 h0)
    (hcomplete : DifferentialGeometry.HCGCompactness.CompleteInput (I := I) X)
    (hcurv : DifferentialGeometry.HCGCompactness.CurvBoundInput (I := I) X)
    (hinj : DifferentialGeometry.HCGCompactness.FlowBaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      ConnectedSpace (X.term k).M) :
    exists L : DifferentialGeometry.HCGCompactness.PointedFlowData.{u, uE, uH}
        (I := I) X.D,
      exists subseq : Nat -> Nat,
        StrictMono subseq ∧
          Nonempty (DifferentialGeometry.HCGCompactness.SmoothCGHConverges
            (I := I) X L subseq) ∧
            forall t : Real, t ∈ X.D.carrier ->
              DifferentialGeometry.HCGCompactness.MetricComplete
                (I := I) (L.atTime (I := I) t) := by
  exact DifferentialGeometry.HCGCompactness.compactnessSol
    (I := I) h0 X hD hcomplete hcurv hinj hconn

end DifferentialGeometry.PDE.RicciFlow
