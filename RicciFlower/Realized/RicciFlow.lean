import RicciFlower.Realized.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Realized Ricci-Flow Interfaces

The Ricci-flow equation is a predicate on a realized metric family. It is not a
field of a solution record.
-/

namespace RicciFlower
namespace Realized

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- A pointwise symmetric two-covariant curvature field, used for Ricci. -/
abbrev RealizedTwoTensorField (Time : Type*) :=
  Time -> (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

/-- The Ricci-flow metric variation equation, evaluated on fixed tangent vectors.

This is the realized version of `partial_t g = -2 Ric`. -/
def MetricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time) : Prop :=
  forall (t : Time) (x : M) (X Y : TangentSpace I x),
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y

/-- The metric evolution theorem extracted from the equation predicate. -/
theorem metric_dt_eq_neg_two_ricci_of_metricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (hEq : MetricVariationEquation td G Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y :=
  hEq t x X Y

/-- A data-only realized Ricci-flow candidate.

Being a Ricci-flow solution is expressed by `IsRealizedRicciFlow`, not by a
proof field on this structure. -/
structure RealizedRicciFlowData where
  family : RealizedMetricFamily (I := I) (M := M) Time

/-- Predicate saying that a data-only realized family solves the Ricci-flow equation
for the supplied Ricci tensor field. -/
def IsRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time) : Prop :=
  MetricVariationEquation td S.family Ric

theorem metric_dt_eq_neg_two_ricci_of_isRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (hS : IsRealizedRicciFlow td S Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td S.family t x X Y = (-2 : Real) * Ric t x X Y :=
  metric_dt_eq_neg_two_ricci_of_metricVariationEquation td S.family Ric hS t x X Y

end Realized
end RicciFlower
