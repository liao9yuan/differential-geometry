import RicciFlower.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bounded Geometry Inputs

The records in this file state the curvature and curvature-derivative
assumptions used by MSM135 compactness theorems.  The pointwise bound
predicates are primitive theorem-facing predicates pending a full curvature
derivative norm API in the metric compactness layer.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Global bound `|∇^k Rm| ≤ C` for one pointed metric object. -/
axiom HasCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : Nat) (C : Real) : Prop

/-- Bounded geometry for one pointed metric: all covariant derivatives of
curvature have global bounds. -/
structure BoundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall k : Nat, HasCurvDerivBound (I := I) X k (C k)

/-- Uniform bounded geometry for a pointed metric sequence, matching MSM135
Definition 3.8. -/
structure SeqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasCurvDerivBound (I := I) (X.obj i) k (C k)

/-- Global spacetime curvature bound for one pointed flow. -/
axiom HasSpacetimeCurvBound
    {D : Realized.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop

/-- Global spacetime curvature-derivative bound for one pointed flow. -/
axiom HasSpacetimeCurvDerivBound
    {D : Realized.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (k : Nat) (C : Real) : Prop

/-- Uniform zeroth-order curvature bound for a pointed flow sequence. -/
structure SpacetimeCurvBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Real
  nonneg : 0 <= C
  bound : forall i : Nat, HasSpacetimeCurvBound (I := I) (X.term i) C

/-- Uniform spacetime curvature-derivative bounds for a pointed flow sequence.

This is stronger than the zeroth-order curvature bound and is the explicit
input used until Shi-type derivative estimates are formalized. -/
structure FlowDerivBounds
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasSpacetimeCurvDerivBound (I := I) (X.term i) k (C k)

/-- Honest derivative input for solution compactness.

The time-zero bounded-geometry field is explicit because the primitive
spacetime derivative predicates are not yet connected to the metric
curvature-derivative predicates by a proved restriction theorem. -/
structure FlowDerivativeInput
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  spacetime : FlowDerivBounds (I := I) X
  at_zero_geom : SeqBoundedGeometry (I := I) (X.atZero (I := I))

end HCGCompactness
end RicciFlower
