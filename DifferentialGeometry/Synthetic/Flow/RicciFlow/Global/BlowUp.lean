import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.Existence
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Geometric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Blow-Up and Extension Criterion Interfaces

These are global Ricci-flow inputs used after the tensor maximum-principle and
pinching estimates.
-/

open SyntheticTensor

/-- A quantity is bounded above on an abstract time domain. -/
def BoundedAboveOn {R Time : Type*} [Preorder R]
    (q : Time -> R) (domain : Time -> Prop) : Prop :=
  exists C, forall t, domain t -> q t <= C

/-- A quantity is unbounded above on an abstract time domain. -/
def UnboundedAboveOn {R Time : Type*} [Preorder R]
    (q : Time -> R) (domain : Time -> Prop) : Prop :=
  forall C, exists t, domain t /\ C <= q t

section BlowUpInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Black-box form of Lemma 11.1: positive initial scalar curvature forces a
finite maximal existence time, with an initial-data-dependent upper bound. -/
class PositiveScalarFiniteTimeTheorem where
  PositiveInitialScalar : RicciFlowData k R V Time A -> Prop
  HasFiniteMaximalTime : RicciFlowData k R V Time A -> Prop
  UpperBoundForMaximalTime : RicciFlowData k R V Time A -> R -> Prop
  finite_time :
    forall D : RicciFlowData k R V Time A,
      PositiveInitialScalar D -> HasFiniteMaximalTime D
  finite_time_bound :
    forall D : RicciFlowData k R V Time A,
      PositiveInitialScalar D -> exists bound, UpperBoundForMaximalTime D bound

theorem finite_time_singularity_from_positive_scalar
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    (D : RicciFlowData k R V Time A)
    (hpos : H.PositiveInitialScalar D) :
    H.HasFiniteMaximalTime D :=
  H.finite_time D hpos

theorem finite_time_singularity_bound_from_positive_scalar
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    (D : RicciFlowData k R V Time A)
    (hpos : H.PositiveInitialScalar D) :
    exists bound, H.UpperBoundForMaximalTime D bound :=
  H.finite_time_bound D hpos

/-- Black-box extension criterion: bounded curvature allows extension. -/
class RicciFlowExtensionCriterion where
  curvatureQuantity : RicciFlowData k R V Time A -> Time -> R
  CanExtendPast : RicciFlowData k R V Time A -> Time -> Prop
  extend_of_bounded_curvature :
    forall (D : RicciFlowData k R V Time A) (T : Time) (domain : Time -> Prop),
      BoundedAboveOn (curvatureQuantity D) domain -> CanExtendPast D T

/-- Bridge from an abstract finite-maximal-time predicate to the terminal time
at which the flow cannot be extended. This keeps
`PositiveScalarFiniteTimeTheorem.HasFiniteMaximalTime` abstract while making
the next blow-up step composable. The concrete realization should instantiate
this from its maximal-interval object. -/
class MaximalTimeWitness
    (HasFiniteMaximalTime : RicciFlowData k R V Time A -> Prop) where
  terminalTime : RicciFlowData k R V Time A -> Time
  nonextendable_at_terminal :
    forall D : RicciFlowData k R V Time A,
      HasFiniteMaximalTime D ->
        forall ext : RicciFlowExtensionCriterion k R V Time A,
          ¬ ext.CanExtendPast D (terminalTime D)

theorem maximal_time_nonextendable_from_interface
    {HasFiniteMaximalTime : RicciFlowData k R V Time A -> Prop}
    [H : MaximalTimeWitness k R V Time A HasFiniteMaximalTime]
    (D : RicciFlowData k R V Time A)
    (hfinite : HasFiniteMaximalTime D) :
    forall ext : RicciFlowExtensionCriterion k R V Time A,
      ¬ ext.CanExtendPast D (H.terminalTime D) :=
  H.nonextendable_at_terminal D hfinite

/-- Black-box curvature blow-up alternative at a finite singular time. -/
class CurvatureBlowUpAlternative where
  curvatureQuantity : RicciFlowData k R V Time A -> Time -> R
  domain : RicciFlowData k R V Time A -> Time -> Time -> Prop
  blows_up_if_not_extendable :
    forall (D : RicciFlowData k R V Time A) (T : Time),
      (forall ext : RicciFlowExtensionCriterion k R V Time A,
        ¬ ext.CanExtendPast D T) ->
      UnboundedAboveOn (curvatureQuantity D) (domain D T)

/-- Lemma 11.2: at a finite maximal time, curvature blows up. This is the
formal contradiction with the extension criterion, kept as a black-box
alternative in the current global layer. -/
theorem finite_time_curvature_blow_up_from_maximality
    [H : CurvatureBlowUpAlternative k R V Time A]
    (D : RicciFlowData k R V Time A) (T : Time)
    (hmax : forall ext : RicciFlowExtensionCriterion k R V Time A,
      ¬ ext.CanExtendPast D T) :
    UnboundedAboveOn (H.curvatureQuantity D) (H.domain D T) :=
  H.blows_up_if_not_extendable D T hmax

/-- Curvature blow-up directly from an abstract finite-time predicate once the
realization supplies a terminal-time witness for that predicate. -/
theorem finite_time_curvature_blow_up_from_finite_time
    [F : PositiveScalarFiniteTimeTheorem k R V Time A]
    [W : MaximalTimeWitness k R V Time A F.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    (D : RicciFlowData k R V Time A)
    (hfinite : F.HasFiniteMaximalTime D) :
    UnboundedAboveOn (B.curvatureQuantity D) (B.domain D (W.terminalTime D)) :=
  finite_time_curvature_blow_up_from_maximality k R V Time A D (W.terminalTime D)
    (maximal_time_nonextendable_from_interface k R V Time A D hfinite)

/-- Interface for the scalar-curvature blow-up consequence used by point
selection: full curvature blow-up plus three-dimensional Ricci control gives
unbounded scalar curvature. -/
class ScalarBlowUpFromCurvatureBlowUp where
  scalarQuantity : RicciFlowData k R V Time A -> Time -> R
  domain : RicciFlowData k R V Time A -> Time -> Prop
  scalar_unbounded_of_curvature_blowup :
    forall [B : CurvatureBlowUpAlternative k R V Time A]
      (D : RicciFlowData k R V Time A) (T : Time),
      UnboundedAboveOn (B.curvatureQuantity D) (B.domain D T) ->
      UnboundedAboveOn (scalarQuantity D) (domain D)

theorem scalar_unbounded_from_curvature_blowup
    [H : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [B : CurvatureBlowUpAlternative k R V Time A]
    (D : RicciFlowData k R V Time A) (T : Time)
    (hblow : UnboundedAboveOn (B.curvatureQuantity D) (B.domain D T)) :
    UnboundedAboveOn (H.scalarQuantity D) (H.domain D) :=
  H.scalar_unbounded_of_curvature_blowup D T hblow

end BlowUpInterfaces

section GeometricBlowUpInterfaces

variable (k R V Time A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Geometric flow abbreviation used by the global interfaces. -/
abbrev GeometricFlow :=
  GeometricRicciFlowData k R V Time A Manifold Point Metric

/-- Positive initial scalar curvature as an actual pointwise statement on the
initial time slice of a geometric Ricci flow. -/
def GeometricPositiveInitialScalar (G : GeometricFlow k R V Time A Manifold Point Metric) :
    Prop :=
  forall p, G.pointMem p -> 0 < G.scalarAt p G.initialTime

/-- Geometric form of Lemma 11.1: positive initial scalar curvature forces a
finite maximal time, with an initial-data-dependent upper bound. -/
class GeometricPositiveScalarFiniteTimeTheorem where
  HasFiniteMaximalTime : GeometricFlow k R V Time A Manifold Point Metric -> Prop
  UpperBoundForMaximalTime :
    GeometricFlow k R V Time A Manifold Point Metric -> R -> Prop
  finite_time :
    forall G : GeometricFlow k R V Time A Manifold Point Metric,
      GeometricPositiveInitialScalar k R V Time A Manifold Point Metric G ->
        HasFiniteMaximalTime G
  finite_time_bound :
    forall G : GeometricFlow k R V Time A Manifold Point Metric,
      GeometricPositiveInitialScalar k R V Time A Manifold Point Metric G ->
        exists bound, UpperBoundForMaximalTime G bound

theorem geometric_finite_time_singularity_from_positive_scalar
    [H : GeometricPositiveScalarFiniteTimeTheorem k R V Time A Manifold Point Metric]
    (G : GeometricFlow k R V Time A Manifold Point Metric)
    (hpos : GeometricPositiveInitialScalar k R V Time A Manifold Point Metric G) :
    H.HasFiniteMaximalTime G :=
  H.finite_time G hpos

theorem geometric_finite_time_singularity_bound_from_positive_scalar
    [H : GeometricPositiveScalarFiniteTimeTheorem k R V Time A Manifold Point Metric]
    (G : GeometricFlow k R V Time A Manifold Point Metric)
    (hpos : GeometricPositiveInitialScalar k R V Time A Manifold Point Metric G) :
    exists bound, H.UpperBoundForMaximalTime G bound :=
  H.finite_time_bound G hpos

/-- Geometric extension criterion: bounded spacetime curvature allows extension
past the terminal time. -/
class GeometricRicciFlowExtensionCriterion where
  curvatureQuantity : GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  CanExtendPast : GeometricFlow k R V Time A Manifold Point Metric -> Time -> Prop
  extend_of_bounded_curvature :
    forall (G : GeometricFlow k R V Time A Manifold Point Metric)
        (T : Time) (domain : Point -> Time -> Prop),
      BoundedAboveOnSpacetime (curvatureQuantity G) domain ->
        CanExtendPast G T

/-- Bridge from a finite-maximal-time predicate to an actual terminal time.
Concrete maximal-interval realizations should instantiate this. -/
class GeometricMaximalTimeWitness
    (HasFiniteMaximalTime :
      GeometricFlow k R V Time A Manifold Point Metric -> Prop) where
  terminalTime : GeometricFlow k R V Time A Manifold Point Metric -> Time
  nonextendable_at_terminal :
    forall G : GeometricFlow k R V Time A Manifold Point Metric,
      HasFiniteMaximalTime G ->
        forall ext :
            GeometricRicciFlowExtensionCriterion k R V Time A Manifold Point Metric,
          ¬ ext.CanExtendPast G (terminalTime G)

theorem geometric_maximal_time_nonextendable_from_interface
    {HasFiniteMaximalTime :
      GeometricFlow k R V Time A Manifold Point Metric -> Prop}
    [H : GeometricMaximalTimeWitness k R V Time A Manifold Point Metric
      HasFiniteMaximalTime]
    (G : GeometricFlow k R V Time A Manifold Point Metric)
    (hfinite : HasFiniteMaximalTime G) :
    forall ext : GeometricRicciFlowExtensionCriterion k R V Time A Manifold Point Metric,
      ¬ ext.CanExtendPast G (H.terminalTime G) :=
  H.nonextendable_at_terminal G hfinite

/-- Geometric curvature blow-up alternative at a finite singular time. -/
class GeometricCurvatureBlowUpAlternative where
  curvatureQuantity : GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  domain : GeometricFlow k R V Time A Manifold Point Metric -> Time -> Point -> Time -> Prop
  blows_up_if_not_extendable :
    forall (G : GeometricFlow k R V Time A Manifold Point Metric) (T : Time),
      (forall ext :
          GeometricRicciFlowExtensionCriterion k R V Time A Manifold Point Metric,
        ¬ ext.CanExtendPast G T) ->
      UnboundedAboveOnSpacetime (curvatureQuantity G) (domain G T)

/-- Lemma 11.2 in the geometric layer: at a nonextendable terminal time,
curvature is unbounded on spacetime. -/
theorem geometric_finite_time_curvature_blow_up_from_maximality
    [H : GeometricCurvatureBlowUpAlternative k R V Time A Manifold Point Metric]
    (G : GeometricFlow k R V Time A Manifold Point Metric) (T : Time)
    (hmax :
      forall ext : GeometricRicciFlowExtensionCriterion k R V Time A Manifold Point Metric,
        ¬ ext.CanExtendPast G T) :
    UnboundedAboveOnSpacetime (H.curvatureQuantity G) (H.domain G T) :=
  H.blows_up_if_not_extendable G T hmax

/-- Curvature blow-up directly from a geometric finite-time predicate once the
realization supplies a terminal-time witness. -/
theorem geometric_finite_time_curvature_blow_up_from_finite_time
    [F : GeometricPositiveScalarFiniteTimeTheorem k R V Time A Manifold Point Metric]
    [W : GeometricMaximalTimeWitness k R V Time A Manifold Point Metric
      F.HasFiniteMaximalTime]
    [B : GeometricCurvatureBlowUpAlternative k R V Time A Manifold Point Metric]
    (G : GeometricFlow k R V Time A Manifold Point Metric)
    (hfinite : F.HasFiniteMaximalTime G) :
    UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G (W.terminalTime G)) :=
  geometric_finite_time_curvature_blow_up_from_maximality
    k R V Time A Manifold Point Metric G (W.terminalTime G)
    (geometric_maximal_time_nonextendable_from_interface
      k R V Time A Manifold Point Metric G hfinite)

/-- Geometric scalar blow-up consequence used by point selection. -/
class GeometricScalarBlowUpFromCurvatureBlowUp where
  scalarQuantity : GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  domain : GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> Prop
  scalar_unbounded_of_curvature_blowup :
    forall [B : GeometricCurvatureBlowUpAlternative k R V Time A Manifold Point Metric]
      (G : GeometricFlow k R V Time A Manifold Point Metric) (T : Time),
      UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G T) ->
      UnboundedAboveOnSpacetime (scalarQuantity G) (domain G)

theorem geometric_scalar_unbounded_from_curvature_blowup
    [H : GeometricScalarBlowUpFromCurvatureBlowUp k R V Time A Manifold Point Metric]
    [B : GeometricCurvatureBlowUpAlternative k R V Time A Manifold Point Metric]
    (G : GeometricFlow k R V Time A Manifold Point Metric) (T : Time)
    (hblow : UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G T)) :
    UnboundedAboveOnSpacetime (H.scalarQuantity G) (H.domain G) :=
  H.scalar_unbounded_of_curvature_blowup G T hblow

end GeometricBlowUpInterfaces

section IntervalGeometricBlowUpInterfaces

variable (k R V FlowTime AmbientTime A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Interval-aware geometric flow abbreviation used by global interfaces.
`FlowTime` is the smooth time type; endpoint and infinity data live in
`AmbientTime`. -/
abbrev IntervalGeometricFlow :=
  GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric

/-- Positive initial scalar curvature as a pointwise statement on the initial
regular time slice of an interval-aware geometric Ricci flow. -/
def IntervalPositiveInitialScalar
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric) :
    Prop :=
  forall p, G.pointMem p -> 0 < G.scalarAt p G.initialTime

/-- Interval-aware form of Lemma 11.1: positive initial scalar curvature
forces finite maximal time. Finite maximal time is a predicate; infinite
maximal intervals simply do not produce it. -/
class IntervalPositiveScalarFiniteTimeTheorem where
  HasFiniteMaximalTime :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> Prop
  UpperBoundForMaximalTime :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> R -> Prop
  finite_time :
    forall G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric,
      IntervalPositiveInitialScalar k R V FlowTime AmbientTime A Manifold Point Metric G ->
        HasFiniteMaximalTime G
  finite_time_bound :
    forall G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric,
      IntervalPositiveInitialScalar k R V FlowTime AmbientTime A Manifold Point Metric G ->
        exists bound, UpperBoundForMaximalTime G bound

theorem interval_finite_time_singularity_from_positive_scalar
    [H : IntervalPositiveScalarFiniteTimeTheorem
      k R V FlowTime AmbientTime A Manifold Point Metric]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (hpos :
      IntervalPositiveInitialScalar k R V FlowTime AmbientTime A Manifold Point Metric G) :
    H.HasFiniteMaximalTime G :=
  H.finite_time G hpos

theorem interval_finite_time_singularity_bound_from_positive_scalar
    [H : IntervalPositiveScalarFiniteTimeTheorem
      k R V FlowTime AmbientTime A Manifold Point Metric]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (hpos :
      IntervalPositiveInitialScalar k R V FlowTime AmbientTime A Manifold Point Metric G) :
    exists bound, H.UpperBoundForMaximalTime G bound :=
  H.finite_time_bound G hpos

/-- Interval-aware extension criterion. Extension is past an ambient terminal
time, while curvature boundedness is stated on regular spacetime. -/
class IntervalRicciFlowExtensionCriterion where
  curvatureQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  CanExtendPast :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      AmbientTime -> Prop
  extend_of_bounded_curvature :
    forall (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
        (T : AmbientTime) (domain : Point -> FlowTime -> Prop),
      BoundedAboveOnSpacetime (curvatureQuantity G) domain ->
        CanExtendPast G T

/-- Bridge from finite maximality to an ambient terminal time. -/
class IntervalMaximalTimeWitness
    (HasFiniteMaximalTime :
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> Prop) where
  terminalTime :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> AmbientTime
  nonextendable_at_terminal :
    forall G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric,
      HasFiniteMaximalTime G ->
        forall ext :
            IntervalRicciFlowExtensionCriterion
              k R V FlowTime AmbientTime A Manifold Point Metric,
          ¬ ext.CanExtendPast G (terminalTime G)

theorem interval_maximal_time_nonextendable_from_interface
    {HasFiniteMaximalTime :
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> Prop}
    [H : IntervalMaximalTimeWitness
      k R V FlowTime AmbientTime A Manifold Point Metric HasFiniteMaximalTime]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (hfinite : HasFiniteMaximalTime G) :
    forall ext :
        IntervalRicciFlowExtensionCriterion
          k R V FlowTime AmbientTime A Manifold Point Metric,
      ¬ ext.CanExtendPast G (H.terminalTime G) :=
  H.nonextendable_at_terminal G hfinite

/-- Interval-aware curvature blow-up alternative: the terminal time is ambient,
but the unbounded quantity is sampled only at regular flow times. -/
class IntervalCurvatureBlowUpAlternative where
  curvatureQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  domain :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      AmbientTime -> Point -> FlowTime -> Prop
  blows_up_if_not_extendable :
    forall (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
        (T : AmbientTime),
      (forall ext :
          IntervalRicciFlowExtensionCriterion
            k R V FlowTime AmbientTime A Manifold Point Metric,
        ¬ ext.CanExtendPast G T) ->
      UnboundedAboveOnSpacetime (curvatureQuantity G) (domain G T)

theorem interval_finite_time_curvature_blow_up_from_maximality
    [H : IntervalCurvatureBlowUpAlternative
      k R V FlowTime AmbientTime A Manifold Point Metric]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (T : AmbientTime)
    (hmax :
      forall ext :
          IntervalRicciFlowExtensionCriterion
            k R V FlowTime AmbientTime A Manifold Point Metric,
        ¬ ext.CanExtendPast G T) :
    UnboundedAboveOnSpacetime (H.curvatureQuantity G) (H.domain G T) :=
  H.blows_up_if_not_extendable G T hmax

theorem interval_finite_time_curvature_blow_up_from_finite_time
    [F : IntervalPositiveScalarFiniteTimeTheorem
      k R V FlowTime AmbientTime A Manifold Point Metric]
    [W : IntervalMaximalTimeWitness
      k R V FlowTime AmbientTime A Manifold Point Metric F.HasFiniteMaximalTime]
    [B : IntervalCurvatureBlowUpAlternative
      k R V FlowTime AmbientTime A Manifold Point Metric]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (hfinite : F.HasFiniteMaximalTime G) :
    UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G (W.terminalTime G)) :=
  interval_finite_time_curvature_blow_up_from_maximality
    k R V FlowTime AmbientTime A Manifold Point Metric G (W.terminalTime G)
    (interval_maximal_time_nonextendable_from_interface
      k R V FlowTime AmbientTime A Manifold Point Metric G hfinite)

/-- Interval-aware scalar blow-up consequence used by point selection. -/
class IntervalScalarBlowUpFromCurvatureBlowUp where
  scalarQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  domain :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> Prop
  scalar_unbounded_of_curvature_blowup :
    forall [B : IntervalCurvatureBlowUpAlternative
      k R V FlowTime AmbientTime A Manifold Point Metric]
      (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
      (T : AmbientTime),
      UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G T) ->
      UnboundedAboveOnSpacetime (scalarQuantity G) (domain G)

theorem interval_scalar_unbounded_from_curvature_blowup
    [H : IntervalScalarBlowUpFromCurvatureBlowUp
      k R V FlowTime AmbientTime A Manifold Point Metric]
    [B : IntervalCurvatureBlowUpAlternative
      k R V FlowTime AmbientTime A Manifold Point Metric]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (T : AmbientTime)
    (hblow : UnboundedAboveOnSpacetime (B.curvatureQuantity G) (B.domain G T)) :
    UnboundedAboveOnSpacetime (H.scalarQuantity G) (H.domain G) :=
  H.scalar_unbounded_of_curvature_blowup G T hblow

end IntervalGeometricBlowUpInterfaces

