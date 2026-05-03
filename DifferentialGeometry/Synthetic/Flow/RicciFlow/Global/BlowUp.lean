import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.Existence

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

