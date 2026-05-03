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

section BlowUpInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Black-box extension criterion: bounded curvature allows extension. -/
class RicciFlowExtensionCriterion where
  curvatureQuantity : RicciFlowData k R V Time A -> Time -> R
  CanExtendPast : RicciFlowData k R V Time A -> Time -> Prop
  extend_of_bounded_curvature :
    forall (D : RicciFlowData k R V Time A) (T : Time) (domain : Time -> Prop),
      BoundedAboveOn (curvatureQuantity D) domain -> CanExtendPast D T

/-- Black-box curvature blow-up alternative at a finite singular time. -/
class CurvatureBlowUpAlternative where
  curvatureQuantity : RicciFlowData k R V Time A -> Time -> R
  BlowsUpAt : RicciFlowData k R V Time A -> Time -> Prop
  blows_up_if_not_extendable :
    forall (D : RicciFlowData k R V Time A) (T : Time),
      (forall ext : RicciFlowExtensionCriterion k R V Time A,
        ¬ ext.CanExtendPast D T) ->
      BlowsUpAt D T

end BlowUpInterfaces

