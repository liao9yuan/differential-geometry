import Mathlib.Order.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Tensor Parabolic Maximum Principle Interface

Hamilton's tensor maximum principle is represented as an abstract cone
invariance theorem. Concrete cone geometry can be supplied later by instances.
-/

/-- A cone in an abstract tensor space. -/
structure TensorCone (T : Type*) where
  mem : T -> Prop

/-- A tensor parabolic problem with a cone and a heat-inequality predicate. -/
structure TensorParabolicProblem (T Time : Type*) where
  domain : Time -> Prop
  initial : Time -> Prop
  cone : TensorCone T
  heatInequality : (Time -> T) -> Prop

def IsTensorSubsolution {T Time : Type*}
    (P : TensorParabolicProblem T Time) (u : Time -> T) : Prop :=
  P.heatInequality u

def IsInitiallyInCone {T Time : Type*}
    (P : TensorParabolicProblem T Time) (u : Time -> T) : Prop :=
  forall t, P.initial t -> P.cone.mem (u t)

/-- Black-box tensor maximum principle. -/
class TensorWeakMaximumPrinciple (T Time : Type*) where
  preserve_cone :
    forall (P : TensorParabolicProblem T Time) (u : Time -> T),
      IsTensorSubsolution P u ->
      IsInitiallyInCone P u ->
      forall t, P.domain t -> P.cone.mem (u t)

theorem tensor_wmp_preserve_cone
    {T Time : Type*} [TensorWeakMaximumPrinciple T Time]
    (P : TensorParabolicProblem T Time) (u : Time -> T)
    (hsub : IsTensorSubsolution P u) (hinit : IsInitiallyInCone P u)
    (t : Time) (ht : P.domain t) :
    P.cone.mem (u t) :=
  TensorWeakMaximumPrinciple.preserve_cone P u hsub hinit t ht

/-- Common cone-invariance proof pattern: if the initial cone membership is
given pointwise rather than already packaged as `IsInitiallyInCone`, package it
once and apply the tensor weak maximum principle. -/
theorem tensor_wmp_preserve_cone_of_initial
    {T Time : Type*} [TensorWeakMaximumPrinciple T Time]
    (P : TensorParabolicProblem T Time) (u : Time -> T)
    (hsub : IsTensorSubsolution P u)
    (hinit : forall t, P.initial t -> P.cone.mem (u t))
    (t : Time) (ht : P.domain t) :
    P.cone.mem (u t) :=
  tensor_wmp_preserve_cone P u hsub hinit t ht
