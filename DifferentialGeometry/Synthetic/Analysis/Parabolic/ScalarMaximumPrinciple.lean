import Mathlib.Order.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Parabolic Maximum Principle Interface

The Ricci-flow proof uses scalar weak and strong maximum principles. This file
keeps them as analytic interfaces, independent of the synthetic tensor algebra.
-/

/-- A scalar parabolic problem over an abstract time domain. -/
structure ScalarParabolicProblem (R Time : Type*) [Preorder R] [Zero R] where
  domain : Time -> Prop
  initial : Time -> Prop
  heat : (Time -> R) -> Time -> R

def IsScalarSubsolution {R Time : Type*} [Preorder R] [Zero R]
    (P : ScalarParabolicProblem R Time) (u : Time -> R) : Prop :=
  forall t, P.domain t -> P.heat u t <= 0

def IsInitiallyNonpositive {R Time : Type*} [Preorder R] [Zero R]
    (P : ScalarParabolicProblem R Time) (u : Time -> R) : Prop :=
  forall t, P.initial t -> u t <= 0

/-- Black-box weak maximum principle for scalar parabolic inequalities. -/
class ScalarWeakMaximumPrinciple (R Time : Type*) [Preorder R] [Zero R] where
  preserve_nonpositive :
    forall (P : ScalarParabolicProblem R Time) (u : Time -> R),
      IsScalarSubsolution P u ->
      IsInitiallyNonpositive P u ->
      forall t, P.domain t -> u t <= 0

theorem scalar_wmp_preserve_nonpositive
    {R Time : Type*} [Preorder R] [Zero R] [ScalarWeakMaximumPrinciple R Time]
    (P : ScalarParabolicProblem R Time) (u : Time -> R)
    (hsub : IsScalarSubsolution P u) (hinit : IsInitiallyNonpositive P u)
    (t : Time) (ht : P.domain t) :
    u t <= 0 :=
  ScalarWeakMaximumPrinciple.preserve_nonpositive P u hsub hinit t ht

/-- Black-box strong maximum principle for scalar parabolic inequalities. -/
class ScalarStrongMaximumPrinciple (R Time : Type*) [Preorder R] [Zero R] where
  strict_of_nontrivial :
    forall (P : ScalarParabolicProblem R Time) (u : Time -> R),
      (forall t, P.domain t -> 0 <= u t) ->
      (exists t, P.domain t /\ 0 < u t) ->
      forall t, P.domain t -> 0 < u t
