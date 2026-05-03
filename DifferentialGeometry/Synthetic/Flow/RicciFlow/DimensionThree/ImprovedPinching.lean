import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.Pinching
import DifferentialGeometry.Synthetic.Analysis.Parabolic.ScalarMaximumPrinciple

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved Ricci Pinching: Maximum-Principle Consumer

This file keeps the analytic support for Hamilton's improved pinching estimate
small.  The heavy calculation still has to prove that the Hamilton pinching
quantity is a scalar subsolution; once that is available, the weak maximum
principle gives the estimate here.

The design deliberately avoids importing the large Sobolev/De Giorgi analysis
subtree.  Those files are useful as examples of `rpow` and decay estimates, but
the Ricci-flow layer only needs this narrow subsolution-to-bound step.
-/

section ImprovedPinchingMaximumPrinciple

variable {R Time : Type*}
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Data for the maximum-principle part of Hamilton's improved pinching
estimate.  `P` is the Hamilton quantity
`|Ric^0|^2 / R^(2 - epsilon)`.  `ratio` is the scale-invariant quantity
`|Ric^0|^2 / R^2`, and `decay` is the factor intended to be `R^(-epsilon)`.

The theorem below uses only the weak maximum principle.  The geometric work is
to instantiate `shifted_subsolution`, `initial_bound`, and
`ratio_decay_relation` from the Ricci-flow evolution identities.  In the
intended Ricci-flow instantiation, `ratio` is
`tracefreeRicciPinchingQuantity`, `decay` is `R^(-epsilon)`, and the relation
comes from an equality under positive scalar curvature; the consumer theorem
only needs the weaker inequality. -/
structure ImprovedRicciPinchingEstimateAlongFlow where
  problem : ScalarParabolicProblem R Time
  P : Time -> R
  ratio : Time -> R
  epsilon : R
  C : R
  decay : Time -> R
  shifted_subsolution : IsScalarSubsolution problem (fun t => P t - C)
  initial_bound : IsInitiallyNonpositive problem (fun t => P t - C)
  ratio_decay_relation :
    forall t, problem.domain t -> ratio t <= P t * decay t
  decay_nonnegative : forall t, problem.domain t -> 0 <= decay t

/-- The weak maximum principle gives the uniform bound `P <= C`. -/
theorem improved_pinching_P_bound_from_wmp
    [ScalarWeakMaximumPrinciple R Time]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time))
    (t : Time) (ht : E.problem.domain t) :
    E.P t <= E.C :=
  scalar_wmp_preserve_upper_bound E.problem E.P E.C E.shifted_subsolution
    E.initial_bound t ht

/-- The Section 12 ratio estimate
`|Ric^0|^2 / R^2 <= C * R^(-epsilon)`, stated with an abstract decay factor. -/
theorem improved_ricci_pinching_ratio_bound_from_wmp
    [ScalarWeakMaximumPrinciple R Time]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Time))
    (t : Time) (ht : E.problem.domain t) :
    E.ratio t <= E.C * E.decay t := by
  exact (E.ratio_decay_relation t ht).trans
    (mul_le_mul_of_nonneg_right
      (improved_pinching_P_bound_from_wmp E t ht) (E.decay_nonnegative t ht))

end ImprovedPinchingMaximumPrinciple
