import DifferentialGeometry.Synthetic.Flow.RicciFlow.Calculus

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci Flow Existence Interfaces

Short-time existence and maximal-interval construction are analytic inputs for
the final Hamilton theorem. They are kept as black-box interfaces.
-/

open SyntheticTensor

section ExistenceInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A concrete Ricci-flow solution packaged for black-box existence statements. -/
structure RicciFlowSolutionToken where
  data : RicciFlowData k R V Time A

/-- Short-time existence from an abstract initial-data type. -/
class ShortTimeExistence (Initial : Type*) where
  exists_solution : Initial -> Nonempty (RicciFlowSolutionToken k R V Time A)

/-- A maximal Ricci flow extending a short-time solution. -/
structure MaximalRicciFlow where
  data : RicciFlowData k R V Time A
  isMaximal : Prop

/-- Black-box maximal interval construction. -/
class MaximalIntervalExistence where
  extend_to_maximal : RicciFlowData k R V Time A -> Nonempty (MaximalRicciFlow k R V Time A)

end ExistenceInterfaces

