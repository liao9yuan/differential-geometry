import RicciFlower.RicciFlow.Evolution.LocalPinching

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! # MSM110 Chapter 6.5: Local Pinching Estimates -/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section05

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}

theorem lem_ricci_pinching_preserved
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (hode : ∀ x : M, True)
    (hordered : CurvatureEigenvaluesOrdered lambda mu nu)
    (hinit : ∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) :
    RicciPinchingPreservedOn lambda mu nu C :=
  RicciFlower.RicciFlow.ricci_pinching_preserved
    lambda mu nu C hode hordered hinit

theorem cor_ricci_lower_bound
    (lambda mu nu ricciLower scalar : Real -> M -> Real)
    (C beta : Real)
    (hpinch : RicciPinchingPreservedOn lambda mu nu C)
    (hbeta : beta > 0) :
    RicciLowerBoundFromPinchingOn ricciLower scalar beta :=
  RicciFlower.RicciFlow.ricci_lower_bound_of_pinching
    lambda mu nu ricciLower scalar C beta hpinch hbeta

theorem thm_ricci_pinching_improves_theorem
    (lambda mu nu : Real -> M -> Real)
    (hpositiveRicciInitial : Prop) :
    ∃ C delta : Real, ∃ weight : Real -> M -> Real,
      0 < C ∧ 0 < delta ∧ delta < 1 ∧
      PinchingDecayWeightOn lambda mu nu weight delta ∧
      RicciPinchingImprovesOn lambda mu nu weight C :=
  RicciFlower.RicciFlow.ricci_pinching_improves
    lambda mu nu hpositiveRicciInitial

theorem eq_pinching_estimate_hamilton_form
    (lambda mu nu tracefreeRmNormSq scalar weight : Real -> M -> Real)
    (C : Real)
    (hpinch : RicciPinchingImprovesOn lambda mu nu weight C) :
    HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C :=
  RicciFlower.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching
    lambda mu nu tracefreeRmNormSq scalar weight C hpinch

theorem lem_palpha_over_qbeta
    (phi psi quotient rhs : Real -> M -> Real)
    (hphi : ∀ t x, 0 ≤ phi t x)
    (hpsi : ∀ t x, 0 < psi t x) :
    PAlphaOverQBetaFormulaOn phi psi quotient rhs :=
  RicciFlower.RicciFlow.palpha_over_qbeta_formula phi psi quotient rhs hphi hpsi

theorem item_define_p
    (lambda mu nu P : Real -> M -> Real)
    (h : PinchingPFormulaOn lambda mu nu P) :
    PinchingPFormulaOn lambda mu nu P := h

theorem lem_f_pinching_evolution
    (f scalar Q : Real -> M -> Real) (epsilon : Real)
    (hpq : Prop) :
    TracefreeRmPinchingEvolutionInequalityOn f scalar Q epsilon :=
  RicciFlower.RicciFlow.tracefree_rm_pinching_evolution f scalar Q epsilon hpq

end

end Section05
end Chapter06
end MSM110
end BK
