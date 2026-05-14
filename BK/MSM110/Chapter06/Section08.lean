import RicciFlower.RicciFlow.Evolution.FiniteTimeBlowup

set_option autoImplicit false
set_option linter.style.longLine false

/-! # MSM110 Chapter 6.8: Finite-Time Blowup -/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section08

noncomputable section

open RicciFlower.RicciFlow

theorem lem_finite_time_singularity
    (T t0 rho : Real)
    (hweakMaximumPrinciple hscalarInf : Prop)
    (hrho : 0 < rho) :
    FiniteTimeSingularityConclusion T :=
  RicciFlower.RicciFlow.finite_time_singularity
    T t0 rho hweakMaximumPrinciple hscalarInf hrho

theorem cor_curvature_blowup_two
    (curvSup : Real -> Real) (T : Real)
    (hpositiveRicciInitial : Prop)
    (hfinite : FiniteTimeSingularityConclusion T)
    (hblowup : CurvatureBlowupAtMaximalTime curvSup T) :
    CurvatureBlowupTwoConclusion curvSup T :=
  RicciFlower.RicciFlow.curvature_blowup_two
    curvSup T hpositiveRicciInitial hfinite hblowup

theorem lem_positive_sectional_pinching
    (scalarMin scalarMax lambdaMax nuMin : Real -> Real) (T : Real)
    (hpositiveRicciInitial hlocalPinching hgradientEstimate : Prop) :
    PositiveSectionalPinchingConclusion scalarMin scalarMax lambdaMax nuMin T :=
  RicciFlower.RicciFlow.positive_sectional_pinching
    scalarMin scalarMax lambdaMax nuMin T
    hpositiveRicciInitial hlocalPinching hgradientEstimate

theorem cor_uniform_convergence_to_einstein
    (tracefreeRicciRatio : Real -> Real) (T : Real)
    (hpinching : PositiveSectionalPinchingConclusion
      (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 1) T)
    (hhamiltonPinching : Prop) :
    UniformConvergenceToEinsteinConclusion tracefreeRicciRatio T :=
  RicciFlower.RicciFlow.uniform_convergence_to_einstein
    tracefreeRicciRatio T hpinching hhamiltonPinching

end

end Section08
end Chapter06
end MSM110
end BK
