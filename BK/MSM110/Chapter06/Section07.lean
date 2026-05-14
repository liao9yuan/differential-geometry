import RicciFlower.RicciFlow.Evolution.LongTimeExistence

set_option autoImplicit false
set_option linter.style.longLine false

/-! # MSM110 Chapter 6.7: Higher Derivative Estimates and Long-Time Existence -/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section07

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}

theorem thm_chapter_five_curvature_derivative_bounds_assumed
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real) :
    BBSDerivativeEstimateOn curvNorm derivNorm :=
  RicciFlower.RicciFlow.chapter_five_curvature_derivative_bounds_assumed
    curvNorm derivNorm

theorem cor_chapter_five_curvature_derivative_bounds_used
    (curvNorm : Real -> M -> Real)
    (derivNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (hBBS : BBSDerivativeEstimateOn curvNorm derivNorm)
    (hcurv : ∀ t x, 0 ≤ t -> t ≤ T -> curvNorm t x ≤ K) :
    UniformCurvatureDerivativeBoundsOn curvNorm derivNorm K T :=
  RicciFlower.RicciFlow.chapter_five_curvature_derivative_bounds_used
    curvNorm derivNorm K T hBBS hcurv

theorem prop_metric_derivative_bounds
    (metricDerivNorm curvNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (hcurv : ∀ t x, 0 ≤ t -> t < T -> curvNorm 0 t x ≤ K) :
    MetricDerivativeBoundsOn metricDerivNorm T :=
  RicciFlower.RicciFlow.metric_derivative_bounds
    metricDerivNorm curvNorm K T hcurv

theorem lem_continuous_limit_metric
    (metricDistToLimit : Real -> M -> Real) (T C : Real)
    (hintegrableTimeDerivative : Prop) :
    ContinuousLimitMetricAt metricDistToLimit T :=
  RicciFlower.RicciFlow.continuous_limit_metric
    metricDistToLimit T C hintegrableTimeDerivative

theorem cor_uniform_equivalence_of_metrics
    (metricRatioUpper metricRatioLower : Real -> M -> Real) (K T : Real)
    (hricciBound : Prop) :
    ∃ lowerBound upperBound : Real,
      UniformEquivalenceOfMetricsOn
        metricRatioUpper metricRatioLower lowerBound upperBound T :=
  RicciFlower.RicciFlow.uniform_equivalence_of_metrics
    metricRatioUpper metricRatioLower K T hricciBound

theorem cor_ricci_derivative_bounds
    (ricciDerivNorm curvNorm : Nat -> Real -> M -> Real)
    (K T : Real)
    (hcurv : ∀ t x, 0 ≤ t -> t < T -> curvNorm 0 t x ≤ K) :
    RicciDerivativeBoundsOn ricciDerivNorm T :=
  RicciFlower.RicciFlow.ricci_derivative_bounds
    ricciDerivNorm curvNorm K T hcurv

theorem thm_curvature_blowup
    (curvSup : Real -> Real) (T : Real)
    (hmaximal hshortTimeExistence hBBS : Prop) :
    CurvatureBlowupAtMaximalTime curvSup T :=
  RicciFlower.RicciFlow.curvature_blowup
    curvSup T hmaximal hshortTimeExistence hBBS

end

end Section07
end Chapter06
end MSM110
end BK
