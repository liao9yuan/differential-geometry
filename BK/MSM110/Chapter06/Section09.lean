import RicciFlower.RicciFlow.Evolution.NormalizedFlow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! # MSM110 Chapter 6.9: Properties of the Normalized Ricci Flow -/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section09

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem lem_scale_the_metric
    (psi : Real) (hpsi : 0 < psi)
    (gammaEq rm13Eq ricciEq scalarScale volumeScale : Prop) :
    MetricScalingRelations psi gammaEq rm13Eq ricciEq scalarScale volumeScale :=
  RicciFlower.RicciFlow.scale_the_metric
    psi hpsi gammaEq rm13Eq ricciEq scalarScale volumeScale

theorem eq_evolution_of_g_bar_one
    (psi tbar : Real -> Real)
    (hvolumeNormalized : Prop) :
    UnnormalizedToNormalizedRescaling psi tbar :=
  RicciFlower.RicciFlow.unnormalized_to_normalized_rescaling
    psi tbar hvolumeNormalized

theorem thm_long_time_existence_for_normalized_flow
    (Tbar : Real)
    (hunnormalizedPositiveRicci hfiniteBlowup hscalarBound : Prop) :
    NormalizedLongTimeExistenceConclusion Tbar :=
  RicciFlower.RicciFlow.long_time_existence_for_normalized_flow
    Tbar hunnormalizedPositiveRicci hfiniteBlowup hscalarBound

theorem lem_rmax_integral_diverges
    (rmax : Real -> Real) (T : Real)
    (hpositiveRicciInitial : Prop) :
    RmaxIntegralDiverges rmax T :=
  RicciFlower.RicciFlow.rmax_integral_diverges
    rmax T hpositiveRicciInitial

theorem lem_bound_r_bar
    (rmaxBar : Real -> Real)
    (hvolumeComparison hMyers hpinching : Prop) :
    ∃ C : Real, NormalizedScalarBound rmaxBar C :=
  RicciFlower.RicciFlow.bound_r_bar
    rmaxBar hvolumeComparison hMyers hpinching

theorem cor_normalized_flow_becomes_einstein
    (tracefreeRicciRatio : Real -> Real)
    (huniformUnnormalized hscaleInvariant : Prop) :
    NormalizedFlowBecomesEinstein tracefreeRicciRatio :=
  RicciFlower.RicciFlow.normalized_flow_becomes_einstein
    tracefreeRicciRatio huniformUnnormalized hscaleInvariant

theorem pure_scaling_metric_relations
    (phi : Real -> Real)
    (connectionStatic rm13Static ricciStatic rm04Scale scalarScale : Prop) :
    PureScalingMetricEvolutionRelations
      phi connectionStatic rm13Static ricciStatic rm04Scale scalarScale :=
  RicciFlower.RicciFlow.pure_scaling_metric_evolution_relations
    phi connectionStatic rm13Static ricciStatic rm04Scale scalarScale

theorem cor_curvature_evolutions_for_nrf
    (r : Real -> Real)
    (christoffelDt rm13Dt rm04Dt ricciDt scalarDt : Prop) :
    NormalizedCurvatureEvolutionsInFrameOn
      r christoffelDt rm13Dt rm04Dt ricciDt scalarDt :=
  RicciFlower.RicciFlow.curvature_evolutions_for_normalized_ricci_flow
    r christoffelDt rm13Dt rm04Dt ricciDt scalarDt

end

end Section09
end Chapter06
end MSM110
end BK
