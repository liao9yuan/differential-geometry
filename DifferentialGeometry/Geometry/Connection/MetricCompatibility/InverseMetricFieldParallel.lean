import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem inverseMetricSharp_covDeriv_eq (g : SmoothRiemannianMetric I M)
    {X : Π x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x)
    (v : TangentSpace I x) :
    metricSharp (I := I) g x
        ((cotangentCov (LeviCivita (I := I) g)).toFun (metricFlat (I := I) g X) x v) =
      (LeviCivita (I := I) g).toFun X x v := by
  classical
  refine metricFlatLinear_injective (I := I) g x ?_
  ext y
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [inner_metricSharp (I := I) g x
    ((cotangentCov (LeviCivita (I := I) g)).toFun (metricFlat (I := I) g X) x v) y]
  exact cotangentCov_metricDuality (I := I) g hX v y

theorem metricFlat_inverseMetricSharpField_eq (g : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    metricFlat (I := I) g (fun y : M => (inverseMetricSharpFib (I := I) g y) (β y)) b =
      cotangentToCLM (I := I) (β b) := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [metricFlat_apply]
  rw [inverseMetricSharpFib_inner (I := I) g b (β b) w]
  rfl

theorem inverseMetricSharpField_covGrad_eq_zero (g : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g y) (β y))) x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => (inverseMetricSharpFib (I := I) g b) (β b)) x v =
      inverseMetricSharpFib (I := I) g x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) := by
  classical
  set X : Π b : M, TangentSpace I b :=
    fun b : M => (inverseMetricSharpFib (I := I) g b) (β b) with hX
  have hflat : metricFlat (I := I) g X =
      fun b : M => cotangentToCLM (I := I) (β b) := by
    funext b
    exact metricFlat_inverseMetricSharpField_eq (I := I) g β b
  have hcore := inverseMetricSharp_covDeriv_eq (I := I) g (X := X) hβ v
  rw [hflat] at hcore
  rw [← hcore]
  rw [inverseMetricSharpFib_apply]
  congr 1

end Connection
end Integral
end DifferentialGeometry
