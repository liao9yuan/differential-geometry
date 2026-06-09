import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension

/-!
# The inverse-metric sharp field is `∇`-parallel (the cometric parallelism `∇g⁻¹ = 0`)

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
inverse metric raises indices through the musical sharp `♯ = metricSharp g x`, packaged on the
realized one-covariant fibre `Tensor0SSpace 1 I x` as `inverseMetricSharpFib g x`
(`InverseMetricField.lean`), and globally as the smooth `Hom(T^*M, TM)` section
`inverseMetricSharpField g`.

This file proves that the inverse-metric raise is **`∇`-parallel** — the cometric form of
metric compatibility `∇g⁻¹ = 0`.  It is the raise companion of the index-lowering parallelism in
`TensorLoweringParallel.lean`: lowering is intertwined by `∇` because the metric is parallel; here
the raise is intertwined by `∇` for the same reason.

## The genuine content

The directional statement is the **sharp-parallelism** identity
```
∇₀_v (♯ ω)  =  ♯ (∇₀_v ω),
```
for a covector field `ω` (whose sharp field `b ↦ ♯ ω(b)` is differentiable at `x`), where the
left covariant derivative is the tangent-bundle Levi-Civita connection `LeviCivita g` acting on
the raised vector field, and the right covariant derivative is the induced cotangent connection
`cotangentCov (LeviCivita g)` acting on the covector field.

It is proved directly from the **flat**-parallelism `cotangentCov_metricDuality` (the Levi-Civita
metric compatibility read through the Riesz/♭ isomorphism, `CotangentExtension.lean`) together
with the defining inverse property `g(♯ ω, ·) = ω` (`inner_metricSharp`) and the
positive-definiteness injectivity of `♭` (`metricFlatLinear_injective`): the raise is the inverse
of the flat, so it is parallel iff the flat is.

## Main results

* `inverseMetricSharp_covDeriv_eq` — the sharp-parallelism in the canonical
  `metricSharp` / `cotangentCov` form: `∇₀(♯ ω) = ♯(∇₀ ω)`.
* `metricFlat_inverseMetricSharpField_eq` — the round-trip `♭ ∘ ♯ = id`: the flat of the raised
  field of a `Tensor0SSpace 1`-covector field `β` is the genuine cotangent functional of `β`.
* `inverseMetricSharpField_covGrad_eq_zero` — the cometric parallelism in the consumer's
  `inverseMetricSharpField` cometric form (the `∇₀`-parallelism of the inverse-metric Hom-section
  read on a covector field): the covariant derivative of the raised field equals the raise of the
  covariant derivative of the covector, `∇₀(♯ β) = ♯(∇₀ β)`.

## Non-vacuity

The statement is a genuine differential-geometric identity: it asserts that the background inverse
metric is parallel, which is **false for a non-parallel ambient frame**.  Specialised to a single
parallel field it is the per-direction reading of `∇g⁻¹ = 0`.
-/

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

/-- **The musical sharp is `∇`-parallel** (the cometric form of metric compatibility, directional,
canonical form).  For a tangent vector field `X` that is differentiable at `x` (in total-space
form), re-sharping the cotangent covariant derivative of its flat `♭X` recovers the tangent
covariant derivative of `X`:
```
♯ (∇₀_v (♭ X))  =  ∇₀_v X.
```
Equivalently, with `ω := ♭X`, this is `∇₀(♯ ω) = ♯(∇₀ ω)`.

Proved by pairing both sides against an arbitrary tangent vector through `g` and using the
flat-parallelism `cotangentCov_metricDuality` (`g(∇₀ X, ·) = (∇₀ ♭X)(·)`) together with the sharp
inverse property `g(♯ α, ·) = α(·)` (`inner_metricSharp`); the positive-definiteness injectivity
of the flat (`metricFlatLinear_injective`) then upgrades the pairing equality to the vector
equality. -/
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

/-- **The round-trip `♭ ∘ ♯ = id` at the field level.**  The metric flat of the raised field of a
realized one-covariant covector field `β` is the genuine cotangent functional `cotangentToCLM` of
`β`: `g(♯ β, ·) = β(·)`.  This is the inverse-metric defining property
`inverseMetricSharpFib_inner`, packaged as an equality of continuous cotangent functionals; it ties
the tangent-bundle flat `metricFlat` of the raised field to the cotangent realization `β` feeds
through `inverseMetricSharpField`. -/
theorem metricFlat_inverseMetricSharpField_eq (g : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    metricFlat (I := I) g (fun y : M => (inverseMetricSharpFib (I := I) g y) (β y)) b =
      cotangentToCLM (I := I) (β b) := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [metricFlat_apply]
  rw [inverseMetricSharpFib_inner (I := I) g b (β b) w]
  rfl

/-- **The inverse-metric sharp field is `∇₀`-parallel** (the cometric parallelism `∇₀ g⁻¹ = 0`, in
the `inverseMetricSharpField` cometric form the curvature trace arm consumes).  For a realized
one-covariant covector field `β` whose raised field `b ↦ ♯ β(b)` is differentiable at `x`, the
tangent covariant derivative of the raised field is the raise of the cotangent covariant derivative
of `β`:
```
∇₀_v (♯ β)  =  ♯ (∇₀_v β),
```
where the left `∇₀` is the tangent-bundle Levi-Civita connection `LeviCivita g`, the right `∇₀` is
the induced cotangent connection `cotangentCov (LeviCivita g)` acting on the cotangent realization
`b ↦ cotangentToCLM (β b)`, and `♯` is the inverse-metric raise `inverseMetricSharpFib g x` applied
through the cotangent realization `dualToCotangent`.

This is the genuine deep cometric core `∇₀ g⁻¹ = 0`: the inverse metric raises indices through the
musical sharp `♯`, which is `∇₀`-parallel because the metric is (`cotangentCov_metricDuality`); the
raise/flat round-trip `metricFlat_inverseMetricSharpField_eq` identifies `♭(♯ β) = β`, so the
sharp-parallelism `inverseMetricSharp_covDeriv_eq` applies.  It is **non-vacuous**: it asserts the
genuine identity that the background cometric is parallel (false for a non-parallel ambient
frame). -/
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
