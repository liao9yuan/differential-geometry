import DifferentialGeometry.Geometry.Riemannian.Exponential.Unconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.UniformExistence
import DifferentialGeometry.Geometry.Riemannian.Exponential.UniformUniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalRescaling

set_option linter.unusedSectionVars false

/-!
# Final assembly: closing the headline

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the exponential map
`expMap g p : T_p M → M` is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero
vector.

The conditional headline
`expMap_contMDiffAt_zero_unconditional` consumes the data predicate
`HasChartFlowGeodesicMatchData g p`, which captures the manifold-side
identification of the exponential map against a V.4 chart-pushed flow's
projection. This file lays out the final-assembly pipeline that, given:

* the uniform chart-coord existence interval from
  `Exponential/UniformExistence.lean` (V.4-compatible flow `Φ` with
  uniform spatial radius `ρ` and time horizon `T`, plus per-`v`
  manifold lift `f_v`),
* the uniform chart-coord ODE uniqueness on `Ioo (-T') T'` for compact
  spatial sets from `Exponential/UniformUniqueness.lean`,
* the manifold-level rescaling of `maximalGeodesic` at time `1` from
  `Geodesic/MaximalRescaling.lean`,

would discharge `HasChartFlowGeodesicMatchData` unconditionally and
thereby close `expMap_contMDiffAt_zero_truly_unconditional`.

## Closure pipeline (mathematical content)

Let `(Φ, ρ, T)` be supplied by `exists_uniform_existence_interval`. For
every `v ∈ Metric.ball (0 : E) ρ`, the chart-flow orbit
`s ↦ Φ ((x₀, v), s)` satisfies the genuine chart-phase ODE on
`Ioo (-T) T`, and there is a manifold-side lift
`f_v : ℝ → TangentBundle I M` with `f_v 0 = ⟨p, v⟩` and an eventually-
near-`0` identification of the orbit's projection with `(f_v ·).proj`.

The final pieces required to discharge `HasChartFlowGeodesicMatchData`:

1. **Manifold-side lift extension on the uniform interval.** The chart-
   flow orbit `Φ ((x₀, v), ·)` extends to a `TangentBundle I M`-valued
   integral curve `F_v` of `geodesicVectorFieldChart g p` on the entire
   `Ioo (-T) T`, constructed by inverting the chart trivialisation at
   `p` against the orbit's chart-coord coordinates. `F_v` automatically
   has `F_v 0 = ⟨p, v⟩` (matching `f_v` at `0`) and, by chart-coord
   ODE uniqueness on `Ioo (-T) T`, projects to the same manifold curve
   as `f_v` near `0`. By Mathlib's `IsMIntegralCurveAt` uniqueness
   propagation, `F_v = f_v` on a maximal connected open subset of
   `Ioo (-T) T`; we need the full interval, which uses preconnected
   propagation in `Ioo (-T) T`.

2. **Identification with `maximalGeodesicChosenCurve`.** The witness
   `(projectCurve F_v, Ioo (-T) T)` together with the integral-curve
   property gives `Ioo (-T) T ⊆ maximalGeodesicInterval g p v`. The
   chosen curve `maximalGeodesicChosenCurve g p v` agrees with
   `projectCurve F_v` on a neighbourhood of `0` by Layer 1 uniqueness;
   uniqueness propagates across the preconnected `Ioo (-T) T` to give
   full agreement on the interval.

3. **Apply rescaling at `t' = 1/N` for `N` large.** Pick `t' > 0` small
   enough that `t' ∈ Ioo (-T) T` and the rescaled image
   `t' • Metric.ball 0 ρ` falls inside a smaller ball where the lift
   for `t' • v` exists on a time interval containing `1`. The
   `maximalGeodesic_rescale_at_one` of `Geodesic/MaximalRescaling.lean`
   then gives, when its smallness hypothesis (chart-coord agreement at
   `s = 1`) is discharged:
   `maximalGeodesic g p (t' • v) 1 = maximalGeodesic g p v t'`.

4. **Combine.** The right-hand side equals `(F_v t').proj`, which equals
   `(extChartAt I p).symm (Φ ((x₀, v), t')).1 = chartFlowCandidate Φ p t' v`.
   Hence `expMap g p (t' • v) = chartFlowCandidate Φ p t' v` for every
   `v ∈ Metric.ball (0 : E) ρ`, which is `ChartFlowGeodesicMatchAt g p Φ t' ρ`.

## Status of the final assembly

The four steps above together discharge `HasChartFlowGeodesicMatchData`
unconditionally. Steps (1) (manifold-side lift extension) and (2)
(uniform preconnected propagation of uniqueness against
`maximalGeodesicChosenCurve`) require substantial new infrastructure
beyond R.A/R.B/R.C — specifically, the construction of a `TangentBundle
I M`-valued curve from a chart-coordinate `E × E`-valued orbit via
inverse chart trivialisation, plus the verification that this curve is
a `IsMIntegralCurveOn` of `geodesicVectorFieldChart g p` on the entire
`Ioo (-T) T`. Step (3) requires discharging the smallness hypothesis
`h1_in_agreement` of `maximalGeodesic_rescale_at_one`, which in turn
uses the full-interval chart-coord agreement established in step (2)
applied uniformly across both `(p, v)`-orbits and `(p, t' • v)`-orbits.

Each of these pieces is mathematically sound; together they exceed the
500-line scope of a single substep. The infrastructure naturally divides
into:

* `Exponential/ChartFlowToTangentLift.lean` — manifold lift `F_v`
  construction from the chart-flow's first and second components via
  the trivialisation at `p`, plus its `IsMIntegralCurveOn` property on
  `Ioo (-T) T`;

* `Exponential/UniformChartCoordUniquenessOnIoo.lean` — chart-coord
  uniqueness identifying `chartPushLift f_v 0` with the chart-flow
  orbit on `Ioo (-T) T` (uniformly in `v`), specialised to the witness
  curves of `maximalGeodesicChosenCurve` (uniformly in `v`);

* `Exponential/RescaleSmallnessUniform.lean` — uniform-in-`v` discharge
  of the smallness hypothesis of `maximalGeodesic_rescale_at_one`,
  reducing it to the uniform chart-coord agreement on `Ioo (-T) T`.

This file packages the conditional headline of `Unconditional.lean`
under its public name. The unconditional theorem name is reserved for
the final closure once the three additional pieces above are
delivered.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Public final-assembly endpoint

The headline takes the form of the conditional theorem from
`Unconditional.lean`. It is re-stated here for documentation, under
the name reserved for the final unconditional endpoint. -/

section FinalEndpoint

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Final assembly endpoint, conditional form.** For a smooth
Riemannian metric `g` and a base point `p : M` on a boundaryless smooth
manifold modelled on a complete inner-product space, the exponential
map `expMap g p` is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero vector,
conditional on the named manifold-side identification predicate
`HasChartFlowGeodesicMatchData g p`. The unconditional discharge of
this predicate reduces, via R.A/R.B/R.C of this directory, to the
three pieces of additional infrastructure listed in the module
docstring above. -/
theorem expMap_contMDiffAt_zero_final
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : HasChartFlowGeodesicMatchData (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_unconditional (I := I) g p h

end FinalEndpoint

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
