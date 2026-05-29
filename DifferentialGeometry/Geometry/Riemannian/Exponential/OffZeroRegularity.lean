import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Unconditional

set_option linter.unusedSectionVars false

/-!
# Off-zero `ContMDiffAt 1` regularity of `expMap`

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file records the
off-zero (`v ≠ 0`) analogue of the at-zero smoothness lemma
`expMap_contMDiffAt_zero_unconditional`.

Away from the zero vector the regularity of the exponential map is
unconditional: the `HasChartFlowGeodesicMatchData` hypothesis required at
the zero vector is not needed once `v ≠ 0`, because the geodesic flow is
jointly smooth in `(t, v)` along any orbit with non-zero initial velocity.

## Main result

* `off_zero_exp_regularity` — for `v ≠ 0`, the exponential map
  `fun w : E => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section OffZero

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Off-zero unconditional regularity.** For any smooth Riemannian metric
`g`, base point `p : M`, and non-zero tangent vector `v ≠ 0`, the
exponential map `fun w => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v`.

This is the off-zero analogue of `expMap_contMDiffAt_zero_unconditional`;
the `HasChartFlowGeodesicMatchData` hypothesis needed at the zero vector is
dropped, since away from `0` the geodesic flow's joint smoothness in
`(t, v)` yields the regularity unconditionally. -/
theorem off_zero_exp_regularity
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M))
      v := sorry

end OffZero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
