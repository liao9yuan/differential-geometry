import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.FlowC1Continuous
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

/-!
# Chain-of-charts continuity of the exponential map

This file collects the six chained-flow continuity steps used to deduce
`Continuous (expMap g p)` on a geodesically complete Riemannian manifold:
compactness of the geodesic segment `γ([0, 1])`, a finite chart-cover
partition via the Lebesgue-number lemma, per-chart joint-`C¹` local flows
from Picard–Lindelöf, continuity at chart junctions via the local-flow
group-property gluing, and the final continuity statement obtained by
specialising the joint flow to `t = 1`.

The detailed Lean types of the intermediate joint-flow predicates are
deferred to the proof phase; here we expose only the propositional
shells required to record the chain. The headline statement is
`bm_c_expMap_continuity_from_jointFlow`, whose signature is
`Continuous (expMap g p)`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

/-! ## 1. Compactness of the geodesic segment image -/

/-- The image of `[0, 1]` under `maximalGeodesic g p v₀` is a compact
subset of `M`. -/
theorem bm_c_expMap_geodesicSegment_compactImage
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    IsCompact (maximalGeodesic (I := I) g p v₀ '' Set.Icc (0 : ℝ) 1) := by
  -- Continuous image of a compact set is compact. The unit interval
  -- `[0, 1]` is compact (`isCompact_Icc`); the maximal geodesic curve is
  -- continuous on `[0, 1]` because, under geodesic completeness, every
  -- point of `[0, 1]` lies in the maximal interval and is covered by a
  -- chosen-curve witness which is itself continuous (as the projection
  -- of an integral curve). The agreement of `maximalGeodesic` with the
  -- local witness on a neighbourhood is the cross-basepoint coincidence
  -- step; we package the continuity as the deferred sub-statement.
  have h_cont :
      ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
    sorry
  exact isCompact_Icc.image_of_continuousOn h_cont

/-! ## 2. Finite chart-cover via the Lebesgue-number lemma -/

/-- Existence of a chart-cover partition of the unit interval along the
geodesic `maximalGeodesic g p v₀`: a `True`-shelled propositional shell
recording the witness `(n, t, idx)` produced by the Lebesgue-number
lemma. The detailed type is deferred. -/
theorem bm_c_expMap_finite_chartCover
    (_g : SmoothRiemannianMetric I M) (_p : M) (_v₀ : TangentSpace I _p) :
    True := by
  trivial

/-! ## 3. Per-chart joint-`C¹` local flow (Picard–Lindelöf) -/

/-- Per-chart Picard–Lindelöf local flow with joint-`C¹` regularity on a
product `ball × Ioo (-T) T`. The detailed type is deferred. -/
theorem bm_c_expMap_perChart_jointFlow
    (_g : SmoothRiemannianMetric I M) (_q : M) :
    True := by
  trivial

/-! ## 4. Continuity at a chart junction -/

/-- The composition of two adjacent chart flows is continuous in the
initial datum, and its projection to the tangent bundle is an integral
curve of the next chart's geodesic vector field near the junction time.
The detailed type is deferred. -/
theorem bm_c_expMap_chartJunction_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    True := by
  sorry

/-! ## 5. Joint continuity of the chained flow on a ball × `[0, 1]` -/

/-- For every initial velocity `v₀` there exists a radius `ρ > 0` such
that the chained flow `(v, t) ↦ maximalGeodesic g p v t` is jointly
continuous on `Metric.ball v₀ ρ × Set.Icc 0 1`. -/
theorem bm_c_expMap_chainedFlow_joint_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          maximalGeodesic (I := I) g p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

/-! ## 6. Continuity of `expMap g p` -/

/-- The exponential map `expMap g p` is continuous on `T_p M`. -/
theorem bm_c_expMap_continuity_from_jointFlow
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  sorry

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
