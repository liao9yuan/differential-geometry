import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Pullback

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- Candidate data for a standard initial metric.  Geometric assertions are kept
in separate predicates so that constructing the data does not assume the desired
standard-solution properties. -/
structure StdInit (I : ModelWithCorners Real E H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  tip : M
  metric : SmoothRiemannianMetric I M

/-- The presently expressible intrinsic core of the standard initial metric:
completeness, nonnegative sectional curvature, and curvature `1 / 4` on a
neighborhood of the tip.  The exact cylindrical-end realization is deliberately
not hidden in this predicate. -/
structure IsStdCore (A : StdInit I M) : Prop where
  complete : RiemannianMetricComplete (I := I) A.metric
  nonneg : forall x : M, forall X Y : TangentSpace I x,
    0 <= DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
      (I := I) (M := M) A.metric x X Y Y X
  roundTip : exists U : Set M, U ∈ nhds A.tip ∧
    forall x : M, x ∈ U -> forall X Y : TangentSpace I x,
      DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
          (I := I) (M := M) A.metric x X Y Y X =
        ((1 : Real) / 4) *
          (A.metric.inner x X X * A.metric.inner x Y Y -
            A.metric.inner x X Y * A.metric.inner x X Y)

/-- A supplied diffeomorphism action preserves a candidate initial metric. -/
def IsMetricInv {G : Type*} (A : StdInit I M)
    (rho : G -> M ≃ₘ⟮I, I⟯ M) : Prop :=
  forall a : G, Diffeomorph.pullbackMetric A.metric (rho a) = A.metric

namespace IsStdCore

/-- The standard core has nonnegative sectional-curvature numerator. -/
theorem nonneg_apply {A : StdInit I M} (hA : IsStdCore A)
    (x : M) (X Y : TangentSpace I x) :
    0 <= DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
      (I := I) (M := M) A.metric x X Y Y X :=
  hA.nonneg x X Y

/-- The curvature normalization in `IsStdCore` holds at the distinguished tip. -/
theorem round_at_tip {A : StdInit I M} (hA : IsStdCore A)
    (X Y : TangentSpace I A.tip) :
    DifferentialGeometry.Geometry.Curvature.metricRm04StdAt
        (I := I) (M := M) A.metric A.tip X Y Y X =
      ((1 : Real) / 4) *
        (A.metric.inner A.tip X X * A.metric.inner A.tip Y Y -
          A.metric.inner A.tip X Y * A.metric.inner A.tip X Y) := by
  obtain ⟨U, hU, hround⟩ := hA.roundTip
  exact hround A.tip (mem_of_mem_nhds hU) X Y

end IsStdCore

end DifferentialGeometry.PDE.RicciFlow
