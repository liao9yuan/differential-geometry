import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Seam
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Metric.PullbackCross

/-!
# Metric matching across a surgery seam

This file adds the metric predicate for a smooth surgery seam.  It remains a
property of separately supplied metrics; metric data is not duplicated inside
`SurgerySeam`.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

variable {Eold : Type*} [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
  [FiniteDimensional ℝ Eold]
variable {Hold : Type*} [TopologicalSpace Hold]
variable {Iold : ModelWithCorners ℝ Eold Hold}
variable {Mold : Type*} [TopologicalSpace Mold] [ChartedSpace Hold Mold]
  [IsManifold Iold ∞ Mold] [SigmaCompactSpace Mold] [T2Space Mold]
variable {Enew : Type*} [NormedAddCommGroup Enew] [NormedSpace ℝ Enew]
  [FiniteDimensional ℝ Enew]
variable {Hnew : Type*} [TopologicalSpace Hnew]
variable {Inew : ModelWithCorners ℝ Enew Hnew}
variable {Mnew : Type*} [TopologicalSpace Mnew] [ChartedSpace Hnew Mnew]
  [IsManifold Inew ∞ Mnew] [SigmaCompactSpace Mnew] [T2Space Mnew]

/-- The event identification matches the old and new metrics on every retained
point.  Equivalently, the pullback of the new metric equals the old metric
pointwise on `S.keep`; no equality is required on the discarded part of the
open event neighborhood. -/
def IsMetricSeam
    (S : SurgerySeam Iold Mold Inew Mnew)
    (gold : SmoothRiemannianMetric Iold Mold)
    (gnew : SmoothRiemannianMetric Inew Mnew) : Prop :=
  ∀ x : S.oldOpen, x ∈ S.keep →
    (Diffeomorph.pullbackMetricCross
      (gnew.restrictOpen (I := Inew) S.newOpen) S.identify).inner x =
      (gold.restrictOpen (I := Iold) S.oldOpen).inner x

namespace IsMetricSeam

/-- Pointwise evaluation of metric matching on two tangent vectors. -/
theorem inner
    {S : SurgerySeam Iold Mold Inew Mnew}
    {gold : SmoothRiemannianMetric Iold Mold}
    {gnew : SmoothRiemannianMetric Inew Mnew}
    (h : IsMetricSeam S gold gnew)
    {x : S.oldOpen} (hx : x ∈ S.keep) (v w : TangentSpace Iold x) :
    gold.inner (x : Mold) v w =
      gnew.inner (S.identify x : Mnew)
        (mfderiv Iold Inew S.identify x v)
        (mfderiv Iold Inew S.identify x w) := by
  have hxy := congrArg (fun B => B v w) (h x hx)
  simpa only [Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner] using hxy.symm

end IsMetricSeam

/-- Equality of the metrics on the whole old event neighborhood implies metric
matching on any chosen retained region. -/
theorem metricSeam_of_eq
    (S : SurgerySeam Iold Mold Inew Mnew)
    (gold : SmoothRiemannianMetric Iold Mold)
    (gnew : SmoothRiemannianMetric Inew Mnew)
    (hEq : Diffeomorph.pullbackMetricCross
        (gnew.restrictOpen (I := Inew) S.newOpen) S.identify =
      gold.restrictOpen (I := Iold) S.oldOpen) :
    IsMetricSeam S gold gnew := by
  intro x _hx
  exact congrArg (fun g : SmoothRiemannianMetric Iold S.oldOpen => g.inner x) hEq

end DifferentialGeometry.PDE.RicciFlow.Surgery
