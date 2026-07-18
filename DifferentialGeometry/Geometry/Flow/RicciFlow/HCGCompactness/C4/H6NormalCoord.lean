import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# H6 normal-coordinate metric bridges

This file connects the radial Jacobi estimates from the comparison-geometry
layer to the normal-coordinate metric package consumed by Chapter 4.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The normal-coordinate metric after precomposing the exponential
parametrization with the chosen `g_x`-orthonormal model-to-tangent frame. -/
noncomputable def framedMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let L := (normalFrame (I := I) Y.metric x).toContinuousLinearMap
  fun z =>
    (ContinuousLinearMap.precomp Real L).comp
      ((normalCoordMetric (I := I) Y x (normalFrame (I := I) Y.metric x z)).comp L)

/-- Evaluation of the orthonormally framed normal-coordinate metric. -/
theorem framedMetric_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedMetric (I := I) Y x z v w =
      normalCoordMetric (I := I) Y x (normalFrame (I := I) Y.metric x z)
        (normalFrame (I := I) Y.metric x v)
        (normalFrame (I := I) Y.metric x w) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [framedMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

/-- `framedMetric` is the actual pullback of the Riemannian metric through
`framedExpDiffeo`, not merely an algebraic reparametrization of the raw
coordinate coefficients. -/
theorem framed_metric_pull
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E)
    (hz :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      z ∈ (framedExpDiffeo (I := I) Y.metric x).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedMetric (I := I) Y x z v w =
      Y.metric.inner (framedExpDiffeo (I := I) Y.metric x z)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) Y.metric x q) z v)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) Y.metric x q) z w) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [framedMetric_apply, normalCoordMetric_apply, framedExp_apply,
    mfderiv_framedExp (I := I) Y.metric x hz]
  rfl

/-- In orthonormally framed normal coordinates, the metric at the center is
the fixed model inner product exactly. -/
theorem framedMetric_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    framedMetric (I := I) Y x 0 =
      (innerSL Real : E →L[Real] E →L[Real] Real) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext v w
  rw [framedMetric_apply]
  rw [map_zero]
  have hzero := congrArg
    (fun B : E →L[Real] E →L[Real] Real =>
      B (normalFrame (I := I) Y.metric x v)
        (normalFrame (I := I) Y.metric x w))
    (normalMetric_zero (I := I) Y x)
  calc
    normalCoordMetric (I := I) Y x 0
        (normalFrame (I := I) Y.metric x v)
        (normalFrame (I := I) Y.metric x w) =
      Y.metric.inner x (normalFrame (I := I) Y.metric x v)
        (normalFrame (I := I) Y.metric x w) := hzero
    _ = Inner.inner Real v w := normalFrame_inner (I := I) Y.metric x v w
    _ = (innerSL Real : E →L[Real] E →L[Real] Real) v w := rfl

/-- The pulled-back normal-coordinate metric is the endpoint Gram form of the
radial Jacobi fields generated by its two vector arguments. -/
theorem metric_eq_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    z ∈ (expMapDiffeo (I := I) Y.metric x).source →
    ‖z‖ < expMapC2Radius (I := I) Y.metric x →
    normalCoordMetric (I := I) Y x z v w =
      Y.metric.inner
        (expMap (I := I) Y.metric x (show TangentSpace I x from z))
        (radialJacobiField (I := I) Y.metric x z v 1)
        (radialJacobiField (I := I) Y.metric x z w 1) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hz hzC2
  have hev : expMapDiffeo (I := I) Y.metric x =ᶠ[nhds z]
      (fun q : E => (expMap (I := I) Y.metric x
        (show TangentSpace I x from q) : Y.M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hz) ?_
    intro q hq
    exact expMapDiffeo_apply_eq (I := I) Y.metric x hq
  rw [normalCoordMetric_apply (I := I),
    expMapDiffeo_apply_eq (I := I) Y.metric x hz, hev.mfderiv_eq]
  rw [radialJacobi_one (I := I) Y.metric x z v hzC2,
    radialJacobi_one (I := I) Y.metric x z w hzC2]

/-- In orthonormally framed normal coordinates, the pulled-back metric is the
endpoint Gram form of the radial Jacobi fields launched through the same
frame. -/
theorem framed_metric_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ‖z‖ < expRadiusGp (I := I) Y.metric x →
    framedMetric (I := I) Y x z v w =
      Y.metric.inner
        (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
        (radialJacobiField (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z)
          (normalFrame (I := I) Y.metric x v) 1)
        (radialJacobiField (I := I) Y.metric x
          (normalFrame (I := I) Y.metric x z)
          (normalFrame (I := I) Y.metric x w) 1) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hz
  have hsrc := framedExp_mem_of_lt (I := I) Y.metric x hz
  have hzC2 : ‖normalFrame (I := I) Y.metric x z‖ <
      expMapC2Radius (I := I) Y.metric x := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric x
    simpa only [normalFrame_sqrt] using hz
  rw [framedMetric_apply]
  exact metric_eq_jacobi (I := I) Y x
    (normalFrame (I := I) Y.metric x z)
    (normalFrame (I := I) Y.metric x v)
    (normalFrame (I := I) Y.metric x w)
    (by simpa only [framedExp_source] using hsrc) hzC2

/-- Jacobi endpoint comparison in a `g_x`-orthonormal frame gives the genuine
Euclidean half/two estimate for the framed normal-coordinate metric. -/
theorem framed_equiv_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (∀ z ∈ U, ‖z‖ < expRadiusGp (I := I) Y.metric x) →
    (∀ z ∈ U, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ∧
        Y.metric.inner
          (expMap (I := I) Y.metric x (normalFrame (I := I) Y.metric x z))
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1)
          (radialJacobiField (I := I) Y.metric x
            (normalFrame (I := I) Y.metric x z)
            (normalFrame (I := I) Y.metric x v) 1) ≤
              2 * ‖v‖ ^ 2) →
    ∀ z ∈ U, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ framedMetric (I := I) Y x z v v ∧
        framedMetric (I := I) Y x z v v ≤ 2 * ‖v‖ ^ 2 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hsmall hJ z hz v
  rw [framed_metric_jacobi (I := I) Y x z v v (hsmall z hz)]
  exact hJ z hz v

/-- Raw-coordinate Jacobi endpoint bounds imply the legacy Chapter-4 metric
equivalence predicate.  This conditional adapter does not provide the native
H6 producer: genuine normal coordinates use `framed_equiv_jacobi`. -/
theorem equiv_of_jacobi
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    U ⊆ (expMapDiffeo (I := I) Y.metric x).source →
    (∀ z ∈ U, ‖z‖ < expMapC2Radius (I := I) Y.metric x) →
    (∀ z ∈ U, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
        Y.metric.inner
          (expMap (I := I) Y.metric x (show TangentSpace I x from z))
          (radialJacobiField (I := I) Y.metric x z v 1)
          (radialJacobiField (I := I) Y.metric x z v 1) ∧
        Y.metric.inner
          (expMap (I := I) Y.metric x (show TangentSpace I x from z))
          (radialJacobiField (I := I) Y.metric x z v 1)
          (radialJacobiField (I := I) Y.metric x z v 1) ≤
            2 * ‖v‖ ^ 2) →
    NormalCoordMetricEquivOn (I := I) Y x U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro hsrc hC2 hJ z hz v
  rw [metric_eq_jacobi (I := I) Y x z v v (hsrc hz) (hC2 z hz)]
  exact hJ z hz v

end HCGCompactness
end DifferentialGeometry
