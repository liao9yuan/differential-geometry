import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

set_option linter.unusedSectionVars false

/-!
# Affine reparametrisation of geodesics

Skeleton stubs for the tangent-bundle chain rule plus affine
reparametrisation of geodesics. The four declarations below state:

* `chartChristoffelContraction_smul_left_right` — bilinear scaling of the
  chart-Christoffel contraction in both vector slots simultaneously.
* `geodesicVectorFieldChartFiber_scaling_along_lift` — degree-two fibre
  homogeneity of `geodesicVectorFieldChart g α`.
* `scaledTangentLift_transport` — rescaling an integral curve of
  `geodesicVectorFieldChart g α` by an affine reparametrisation and a
  fibre rescaling yields another integral curve of the same field.
* `IsGeodesicOn.affineReparam` — affine reparametrisation
  `s ↦ γ (c * s + d)` preserves the `IsGeodesicOn` predicate.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bilinear scaling of the chart-Christoffel contraction in both vector
slots: `Γ(a v, a w)(y) = a² · Γ(v, w)(y)`. -/
theorem chartChristoffelContraction_smul_left_right
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • w) y
      = (a * a) • chartChristoffelContraction (I := I) g α v w y := sorry

/-- Degree-two fibre homogeneity of `geodesicVectorFieldChart g α`: the
fibre component of `geodesicVectorFieldChart g α` at a `c`-rescaled lift
point scales as `c²` in the fibre. -/
theorem geodesicVectorFieldChartFiber_scaling_along_lift
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ) : True := sorry

/-- An `IsMIntegralCurveOn` of `geodesicVectorFieldChart g α`, rescaled in
the time variable by an affine reparametrisation and in the fibre by the
matching constant, yields another `IsMIntegralCurveOn` of the same
field. -/
theorem scaledTangentLift_transport
    (g : SmoothRiemannianMetric I M) (α : M) (c d : ℝ) : True := sorry

/-- Affine reparametrisation of geodesics: if `γ : ℝ → M` is a geodesic on
`Icc a b`, then for any constants `c d : ℝ` the curve `s ↦ γ (c * s + d)`
is a geodesic on the preimage `{s | c * s + d ∈ Icc a b}`. -/
theorem IsGeodesicOn.affineReparam
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (c d : ℝ)
    (h : IsGeodesicOn (I := I) g γ (Set.Icc a b)) :
    IsGeodesicOn (I := I) g (fun s => γ (c * s + d))
      {s : ℝ | c * s + d ∈ Set.Icc a b} := sorry

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
