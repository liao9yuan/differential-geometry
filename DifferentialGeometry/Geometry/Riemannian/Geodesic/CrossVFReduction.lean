import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.GeodesicEquationBridge
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

set_option linter.unusedSectionVars false

/-!
# Cross-chart-basepoint reduction for the geodesic vector field

This file packages the cross-VF reduction bridge: an integral curve of the
chart-fixed geodesic vector field at one basepoint `α` is, on the overlap of
chart sources, also an integral curve of the chart-fixed geodesic vector field
at a different basepoint `α'`. Combined with chart-fixed Picard–Lindelöf
existence and uniqueness, this yields the unconditional
`IsGeodesicAt → HasGeodesicEquationAt` bridge.
-/

noncomputable section

open Bundle Manifold Set Filter
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

/-- **Cross-basepoint coincidence of the chart-fixed geodesic vector field on
integral curves.** A curve which is a local integral curve at `t₀` of the
chart-fixed geodesic vector field at one basepoint `α` is also a local
integral curve at `t₀` of the chart-fixed geodesic vector field at a
different basepoint `α'`, provided the projection of the curve at `t₀` lies
in both chart sources. -/
theorem bm_c_gc_vf_chart_coincidence
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hα : (f t₀).proj ∈ (chartAt H α).source)
    (hα' : (f t₀).proj ∈ (chartAt H α').source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α') t₀ := sorry

/-- **Cross-VF projection-uniqueness for `IsGeodesicAt`.** From an
`IsGeodesicAt`-witness `(α, f)` of `γ` at `t₀`, construct a
chart-`γ(t₀)`-centred local integral curve `f₁` of the chart-fixed geodesic
vector field at `γ(t₀)` whose projection agrees with `γ` on a neighbourhood
of `t₀`. -/
theorem bm_c_gc_cross_vf_projection_uniqueness
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t₀).proj = γ t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ ∧
      γ =ᶠ[𝓝 t₀] (fun t => (f₁ t).proj) := sorry

/-- **Unconditional bridge `IsGeodesicAt → HasGeodesicEquationAt`.** A local
geodesic at `t₀` satisfies the chart-coordinate second-derivative form of the
geodesic equation at `t₀`. -/
theorem IsGeodesicAt.hasGeodesicEquationAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f₁, hf₁_proj_t₀, hf₁, hcross⟩ :=
    bm_c_gc_cross_vf_projection_uniqueness (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ
  exact IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ (f₁ := f₁) hf₁ hf₁_proj_t₀ hcross

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
