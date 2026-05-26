import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Curvature.Riemann
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Fixed-chart variation identities

For a smooth two-parameter map `f : ℝ × ℝ → M`, with the basepoint of the
chart-local covariant derivative held at `f s t`, the mixed covariant
derivatives along the parameter directions commute (torsion-freeness) and
their commutator on a vector field `Y` along `f` equals the Riemann
curvature operator applied to `∂_s f`, `∂_t f`, `Y`.

Statements only — proofs are deferred.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

/-! ## Smooth two-parameter variation -/

/-- A smooth two-parameter variation `f : ℝ → ℝ → M` is one whose
uncurried map `ℝ × ℝ → M` is jointly smooth. Since neither factor is a
manifold of positive geometric dimension carrying the project's
geometric structures, joint smoothness on `ℝ × ℝ` is admissible here. -/
def IsSmoothVariation
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : ℝ → ℝ → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ (fun p : ℝ × ℝ => f p.1 p.2)

/-! ## Commutation of mixed covariant derivatives (fixed chart) -/

/-- Fixed-chart variant of `commute_ds_dt`: the chart-local covariant
derivatives along the parameter directions of a smooth variation
commute when the chart basepoint is taken to be `f s t`. -/
theorem commute_ds_dt_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f u v) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) s (1 : ℝ)) t := sorry

/-! ## Curvature identity on a variation (fixed chart) -/

/-- Fixed-chart variant of `curvature_identity_on_variation`: for a
vector field `Y` along a smooth two-parameter variation `f`, the
commutator of `∇_s` and `∇_t` taken with the chart basepoint pinned to
`f s t` equals the Riemann curvature operator applied to
`∂_s f`, `∂_t f`, and `Y`. -/
theorem curvature_identity_on_variation_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (Y : ℝ → ℝ → E) (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t) (fun u : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f u v)
          (fun v : ℝ => Y u v) t) s
      - chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v) (fun v : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u v)
          (fun u : ℝ => Y u v) s) t
    = (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (f s t))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) s (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f s v) t (1 : ℝ))
        (Y s t) := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
