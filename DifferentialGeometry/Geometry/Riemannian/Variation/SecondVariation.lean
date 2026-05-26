import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Connection.Ricci
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option linter.unusedSectionVars false

/-!
# Arc length, first and second variation of length, index form

This file packages the analytic content of the second variation of
arc length along a smooth two-parameter variation `f : ℝ × ℝ → M`:

* `arcLength g η a b` — the real-valued arc length of a curve `η`
  on a closed interval `[a, b]`;
* speed positivity on a regular variation;
* commutation of mixed covariant derivatives along a smooth
  two-parameter map (Schwarz / torsion-freeness);
* the Riemann-curvature identity on a variation;
* the first and second variation formulas;
* the index form `indexForm g γ a b V W`;
* the consequence that, along a minimising geodesic with endpoint-fixed
  smooth variation field, the index form is non-negative.

Statements only — proofs are deferred.
-/

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
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
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Arc length functional -/

/-- Real-valued arc length of a curve `η : ℝ → M` on `[a, b]` against
the smooth Riemannian metric `g`. The integrand is the speed
`‖η'(t)‖_g = √ g.inner (η t) (η'(t)) (η'(t))`. -/
def arcLength (g : SmoothRiemannianMetric I M) (η : ℝ → M) (a b : ℝ) : ℝ := by
  classical
  exact (sorry : ℝ)

/-! ## Speed positivity on a regular variation -/

/-- On a small neighbourhood of `s = 0`, the speed `‖∂_t f(s, t)‖_g`
of a regular smooth variation `f` whose central curve is unit-speed
admits a uniform positive lower bound on `[0, L]`. -/
theorem speed_positivity_on_regular_variation
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ) :
    ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∀ s ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc 0 L,
      c ≤ Real.sqrt
        (g.inner (f s t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))) := sorry

/-! ## Commutation of mixed covariant derivatives -/

/-- For a smooth two-parameter map `f : ℝ × ℝ → M`, the mixed
covariant derivatives along the parameter directions commute:
`∇_s ∂_t f = ∇_t ∂_s f`. -/
theorem commute_ds_dt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (α : M) (s t : ℝ) :
    chartCovDerivAlong (I := I) g α (fun u : ℝ => f u t)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f s v) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g α (fun v : ℝ => f s v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) s (1 : ℝ)) t := sorry

/-! ## Curvature identity on a variation -/

/-- For a vector field `Y` along a smooth two-parameter map `f`, the
commutator of `∇_s` and `∇_t` is given by the Riemann curvature
operator: `(∇_s ∇_t - ∇_t ∇_s) Y = R(∂_s f, ∂_t f) Y`. -/
theorem curvature_identity_on_variation
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E)
    (α : M) (s t : ℝ) :
    chartCovDerivAlong (I := I) g α (fun u : ℝ => f u t) (fun u : ℝ =>
        chartCovDerivAlong (I := I) g α (fun v : ℝ => f u v)
          (fun v : ℝ => Y u v) t) s
      - chartCovDerivAlong (I := I) g α (fun v : ℝ => f s v) (fun v : ℝ =>
        chartCovDerivAlong (I := I) g α (fun u : ℝ => f u v)
          (fun u : ℝ => Y u v) s) t
    = (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (f s t))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) s (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f s v) t (1 : ℝ))
        (Y s t) := sorry

/-! ## First variation of arc length -/

/-- The first variation of arc length: for a smooth endpoint-fixed
variation `f` of a unit-speed curve `γ := f 0`, the derivative of
`s ↦ arcLength g (f s ·) 0 L` at `s = 0` equals minus the integral
of `⟨V, ∇_t γ'⟩_g`, where `V := ∂_s f|_{s = 0}` is the variation
field. (The boundary contribution vanishes for endpoint-fixed
variations and is omitted.) -/
theorem first_variation_formula
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      (- ∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          ((chartCovDerivAlong (I := I) (M := M) g (f 0 t) (fun v : ℝ => f 0 v)
            (fun v : ℝ =>
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t : E))) 0 := sorry

/-! ## First variation vanishes along a geodesic -/

/-- For a unit-speed geodesic `γ` and any endpoint-fixed smooth
variation `f` whose central curve is `γ`, the first variation of
arc length at `s = 0` vanishes. -/
theorem first_variation_vanishes_for_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (_hγ : IsGeodesic (I := I) g γ) (_hf : ∀ t : ℝ, f 0 t = γ t) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      0 0 := sorry

/-! ## Index form -/

/-- The second-variation **index form** of a smooth curve `γ : ℝ → M`
on the interval `[a, b]`, evaluated on two sections `V, W : ℝ → E`
along `γ`:
`I_γ(V, W) := ∫_a^b (⟨∇_t V, ∇_t W⟩_g - ⟨R(V, γ') γ', W⟩_g) dt`. -/
def indexForm (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) (V W : ℝ → E) : ℝ := by
  classical
  exact (sorry : ℝ)

/-! ## Second variation derivation -/

/-- The **second variation of arc length** for a unit-speed geodesic
`γ` and an endpoint-fixed smooth variation `f` of `γ` with variation
field `V := ∂_s f|_{s = 0}`:
`d²/ds²|_{s = 0} arcLength g (f s ·) 0 L = indexForm g γ 0 L V V`. -/
theorem second_variation_derivation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (V : ℝ → E)
    (_hγ : IsGeodesic (I := I) g γ) (_hf : ∀ t : ℝ, f 0 t = γ t)
    (_hV : ∀ t : ℝ, V t = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ)) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L) s)
      (indexForm (I := I) g γ 0 L V V) 0 := sorry

/-! ## Minimiser implies index form is non-negative -/

/-- A length-minimising unit-speed geodesic `γ : [0, L] → M` realises
a local minimum of arc length on endpoint-fixed smooth variations;
consequently the index form is non-negative on every endpoint-fixed
smooth variation field `V`. -/
theorem minimiser_implies_second_variation_nonneg
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (L : ℝ) (V : ℝ → E)
    (_hγ : IsGeodesic (I := I) g γ)
    (_hmin : ∀ η : ℝ → M, η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (_hV0 : V 0 = 0) (_hVL : V L = 0) :
    0 ≤ indexForm (I := I) g γ 0 L V V := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
