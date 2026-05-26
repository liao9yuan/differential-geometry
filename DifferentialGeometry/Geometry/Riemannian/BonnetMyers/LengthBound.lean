import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.Variation.SecondVariation
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-!
# Bonnet-Myers length bound

This file packages the analytic core of the Bonnet-Myers diameter
theorem: a unit-speed minimising geodesic on a complete Riemannian
manifold whose Ricci curvature is bounded below by `(n-1) K` (with
`K > 0`) has length at most `π / √K`.

The proof routes through the second-variation index form applied to
the family `V_i(t) := sin(πt/L) · e_i(t)`, where `e_i` is a parallel
orthonormal frame of `(γ')⊥` along `γ`.
-/

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

/-! ## Trace identity: sum of sectional curvatures equals Ricci -/

/-- **trace-identity-sum-sec-curv-equals-ricci.** For a unit vector
`X ∈ T_x M` and any orthonormal family `e : Fin (Module.finrank ℝ E - 1)
→ T_x M` orthogonal to `X`,
`∑_i ⟨R(e_i, X) X, e_i⟩_g = Ric(X, X)`.

The proof realises the Ricci tensor as the trace of `Z ↦ R(Z, X) X`
in the orthonormal basis `{X, e_1, …, e_{n-1}}`; the `X`-summand
`⟨R(X, X) X, X⟩` vanishes by curvature antisymmetry. -/
theorem trace_identity_sum_sec_curv_equals_ricci
    (g : SmoothRiemannianMetric I M) (x : M) (X : E)
    (_hUnit : g.inner x X X = 1)
    (e : Fin (Module.finrank ℝ E - 1) → E)
    (_hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (_hPerp : ∀ i, g.inner x (e i) X = 0) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i))
      = ricciTensor (I := I) g x X X := sorry

/-! ## Sum-index-form frame evaluation -/

/-- **sum-index-form-frame-evaluation.** For a unit-speed geodesic
`γ : [0, L] → M`, a parallel orthonormal frame `e : Fin
(Module.finrank ℝ E - 1) → SectionAlongCurve I M γ` of `(γ')⊥`, and
the variation fields `V_i(t) := sin(πt/L) · e_i(t)`,
`∑_i indexForm g γ 0 L V_i V_i =
  ∫₀^L [(n-1)(π/L)² cos²(πt/L) - sin²(πt/L) · Ric(γ', γ')] dt`.

The proof uses parallelism of `e_i` to compute `∇_t V_i =
(π/L) cos(πt/L) · e_i`, hence `‖∇_t V_i‖² = (π/L)² cos²(πt/L)`. Summing
over `i` and applying `trace_identity_sum_sec_curv_equals_ricci`
pointwise on each `γ(t)` yields the displayed integrand. -/
theorem sum_index_form_frame_evaluation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L)
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      = ∫ t in (0 : ℝ)..L,
          ((Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)) := sorry

/-! ## Sum-index-form bound from the Ricci hypothesis -/

/-- **sum-index-form-bound-by-curvature-hypothesis.** Given the lower
Ricci bound `(n-1) K · g(v, v) ≤ Ric(v, v)` (i.e.
`RicciBoundedBelow g ((n-1) K)`), the sum of index forms on the family
`V_i(t) := sin(πt/L) · e_i(t)` is bounded above by
`(n-1)(L/2)((π/L)² - K)`.

The proof applies monotonicity of the interval integral to
`sum_index_form_frame_evaluation`, plugs in the Ricci hypothesis on
the unit speed `γ'`, and evaluates the trigonometric integrals via
`integral_sin_sq` and `integral_cos_sq`. -/
theorem sum_index_form_bound_by_curvature_hypothesis
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L) {K : ℝ}
    (_hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      ≤ (Module.finrank ℝ E - 1 : ℝ) * (L / 2) * ((Real.pi / L) ^ 2 - K) := sorry

/-! ## Length-bound contradiction assembly -/

/-- **length-bound-contradiction-assembly.** *Bonnet-Myers length
bound.* For a unit-speed minimising geodesic `γ : [0, L] → M` on a
Riemannian manifold whose Ricci curvature satisfies
`(n-1) K · g(v, v) ≤ Ric(v, v)` with `K > 0`, the length `L` is at
most `π / √K`.

The proof is by contradiction. If `π/√K < L`, then `(π/L)² < K`, so
`sum_index_form_bound_by_curvature_hypothesis` produces a strictly
negative sum of index forms. On the other hand
`minimiser_implies_second_variation_nonneg` applied to each `V_i`
gives `0 ≤ indexForm g γ 0 L V_i V_i`, hence the sum is non-negative.
This contradiction forces `L ≤ π / √K`. -/
theorem length_bound_contradiction_assembly
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L) {K : ℝ}
    (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (_hmin : ∀ η : ℝ → M, η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L) :
    L ≤ Real.pi / Real.sqrt K := sorry

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
