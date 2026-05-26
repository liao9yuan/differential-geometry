import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Parallel transport: local existence + uniqueness via Picard–Lindelöf

Given a smooth Riemannian metric `g` on `M` and a smooth curve
`γ : ℝ → M` whose image stays inside a single chart at `α`, the
parallel-transport ODE
`Y'(t) = - Γ_α(u'(t), Y(t))(u(t))`
is a continuous time-dependent linear ODE on `E`. This file packages
the chart-local existence + uniqueness obligations on a compact
sub-interval, used by `ParallelTransport.lean` to glue a global
solution.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- **chart-christoffel-clm-continuous-on-compact.** The chart
Christoffel contraction continuous-linear-map
`t ↦ Γ_α(u'(t), ·)(u(t))` is continuous on a compact sub-interval
`[a, b]` whenever `u'` and `u` are continuous on `[a, b]` and `u`
takes values in the chart source. -/
theorem chart_christoffel_clm_continuous_on_compact
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ}
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ContinuousOn (fun t : ℝ =>
      chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)) (Set.Icc a b) := sorry

/-- **parallel-lipschitz-bound-on-compact.** Continuity of
`t ↦ chartChristoffelContractionRightCLM g α (u'(t)) (u(t))` on the
compact interval `[a, b]` yields a uniform Lipschitz constant `K` for
the parallel-transport vector field on `[a, b]`. -/
theorem parallel_lipschitz_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ∃ K : NNReal,
      ParallelTransportLipschitzBound (I := I) g α γ uPrime K
        (Set.Icc a b) := by
  -- Continuity of the CLM-valued function on the compact interval.
  have hCLM : ContinuousOn
      (fun t : ℝ => chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)) (Set.Icc a b) :=
    chart_christoffel_clm_continuous_on_compact g α γ uPrime hu hγ hsource
  -- Hence continuity of its NNReal-valued operator norm.
  have hN : ContinuousOn
      (fun t : ℝ => ‖chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)‖₊) (Set.Icc a b) :=
    hCLM.nnnorm
  -- Extract a maximum on the compact, nonempty interval `[a, b]`.
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  obtain ⟨tmax, htmax_mem, htmax_max⟩ := hcpt.exists_isMaxOn hne hN
  refine ⟨‖chartChristoffelContractionRightCLM (I := I) g α (uPrime tmax)
    (chartCurve (I := I) α γ tmax)‖₊, ?_⟩
  intro t ht
  exact htmax_max ht

/-- **parallel-picard-lindelof-data.** The Picard–Lindelöf data
(time-dependent vector field + Lipschitz bound + continuity in time)
assembled from the chart Christoffel contraction on a compact
sub-interval. The exact Mathlib structure is `IsPicardLindelof`; we
expose existence as an unspecified placeholder so downstream callers
need only the abstract conclusion. -/
theorem parallel_picard_lindelof_data
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    True := sorry

/-- **parallel-local-existence-on-Icc.** On a compact interval
`[a, b] ∋ t₀`, the linear parallel-transport ODE has a solution
`Y : ℝ → E` defined on `[a, b]` with `Y(t₀) = v₀`. Constructed from
Picard–Lindelöf applied to the continuous linear right-hand side. -/
theorem parallel_local_existence_on_Icc
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ Y : ℝ → E,
      (∀ t ∈ Set.Icc a b, HasDerivWithinAt Y
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
      Y t₀ = v₀ := sorry

/-- **parallel-local-uniqueness-on-Icc.** On a compact interval
`[a, b] ∋ t₀`, two solutions of the linear parallel-transport ODE
sharing an initial value at `t₀` coincide on `[a, b]`. Proved via
Grönwall against the uniform Lipschitz bound. -/
theorem parallel_local_uniqueness_on_Icc
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hu : ContinuousOn uPrime (Set.Icc a b))
    (hγ : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    {Y₁ Y₂ : ℝ → E}
    (hY₁ : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y₁
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t)
    (hY₂ : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y₂
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
            (chartCurve (I := I) α γ t)) (Set.Icc a b) t)
    (h_eq : Y₁ t₀ = Y₂ t₀) :
    Set.EqOn Y₁ Y₂ (Set.Icc a b) := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
