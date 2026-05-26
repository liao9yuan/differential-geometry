import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Parallel transport along a smooth curve

Given a smooth Riemannian metric `g` on `M` and a smooth curve `γ : ℝ → M`,
this file packages the global parallel-transport theory:

* the chart-local linear-ODE reduction of `∇_{γ'} V = 0`;
* local existence + uniqueness from the linear Picard-Lindelöf bound;
* chart-overlap consistency of solutions;
* extension of the unique solution to all of `ℝ`;
* the bundled `parallelTransport` section, with simp lemmas for its
  initial value and its parallelism in every chart;
* preservation of the inner product `⟨V, W⟩_g` along the curve;
* existence of a parallel orthonormal frame of `(γ')⊥` along a
  unit-speed geodesic.
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
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-! ## Chart-local ODE form of `∇_{γ'} V = 0`

The chart-local covariant derivative along `γ` is `D V / dt = V'(t) +
Γ_α(u'(t), V(t))(u(t))`, so the parallel-transport equation
`∇_{γ'} V = 0` is the linear ODE `dV/dt = -Γ(γ(t))[γ'(t)] · V`. This
node records the explicit linear-ODE shape that downstream
Picard-Lindelöf / Gronwall arguments consume. -/

/-- **parallel-ode-chart-local.** The parallel-transport condition
`(D V / dt)(t) = 0` in the chart at `α` is equivalent to the linear
ODE `V'(t) = - Γ_α(u'(t), V(t))(u(t))`. -/
theorem parallel_ode_chart_local
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) :
    IsParallelChart (I := I) g α γ uPrime Y s ↔
      (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
        (∀ t ∈ s, HasDerivAt Y
          (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t)) t) := by
  unfold IsParallelChart IsCovDerivAlongChart
  refine Iff.and Iff.rfl ?_
  refine forall_congr' (fun t => ?_)
  refine imp_congr_right (fun _ => ?_)
  -- `(fun _ => 0) t - X = -X`
  simp [zero_sub]

/-! ## Local existence + uniqueness on a compact interval

A continuous time-dependent linear vector field on a compact interval
has a unique global solution given any initial value. This is the
substantive proof obligation: the linear bound rules out finite-time
blow-up, so the solution provided by Picard-Lindelöf extends to the
full compact interval. -/

/-- **parallel-local-existence-uniqueness.** On a compact interval
`[a, b] ∋ t₀`, the linear parallel-transport ODE has a unique global
solution with prescribed initial value `Y(t₀) = v₀`. -/
theorem parallel_local_existence_uniqueness
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (huCont : ContinuousOn uPrime (Set.Icc a b))
    (huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (v₀ : E) :
    ∃! Y : ℝ → E,
      (∀ t ∈ Set.Icc a b, HasDerivAt Y
        (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
            (chartCurve (I := I) α γ t)) t) ∧
      Y t₀ = v₀ := sorry

/-! ## Chart-overlap consistency

Solutions in two overlapping charts at a common point are related by
the linear change-of-frame; equivalently the parallel-transport
condition is chart-invariant, as recorded in the global Levi-Civita
construction. -/

/-- **parallel-chart-overlap-consistency.** Two solutions in
overlapping charts at the same point coincide modulo the chart-change
linear isomorphism on tangent fibres; equivalently the parallel
transport equation is invariant under chart transitions. -/
theorem parallel_chart_overlap_consistency
    (g : SmoothRiemannianMetric I M) (α β : M) (γ : ℝ → M)
    (uPrimeα uPrimeβ : ℝ → E) (Y : ℝ → E) (s : Set ℝ)
    (hαβ : ∀ t ∈ s, γ t ∈ (chartAt H α).source ∩ (chartAt H β).source) :
    IsParallelChart (I := I) g α γ uPrimeα Y s ↔
      IsParallelChart (I := I) g β γ uPrimeβ Y s := sorry

/-! ## Global extension

Cover `ℝ` by a locally finite family of compact intervals; on each
apply the local existence/uniqueness theorem; glue via
chart-overlap consistency to obtain a unique parallel section on all
of `ℝ`. -/

/-- **parallel-global-extension.** There is a unique global parallel
section `V : ℝ → E` along the smooth curve `γ` with prescribed initial
value `V(t₀) = v₀`. Phrased in any fixed chart `α`, the section
satisfies the chart-local parallel-transport ODE on every compact
sub-interval where `γ` stays inside the chart's source. -/
theorem parallel_global_extension
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) :
    ∃! V : ℝ → E,
      V t₀ = v₀ ∧
      (∀ α : M, ∀ s : Set ℝ, (∀ t ∈ s, γ t ∈ (chartAt H α).source) →
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t) V s) := sorry

/-! ## Packaging as a `SectionAlongCurve`

Wrap the unique global solution from `parallel-global-extension` as a
`SectionAlongCurve I M γ`. Expose the initial-value simp lemma and the
"parallel in every chart" simp lemma. -/

/-- **parallel-section-packaging (def).** The parallel transport of
`v₀ ∈ T_{γ t₀} M` along the smooth curve `γ`, as a
`SectionAlongCurve I M γ`. -/
noncomputable def parallelTransport
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) : SectionAlongCurve I M γ := sorry

/-- **parallel-section-packaging (initial value).** The parallel
transport agrees with `v₀` at the base time `t₀`. -/
@[simp] theorem parallelTransport_initial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) :
    (parallelTransport (I := I) g γ hγ t₀ v₀).toFun t₀ = v₀ := sorry

/-- **parallel-section-packaging (parallel in every chart).** In every
chart `α` and on every interval where `γ` lies in the chart source,
`parallelTransport g γ hγ t₀ v₀` satisfies the chart-local
parallel-transport equation. -/
theorem parallelTransport_isParallel
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) (α : M) (s : Set ℝ)
    (hs : ∀ t ∈ s, γ t ∈ (chartAt H α).source) :
    IsParallelChart (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t)
      (parallelTransport (I := I) g γ hγ t₀ v₀).toFun s := sorry

/-! ## Metric compatibility: parallel transport preserves the inner
product

Because the Levi-Civita connection is metric-compatible, two parallel
sections `V` and `W` along `γ` satisfy
`d/dt ⟨V(t), W(t)⟩_g = 0`; hence the inner product is constant along
`γ`. -/

/-- **parallel-transport-preserves-inner-product.** For two parallel
sections `V, W` along `γ`, the function `t ↦ g(γ t)(V t, W t)` is
constant; in particular it equals its value at `t₀`. -/
theorem parallelTransport_preserves_inner_product
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ w₀ : E) (t : ℝ) :
    g.inner (γ t)
        ((parallelTransport (I := I) g γ hγ t₀ v₀).toFun t)
        ((parallelTransport (I := I) g γ hγ t₀ w₀).toFun t) =
      g.inner (γ t₀) v₀ w₀ := sorry

/-! ## Parallel orthonormal frame on `(γ')⊥`

Given a unit-speed geodesic, pick an orthonormal basis of the
orthogonal complement of `γ'(0)` in `T_{γ 0} M` and parallel-transport
it. Orthogonality to `γ'` is preserved because `γ'` itself is parallel
(geodesic equation `∇_{γ'} γ' = 0`); orthonormality is preserved by
the previous theorem. -/

/-- **parallel-on-frame-perp-to-geodesic.** For a unit-speed geodesic
`γ` on `[0, L]`, there exists a family `e : Fin (Module.finrank ℝ E - 1)
→ SectionAlongCurve I M γ` of parallel sections that, at every time
`t ∈ [0, L]`, gives an orthonormal basis of the orthogonal complement
of the velocity `γ'(t)` in `T_{γ t} M`. -/
theorem parallel_on_frame_perp_to_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (hL : 0 < L)
    (uPrime : ℝ → E)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
        ((parallelTransport (I := I) g γ hγ 0 (uPrime 0)).toFun t)
        ((parallelTransport (I := I) g γ hγ 0 (uPrime 0)).toFun t) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ α : M, ∀ s : Set ℝ, (∀ t ∈ s, γ t ∈ (chartAt H α).source) →
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t) (e i).toFun s) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (uPrime t) = 0) := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
