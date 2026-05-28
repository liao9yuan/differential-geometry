import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartTransition
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelLocalODE
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue

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
`[a, b] ∋ t₀`, the linear parallel-transport ODE has a solution
`Y : ℝ → E` with prescribed initial value `Y(t₀) = v₀`, and any
solution agrees with it on `[a, b]`. The derivative condition is
phrased as `HasDerivWithinAt` on `Icc a b` since the solution is
only determined there; uniqueness is therefore expressed as
`Set.EqOn` rather than functional equality on all of `ℝ`. -/
theorem parallel_local_existence_uniqueness [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (huCont : ContinuousOn uPrime (Set.Icc a b))
    (huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ Y : ℝ → E,
      ((∀ t ∈ Set.Icc a b, HasDerivWithinAt Y
          (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
        Y t₀ = v₀) ∧
      (∀ Y' : ℝ → E,
        ((∀ t ∈ Set.Icc a b, HasDerivWithinAt Y'
            (- chartChristoffelContraction (I := I) g α (uPrime t) (Y' t)
                (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
          Y' t₀ = v₀) →
        Set.EqOn Y Y' (Set.Icc a b)) := by
  obtain ⟨Y, hY_deriv, hY_init⟩ :=
    parallel_local_existence_on_Icc (I := I) g α γ uPrime hab ht₀ huCont
      huCurveCont hsource v₀
  refine ⟨Y, ⟨hY_deriv, hY_init⟩, ?_⟩
  rintro Y' ⟨hY'_deriv, hY'_init⟩
  exact parallel_local_uniqueness_on_Icc (I := I) g α γ uPrime hab ht₀ huCont
    huCurveCont hsource hY_deriv hY'_deriv (hY_init.trans hY'_init.symm)

/-! ## Chart-overlap consistency

Solutions in two overlapping charts at a common point are related by
the linear change-of-frame; equivalently the parallel-transport
condition is chart-invariant, as recorded in the global Levi-Civita
construction. -/

/-- **parallel-chart-overlap-consistency.** The chart-α coordinate
representation `Yα` of a tangent-field along `γ` and its chart-β
counterpart `Yβ` are related by the chart-transition Jacobian
`T_{αβ} := chartTransitionAt α β` evaluated along the chart-curve
`u_α(t) := extChartAt I α (γ t)`:
`Yβ t = T_{αβ}(u_α t)(Yα t)`,
and likewise `uPrimeβ t = T_{αβ}(u_α t)(uPrimeα t)`. Under this
transition relation, parallelism of `Yα` in the chart at `α` is
equivalent to parallelism of the transition-transformed
`Yβ := t ↦ T_{αβ}(u_α t)(Yα t)` in the chart at `β`.

This is the mathematically correct formulation: the *same manifold
tangent-section* admits two distinct `E`-valued representations, one
per chart, related by the chart-transition Jacobian. The previous
"same `Y`" form is mathematically false because the chart-α and
chart-β coordinate representations differ. -/
theorem parallel_chart_overlap_consistency [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (γ : ℝ → M)
    (uPrimeα Yα : ℝ → E) (s : Set ℝ)
    (hαβ : ∀ t ∈ s, γ t ∈ (chartAt H α).source ∩ (chartAt H β).source)
    (_hpar : IsParallelChart (I := I) g α γ uPrimeα Yα s) :
    IsParallelChart (I := I) g β γ
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (uPrimeα t))
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (Yα t))
      s := sorry

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
`SectionAlongCurve I M γ`. Built by `Classical.choose` over the unique
global parallel extension. -/
noncomputable def parallelTransport
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) : SectionAlongCurve I M γ :=
  ⟨(parallel_global_extension (I := I) g γ hγ t₀ v₀).exists.choose⟩

/-- The defining property of `parallelTransport`: the underlying
function is the chosen witness of `parallel_global_extension`, hence
satisfies both the initial-value condition and the chart-local
parallel-transport ODE on every chart-segment. -/
lemma parallelTransport_spec
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) :
    (parallelTransport (I := I) g γ hγ t₀ v₀).toFun t₀ = v₀ ∧
      (∀ α : M, ∀ s : Set ℝ, (∀ t ∈ s, γ t ∈ (chartAt H α).source) →
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t)
          (parallelTransport (I := I) g γ hγ t₀ v₀).toFun s) :=
  (parallel_global_extension (I := I) g γ hγ t₀ v₀).exists.choose_spec

/-- **parallel-section-packaging (initial value).** The parallel
transport agrees with `v₀` at the base time `t₀`. -/
@[simp] theorem parallelTransport_initial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) :
    (parallelTransport (I := I) g γ hγ t₀ v₀).toFun t₀ = v₀ :=
  (parallelTransport_spec (I := I) g γ hγ t₀ v₀).1

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
      (parallelTransport (I := I) g γ hγ t₀ v₀).toFun s :=
  (parallelTransport_spec (I := I) g γ hγ t₀ v₀).2 α s hs

/-! ## Metric compatibility: parallel transport preserves the inner
product

Because the Levi-Civita connection is metric-compatible, two parallel
sections `V` and `W` along `γ` satisfy
`d/dt ⟨V(t), W(t)⟩_g = 0`; hence the inner product is constant along
`γ`. -/

/-- **Local constancy of the chart-Gram inner product of two parallel
sections.** If `V` and `W` are both parallel along `γ` in the chart at
`α` on a set `s ⊆ ℝ`, and `γ` maps `s` into the chart source, then the
chart-Gram form `t ↦ ⟨V, W⟩_G(t)` has derivative `0` at every interior
point of `s` (every `t` for which `s ∈ 𝓝 t`).

This is the engine `chartGramAlongCurve_hasDerivAt_covariant`: the
covariant-derivative correction terms `V'(t) + Γ(u', V)` and
`W'(t) + Γ(u', W)` both vanish because `V` and `W` are parallel, so the
Leibniz-product derivative of the Gram form is `0`. -/
theorem chartGramAlongCurve_hasDerivAt_zero_of_parallel [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {V W : ℝ → E} {s : Set ℝ}
    (hV : IsParallelChart (I := I) g α γ
      (fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t) V s)
    (hW : IsParallelChart (I := I) g α γ
      (fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t) W s)
    (hsrc : ∀ τ ∈ s, γ τ ∈ (chartAt H α).source)
    {t : ℝ} (ht : s ∈ 𝓝 t) :
    HasDerivAt (fun τ => AlongCurve.chartGramAlongCurve (I := I) g α γ V W τ)
      0 t := by
  have hts : t ∈ s := mem_of_mem_nhds ht
  -- Curve velocity, parallelism derivatives, and interior membership at `t`.
  have huPrime : HasDerivAt (AlongCurve.chartCurve (I := I) α γ)
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) t :=
    (AlongCurve.IsParallelChart.chartCurve_hasDerivAt hV hts)
  have hVd : HasDerivAt V
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
          (AlongCurve.chartCurve (I := I) α γ t)) t :=
    AlongCurve.IsParallelChart.hasDerivAt hV hts
  have hWd : HasDerivAt W
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
          (AlongCurve.chartCurve (I := I) α γ t)) t :=
    AlongCurve.IsParallelChart.hasDerivAt hW hts
  -- `u(t)` lies in the interior of the chart target.
  have hmem : AlongCurve.chartCurve (I := I) α γ t ∈
      interior (extChartAt I α).target := by
    have hxsrc : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hsrc t hts
    have hxtarget : AlongCurve.chartCurve (I := I) α γ t ∈
        (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hxtarget
  -- Apply the covariant product rule with the chosen `Vprime`, `Wprime`.
  have hbase := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant
    (I := I) g α γ V W
    (uPrime := fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ)
    (Vprime := fun _ => - chartChristoffelContraction (I := I) g α
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
      (AlongCurve.chartCurve (I := I) α γ t))
    (Wprime := fun _ => - chartChristoffelContraction (I := I) g α
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
      (AlongCurve.chartCurve (I := I) α γ t))
    huPrime hmem hVd hWd
  -- The covariant correction terms vanish: `V'(t) + Γ(u', V) = 0` etc.
  have hVzero :
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
          (AlongCurve.chartCurve (I := I) α γ t))
        + chartChristoffelContraction (I := I) g α
            (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
            (AlongCurve.chartCurve (I := I) α γ t) = 0 := by
    rw [neg_add_cancel]
  have hWzero :
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
          (AlongCurve.chartCurve (I := I) α γ t))
        + chartChristoffelContraction (I := I) g α
            (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
            (AlongCurve.chartCurve (I := I) α γ t) = 0 := by
    rw [neg_add_cancel]
  -- Substitute the zero corrections; the derivative value collapses to `0`.
  rw [hVzero, hWzero] at hbase
  simpa using hbase

/-- **parallel-transport-preserves-inner-product.** For two parallel
transports `V`, `W` along `γ`, written in a fixed chart at `α`, the
chart-Gram inner product
`t ↦ ⟨V, W⟩_G(t) = ∑_{i,j} G_{ij}(u(t)) · Vᶜ_i(t) · Wᶜ_j(t)`
— the genuine Riemannian inner product `g(γ t)(V̄(t), W̄(t))` of the
tangent vectors `V̄(t) = triv.symmL (γ t)(V t)`, `W̄(t) = triv.symmL
(γ t)(W t)` represented in the chart frame at `α` — is **constant in
`t` on any interval `s` where `γ` stays in the chart source**. In
particular, on such an interval it equals its value at the base time
`t₀ ∈ s`.

Here `V t = (parallelTransport g γ hγ t₀ v₀).toFun t` etc. are the
chart-coordinate representations on which the parallel-transport ODE
`Y'(t) = -Γ(u'(t), Y(t))(u(t))` acts. The Levi-Civita connection is
metric-compatible (`chartGramOnE_partialDeriv_eq_christoffel_sum_split`),
so the covariant-derivative product rule gives `d/dt ⟨V, W⟩_G = 0`. -/
theorem parallelTransport_preserves_inner_product [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ w₀ : E) (α : M) {s : Set ℝ} (hs : IsPreconnected s)
    (hsrc : ∀ τ ∈ s, γ τ ∈ (chartAt H α).source)
    {t : ℝ} (ht : t ∈ s) (ht₀ : t₀ ∈ s) :
    AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g γ hγ t₀ v₀).toFun
        (parallelTransport (I := I) g γ hγ t₀ w₀).toFun t =
      AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g γ hγ t₀ v₀).toFun
        (parallelTransport (I := I) g γ hγ t₀ w₀).toFun t₀ := by
  classical
  set V : ℝ → E := (parallelTransport (I := I) g γ hγ t₀ v₀).toFun with hV_def
  set W : ℝ → E := (parallelTransport (I := I) g γ hγ t₀ w₀).toFun with hW_def
  set f : ℝ → ℝ := fun τ =>
    AlongCurve.chartGramAlongCurve (I := I) g α γ V W τ with hf_def
  -- Argue on the open set `o := γ ⁻¹' (chartAt H α).source ⊇ s`.
  set o : Set ℝ := γ ⁻¹' (chartAt H α).source with ho_def
  have hγcont : Continuous γ := hγ.continuous
  have ho_open : IsOpen o := (chartAt H α).open_source.preimage hγcont
  have hto : t ∈ o := hsrc t ht
  have ht₀o : t₀ ∈ o := hsrc t₀ ht₀
  -- On `o`, `V` and `W` are parallel: every `τ ∈ o` has `γ τ ∈ source`.
  have hVparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) V o :=
    parallelTransport_isParallel (I := I) g γ hγ t₀ v₀ α o (fun τ hτ => hτ)
  have hWparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) W o :=
    parallelTransport_isParallel (I := I) g γ hγ t₀ w₀ α o (fun τ hτ => hτ)
  -- `f` has derivative `0` at every point of the open set `o`.
  have hderiv : ∀ τ ∈ o, HasDerivAt f 0 τ := by
    intro τ hτ
    exact chartGramAlongCurve_hasDerivAt_zero_of_parallel (I := I) g α γ
      hVparo hWparo (fun σ hσ => hσ) (ho_open.mem_nhds hτ)
  -- `f` is locally constant on the open set `o` (Mathlib mean-value engine),
  -- hence constant on the connected component of `t` containing `t₀`.
  have hDiffOn : DifferentiableOn ℝ f o :=
    fun τ hτ => (hderiv τ hτ).differentiableAt.differentiableWithinAt
  have hEqOn : o.EqOn (deriv f) 0 := fun τ hτ => (hderiv τ hτ).deriv
  -- `f` is locally constant on `o`: the preimage of any singleton meets `o` in
  -- an open set. Both `t` and `t₀` lie in the same connected component of `o`
  -- only when they are joined inside `o`; instead we use that the difference
  -- `f - const` has zero derivative on the connected component.
  -- Use the locally-constant characterisation directly: `f` agrees with the
  -- constant `f t₀` on the maximal preconnected (= connected) subset of `o`
  -- containing `t₀`. We take that component and show `t` lies in it.
  set comp : Set ℝ := connectedComponentIn o t₀ with hcomp_def
  have hcomp_open : IsOpen comp :=
    ho_open.connectedComponentIn
  have hcomp_pre : IsPreconnected comp :=
    isPreconnected_connectedComponentIn
  have hcomp_sub : comp ⊆ o := connectedComponentIn_subset o t₀
  have ht₀comp : t₀ ∈ comp := mem_connectedComponentIn ht₀o
  -- On the open preconnected `comp ⊆ o`, `f` is constant.
  have hconst : ∀ x ∈ comp, f x = f t₀ :=
    fun x hx => hcomp_open.is_const_of_deriv_eq_zero hcomp_pre
      (fun τ hτ => (hderiv τ (hcomp_sub hτ)).differentiableAt.differentiableWithinAt)
      (fun τ hτ => hEqOn (hcomp_sub hτ)) hx ht₀comp
  -- `t` lies in the same connected component of `o` as `t₀`: `s` is
  -- preconnected, `s ⊆ o`, and `t₀ ∈ s`, so `s ⊆ connectedComponentIn o t₀`.
  have hso : s ⊆ o := fun τ hτ => hsrc τ hτ
  have hs_sub_comp : s ⊆ comp :=
    hs.subset_connectedComponentIn ht₀ hso
  have htcomp : t ∈ comp := hs_sub_comp ht
  exact hconst t htcomp

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
