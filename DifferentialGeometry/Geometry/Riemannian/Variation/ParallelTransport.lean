import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
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

-- The chart-transition foot-slot derivative helpers
-- (`chartCoord_fderiv_chartTransitionAt_general`,
-- `fderiv_chartTransitionAt_apply_eq_pushCorrection`) are public in
-- `Geodesic/ChartTransition.lean` and are in scope via the `Geodesic` open above.

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
    (g : SmoothRiemannianMetric I M) (α β : M) (γ : ℝ → M) (hγ : Continuous γ)
    (uPrimeα Yα : ℝ → E) (s : Set ℝ)
    (hαβ : ∀ t ∈ s, γ t ∈ (chartAt H α).source ∩ (chartAt H β).source)
    (hpar : IsParallelChart (I := I) g α γ uPrimeα Yα s) :
    IsParallelChart (I := I) g β γ
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (uPrimeα t))
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (Yα t))
      s := by
  classical
  -- Abbreviations for the chart-β transformed velocity / section.
  set uPrimeβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t) with huPrimeβ
  set Yβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (Yα t) with hYβ
  refine ⟨?_, ?_⟩
  · -- The chart-β curve has the prescribed derivative `uPrimeβ t`.
    intro t ht
    -- Open neighbourhood of `t` on which `γ` stays in both chart sources.
    set U : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) with hU_def
    have hU_open : IsOpen U :=
      ((chartAt H α).open_source.inter (chartAt H β).open_source).preimage hγ
    have htU : t ∈ U := hαβ t ht
    have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds htU
    -- On `U`, `chartCurve β γ = chartTransitionMap α β ∘ chartCurve α γ`.
    have hcurve_eq : (chartCurve (I := I) β γ) =ᶠ[𝓝 t]
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s)) := by
      filter_upwards [hU_nhds] with σ hσ
      obtain ⟨hσα, _hσβ⟩ := hσ
      rw [chartCurve_def, chartCurve_def]
      exact (chartTransitionMap_apply_extChartAt (I := I) α β hσα).symm
    -- Chain rule for the composition.
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hsrc_t : chartCurve (I := I) α γ t ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β (hαβ t ht).1 (hαβ t ht).2
    have hTdiff : DifferentiableAt ℝ (chartTransitionMap (I := I) α β)
        (chartCurve (I := I) α γ t) :=
      chartTransitionMap_differentiableAt (I := I) α β hsrc_t
    have hcomp : HasDerivAt
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s))
        (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t)) t := by
      have := hTdiff.hasFDerivAt.comp_hasDerivAt t huα
      simpa [chartTransitionAt_def] using this
    -- Transfer to `chartCurve β γ` via the local equality.
    exact (hcomp.congr_of_eventuallyEq hcurve_eq)
  · -- The chart-β ODE: `Yβ'(t) = - Γ_β(uPrimeβ t, Yβ t)(u_β t)`.
    intro t ht
    -- Manifold point and source memberships.
    obtain ⟨htα, htβ⟩ := hαβ t ht
    set x : E := chartCurve (I := I) α γ t with hx_def
    have hsrc_t : x ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β htα htβ
    -- Derivatives of the chart-α curve and the chart-α section.
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hYαd : HasDerivAt Yα
        (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x) t :=
      IsParallelChart.hasDerivAt hpar ht
    -- The transition-CLM along the chart-α curve is differentiable.
    have hAdiff : DifferentiableAt ℝ
        (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E)) x := by
      have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
        chartTransitionSource_isOpen (I := I) α β
      exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
        (h_open.mem_nhds hsrc_t)).differentiableAt (by simp)
    have hcA : HasDerivAt
        (fun s => (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ s) : E →L[ℝ] E))
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) t :=
      hAdiff.hasFDerivAt.comp_hasDerivAt t huα
    -- Product (CLM-application) rule for `Yβ t = (T_{αβ}(u_α t)) (Yα t)`.
    have hYβd : HasDerivAt Yβ
        (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)) t := by
      have := hcA.clm_apply hYαd
      simpa [hYβ, hx_def] using this
    -- Rewrite the derivative value into the chart-β Christoffel contraction.
    -- Step 1: the foot-slot derivative = forward push of the second-derivative correction.
    have hfoot :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t) =
          chartTransitionAt (I := I) α β x
            (chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x) :=
      fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α β hsrc_t
        (uPrimeα t) (Yα t)
    -- Step 2: the Christoffel transformation law (α → β at the manifold point γ t).
    have hxeq : x = extChartAt I α (γ t) := by rw [hx_def, chartCurve_def]
    have htransform :
        chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
          chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
              (chartChristoffelContraction (I := I) g β
                (chartTransitionAt (I := I) α β x (uPrimeα t))
                (chartTransitionAt (I := I) α β x (Yα t))
                (chartTransitionMap (I := I) α β x))
            + chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x := by
      rw [hxeq]
      exact chartChristoffelContraction_transform (I := I) g α β htα htβ
        (uPrimeα t) (Yα t)
    -- Identify the chart-β curve / velocity / section in terms of the maps.
    have huβ_eq : chartCurve (I := I) β γ t = chartTransitionMap (I := I) α β x := by
      rw [hx_def, chartCurve_def, chartCurve_def,
        chartTransitionMap_apply_extChartAt (I := I) α β htα]
    -- The derivative value `D = foot + T_{αβ}(x)(-Γ_α)` collapses to `-Γ_β`.
    have hDcollapse :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)
          = - chartChristoffelContraction (I := I) g β
              (uPrimeβ t) (Yβ t) (chartCurve (I := I) β γ t) := by
      -- Push everything through `chartTransitionAt α β x` (a linear map).
      rw [hfoot, map_neg, ← sub_eq_add_neg, ← map_sub]
      -- `corr - Γ_α = - chartTransitionAt β α (Tx) (Γ_β(...))`.
      have hsub :
          chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x -
              chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
            - chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
                (chartChristoffelContraction (I := I) g β
                  (chartTransitionAt (I := I) α β x (uPrimeα t))
                  (chartTransitionAt (I := I) α β x (Yα t))
                  (chartTransitionMap (I := I) α β x)) := by
        rw [htransform]; abel
      rw [hsub, map_neg]
      -- `chartTransitionAt α β x ∘ chartTransitionAt β α (Tx) = id`.
      have hinv := chartTransitionAt_comp_chartTransitionAt' (I := I) α β hsrc_t
      have hid := congrArg (fun L : E →L[ℝ] E => L
          (chartChristoffelContraction (I := I) g β
            (chartTransitionAt (I := I) α β x (uPrimeα t))
            (chartTransitionAt (I := I) α β x (Yα t))
            (chartTransitionMap (I := I) α β x))) hinv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
      rw [hid, huβ_eq]
    -- Conclude: `HasDerivAt Yβ (- Γ_β(uPrimeβ, Yβ)(u_β)) t`, matching the predicate.
    have hgoal : HasDerivAt Yβ
        ((fun _ : ℝ => (0 : E)) t -
          chartChristoffelContraction (I := I) g β (uPrimeβ t) (Yβ t)
            (chartCurve (I := I) β γ t)) t := by
      rw [hDcollapse] at hYβd
      simpa using hYβd
    exact hgoal

/-! ## Single-chart extension

Inside one fixed chart `α`, on an open interval `Ioo a b` where `γ`
stays in the chart source, the chart-local linear parallel-transport
ODE has a solution with any prescribed initial value, unique on that
interval.

The naive "single `V : ℝ → E`, parallel in *every* chart at once"
formulation is mathematically false on a non-parallelizable manifold:
by `parallel_chart_overlap_consistency`, if `V` is parallel in chart
`α` on `s`, the chart-`β` representation of the *same* tangent section
is `t ↦ chartTransitionAt α β (chartCurve α γ t) (V t)`, which differs
from `V` whenever the transition Jacobian is nontrivial (e.g. on `S²`).
A genuinely chart-independent global parallel transport must therefore
carry the transition Jacobian between charts — i.e. be a bundle
`SectionAlongCurve` glued by `parallel_chart_overlap_consistency` — so
the honest local primitive is the single-fixed-chart statement below.

A bare `∃! V : ℝ → E` would also be unsound even within one chart: the
predicate `IsParallelChart … V (Ioo a b)` constrains `V` only on
`Ioo a b`, so any function agreeing with a solution there but differing
off the interval would satisfy it too. Uniqueness is therefore stated
as `Set.EqOn … (Ioo a b)`, the genuine content delivered by
`parallel_local_existence_uniqueness`. -/

/-- **parallel-single-chart-extension.** Fix a chart basepoint `α` and
an open interval `Ioo a b ∋ t₀` on which `γ` stays in the chart source
and the chart-curve `u := chartCurve α γ` is differentiable. Then there
is a section `V : ℝ → E`, parallel in the chart at `α` on `Ioo a b`
with `V t₀ = v₀`, and any parallel section sharing the initial value at
`t₀` agrees with it on `Ioo a b`.

Existence and uniqueness both come from
`parallel_local_existence_uniqueness`: the chart-local
`HasDerivWithinAt … (Icc a b)` form there is converted to the two-sided
`HasDerivAt` form of `IsParallelChart` on the interior `Ioo a b`, where
`Icc a b ∈ 𝓝 t`. The chart-curve differentiability hypothesis `huDeriv`
supplies the first conjunct of `IsParallelChart` (its velocity slot);
it is a genuine smoothness fact about `γ`, not a restatement of the
conclusion. -/
theorem parallel_global_extension [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (huCont : ContinuousOn (fun t => deriv (chartCurve (I := I) α γ) t) (Set.Icc a b))
    (huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (huDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (chartCurve (I := I) α γ) (deriv (chartCurve (I := I) α γ) t) t)
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ V : ℝ → E,
      (V t₀ = v₀ ∧
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t) V (Set.Ioo a b)) ∧
      (∀ V' : ℝ → E,
        (V' t₀ = v₀ ∧
          IsParallelChart (I := I) g α γ
            (fun t => deriv (chartCurve (I := I) α γ) t) V' (Set.Ioo a b)) →
        Set.EqOn V V' (Set.Ioo a b)) := by
  -- The chart-local existence primitive on `Icc a b`. (Uniqueness on the
  -- *open* interval is obtained below via Grönwall, so only the existence
  -- half of `parallel_local_existence_uniqueness` is needed here.)
  obtain ⟨Y, ⟨hY_deriv, hY_init⟩, -⟩ :=
    parallel_local_existence_uniqueness (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) hab (Set.mem_Icc_of_Ioo ht₀)
      huCont huCurveCont hsource v₀
  -- `Icc a b ∈ 𝓝 t` for `t ∈ Ioo a b`, so `HasDerivWithinAt (Icc a b)`
  -- upgrades to two-sided `HasDerivAt` at interior points.
  have hIccNhds : ∀ t ∈ Set.Ioo a b, Set.Icc a b ∈ 𝓝 t := by
    intro t ht
    exact Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  -- Package the existence witness `Y` as `IsParallelChart` on `Ioo a b`.
  have hY_par : IsParallelChart (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) Y (Set.Ioo a b) := by
    refine ⟨fun t ht => huDeriv t ht, ?_⟩
    intro t ht
    have hin : t ∈ Set.Icc a b := Set.mem_Icc_of_Ioo ht
    have hd := (hY_deriv t hin).hasDerivAt (hIccNhds t ht)
    simpa using hd
  refine ⟨Y, ⟨hY_init, hY_par⟩, ?_⟩
  -- Uniqueness on the open interval via Grönwall: any competing parallel
  -- section sharing the value at `t₀` agrees with `Y` on `Ioo a b`. The
  -- Lipschitz constant comes from the uniform operator-norm bound on the
  -- Christoffel contraction over the compact `Icc a b`, restricted to `Ioo`.
  obtain ⟨K, hK_Icc⟩ :=
    parallel_lipschitz_bound_on_compact (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) hab huCont huCurveCont hsource
  have hK_Ioo : ParallelTransportLipschitzBound (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) K (Set.Ioo a b) :=
    fun t ht => hK_Icc t (Set.mem_Icc_of_Ioo ht)
  intro V' ⟨hV'_init, hV'_par⟩
  exact IsParallelChart.unique_of_initial hY_par hV'_par hK_Ioo ht₀
    (hY_init.trans hV'_init.symm)

/-! ## Packaging as a `SectionAlongCurve`

Wrap the unique single-chart solution from `parallel_global_extension`
as a `SectionAlongCurve I M γ`. Because the honest existence statement
is local to one fixed chart `α` and one open interval `Ioo a b`, the
parallel-transport section is now indexed by that chart-and-segment
data. Expose the initial-value lemma and the parallelism lemma in the
chart at `α` on `Ioo a b`. -/

/-- The data pinning down a single-chart parallel-transport problem on
an open segment: a chart basepoint `α`, an open interval `Ioo a b`
containing the base time `t₀`, continuity/differentiability of the
chart-curve there, and the requirement that `γ` stays in the chart
source on the closed interval. Bundling these keeps the
`parallelTransport` section and its specification lemmas readable. -/
structure ParallelSegmentData [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (a b t₀ : ℝ) : Prop where
  /-- The interval is nondegenerate. -/
  hab : a ≤ b
  /-- The base time lies in the open interval. -/
  ht₀ : t₀ ∈ Set.Ioo a b
  /-- The chart-curve velocity is continuous on the closed interval. -/
  huCont : ContinuousOn (fun t => deriv (chartCurve (I := I) α γ) t) (Set.Icc a b)
  /-- The chart-curve is continuous on the closed interval. -/
  huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b)
  /-- The chart-curve is differentiable on the open interval. -/
  huDeriv : ∀ t ∈ Set.Ioo a b,
    HasDerivAt (chartCurve (I := I) α γ) (deriv (chartCurve (I := I) α γ) t) t
  /-- `γ` stays in the chart source on the closed interval. -/
  hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source

/-- **parallel-section-packaging (def).** The parallel transport of
`v₀` along the smooth curve `γ`, in the chart at `α` on the open
segment `Ioo a b ∋ t₀`, as a `SectionAlongCurve I M γ`. Built by
`Classical.choose` over the unique single-chart parallel extension of
`parallel_global_extension`. The underlying function is determined only
on `Ioo a b`; off the interval it is an unconstrained witness. -/
noncomputable def parallelTransport [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    SectionAlongCurve I M γ :=
  ⟨(parallel_global_extension (I := I) g α γ hd.hab hd.ht₀ hd.huCont
      hd.huCurveCont hd.huDeriv hd.hsource v₀).choose⟩

/-- The defining property of `parallelTransport`: the underlying
function is the chosen witness of `parallel_global_extension`, hence
satisfies the initial-value condition at `t₀` and the chart-`α`
parallel-transport ODE on `Ioo a b`. -/
lemma parallelTransport_spec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    (parallelTransport (I := I) g α γ hd v₀).toFun t₀ = v₀ ∧
      IsParallelChart (I := I) g α γ
        (fun t => deriv (chartCurve (I := I) α γ) t)
        (parallelTransport (I := I) g α γ hd v₀).toFun (Set.Ioo a b) :=
  (parallel_global_extension (I := I) g α γ hd.hab hd.ht₀ hd.huCont
    hd.huCurveCont hd.huDeriv hd.hsource v₀).choose_spec.1

/-- **parallel-section-packaging (initial value).** The parallel
transport agrees with `v₀` at the base time `t₀`. -/
@[simp] theorem parallelTransport_initial [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    (parallelTransport (I := I) g α γ hd v₀).toFun t₀ = v₀ :=
  (parallelTransport_spec (I := I) g α γ hd v₀).1

/-- **parallel-section-packaging (parallel in the chart at `α`).** On
the open segment `Ioo a b`, `parallelTransport g α γ hd v₀` satisfies
the chart-`α` parallel-transport equation. -/
theorem parallelTransport_isParallel [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    IsParallelChart (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t)
      (parallelTransport (I := I) g α γ hd v₀).toFun (Set.Ioo a b) :=
  (parallelTransport_spec (I := I) g α γ hd v₀).2

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
transports `V`, `W` along `γ`, written in the same chart at `α` and
sharing the same segment data `hd`, the chart-Gram inner product
`t ↦ ⟨V, W⟩_G(t) = ∑_{i,j} G_{ij}(u(t)) · Vᶜ_i(t) · Wᶜ_j(t)`
— the genuine Riemannian inner product `g(γ t)(V̄(t), W̄(t))` of the
tangent vectors `V̄(t) = triv.symmL (γ t)(V t)`, `W̄(t) = triv.symmL
(γ t)(W t)` represented in the chart frame at `α` — is **constant in
`t` on the open segment `Ioo a b`**.  In particular it equals its value
at the base time `t₀ ∈ Ioo a b`.

Here `V t = (parallelTransport g α γ hd v₀).toFun t` etc. are the
chart-coordinate representations on which the parallel-transport ODE
`Y'(t) = -Γ(u'(t), Y(t))(u(t))` acts. The Levi-Civita connection is
metric-compatible (`chartGramOnE_partialDeriv_eq_christoffel_sum_split`),
so the covariant-derivative product rule gives `d/dt ⟨V, W⟩_G = 0`.
This is sound: both sections are parallel in the *same* chart at `α`,
so no chart-transition Jacobian intervenes. -/
theorem parallelTransport_preserves_inner_product [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ w₀ : E)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g α γ hd v₀).toFun
        (parallelTransport (I := I) g α γ hd w₀).toFun t =
      AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g α γ hd v₀).toFun
        (parallelTransport (I := I) g α γ hd w₀).toFun t₀ := by
  classical
  set V : ℝ → E := (parallelTransport (I := I) g α γ hd v₀).toFun with hV_def
  set W : ℝ → E := (parallelTransport (I := I) g α γ hd w₀).toFun with hW_def
  set f : ℝ → ℝ := fun τ =>
    AlongCurve.chartGramAlongCurve (I := I) g α γ V W τ with hf_def
  -- The open segment `Ioo a b` is open; `γ` stays in the chart source there.
  set o : Set ℝ := Set.Ioo a b with ho_def
  have ho_open : IsOpen o := isOpen_Ioo
  have hsrc_o : ∀ τ ∈ o, γ τ ∈ (chartAt H α).source :=
    fun τ hτ => hd.hsource τ (Set.mem_Icc_of_Ioo hτ)
  -- `V` and `W` are parallel in the chart at `α` on `o`.
  have hVparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) V o :=
    parallelTransport_isParallel (I := I) g α γ hd v₀
  have hWparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) W o :=
    parallelTransport_isParallel (I := I) g α γ hd w₀
  -- `f` has derivative `0` at every point of the open interval `o`.
  have hderiv : ∀ τ ∈ o, HasDerivAt f 0 τ := by
    intro τ hτ
    exact chartGramAlongCurve_hasDerivAt_zero_of_parallel (I := I) g α γ
      hVparo hWparo hsrc_o (ho_open.mem_nhds hτ)
  -- `f` is constant on the (pre)connected open interval `o`.
  have hconst : ∀ x ∈ o, f x = f t₀ :=
    fun x hx => ho_open.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun τ hτ => (hderiv τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => (hderiv τ hτ).deriv) hx hd.ht₀
  exact hconst t ht

/-! ## Cross-chart global parallel transport on a compact interval

The honest single-chart `parallelTransport` lives in one chart `α` on one
open segment. To build a *globally defined* parallel transport along all of
`γ` on a compact interval `[0, L]` — a genuine bundle section
`V : ∀ t, TangentSpace I (γ t)` with vanishing *intrinsic* covariant
derivative `covDerivAlong g γ V` — one chops `[0, L]` into finitely many
sub-intervals (via the Lebesgue number of the chart-source cover of the
compact curve image), solves the linear parallel-transport ODE in a single
chart on each piece, and glues. The intrinsic vanishing is read off in the
chart pinned at the *moving foot* `γ t`; the bridge from a fixed-chart
solution to the moving-foot chart is the trivialisation-composite identity
below, which says that the chart-`(γ t)` coordinate of a fixed-chart-`α`
section is its chart-transition push. -/

/-- **Trivialisation composite is the chart transition Jacobian.** For two
basepoints `α β : M` and a manifold point `b` lying in both chart sources,
the chart-`β` trivialisation coordinate of the inverse chart-`α`
trivialisation of `v` equals the chart-transition Jacobian
`chartTransitionAt α β` (evaluated at the chart-`α` image of `b`) applied to
`v`. This is the bundle-`coordChange` composition law combined with the
boundaryless identification `fderivWithin (range I) = fderiv`. -/
theorem trivCoord_comp_symmL_eq_chartTransitionAt [I.Boundaryless]
    (α β : M) {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
      Geodesic.chartTransitionAt (I := I) α β (extChartAt I α b) v := by
  -- Rewrite both trivialisation CLMs via the tangent-bundle core coordinate change.
  have hαsrc : b ∈ (chartAt H α).source := hα
  have hβsrc : b ∈ (chartAt H β).source := hβ
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hβsrc,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hαsrc]
  -- The composite of the two coordinate changes is the single coordinate change `α → β`.
  have hb_self : b ∈ (chartAt H b).source := mem_chart_source H b
  have hmem : b ∈ (tangentBundleCore I M).baseSet (achart H α)
      ∩ (tangentBundleCore I M).baseSet (achart H b)
      ∩ (tangentBundleCore I M).baseSet (achart H β) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hαsrc
    · rw [tangentBundleCore_baseSet]; exact hb_self
    · rw [tangentBundleCore_baseSet]; exact hβsrc
  have hcomp := (tangentBundleCore I M).coordChange_comp
    (achart H α) (achart H b) (achart H β) b hmem v
  -- The composite equals the single coordinate change `α → β`, i.e. `tangentCoordChange`.
  have hcc : ((tangentBundleCore I M).coordChange (achart H α) (achart H β) b) v =
      Geodesic.chartTransitionAt (I := I) α β (extChartAt I α b) v := by
    change tangentCoordChange I α β b v = _
    -- Bridge `tangentCoordChange` to `chartTransitionAt` in the boundaryless setting.
    rw [tangentCoordChange_def]
    rw [Geodesic.chartTransitionAt_def, Geodesic.chartTransitionMap_def]
    have hrange : (Set.range I : Set E) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I)
    rw [hrange, fderivWithin_univ]
  rw [← hcc]
  exact hcomp

/-- **Uniform chart partition of a curve over a compact interval.** For a
continuous curve `γ` and `L > 0`, there is a positive number of pieces `N`
and a basepoint assignment `bp : ℕ → M` such that on every grid sub-interval
`[k·L/N, (k+1)·L/N]` (for `k < N`) the curve stays inside the chart source of
`bp k`. The mesh is chosen below the Lebesgue number of the chart-source
cover of the compact image `γ '' [0, L]`. -/
theorem exists_uniform_chart_partition
    (γ : ℝ → M) (hγ : Continuous γ) {L : ℝ} (hL : 0 < L) :
    ∃ (N : ℕ) (bp : ℕ → M), 0 < N ∧
      ∀ k : ℕ, k < N → ∀ t ∈ Set.Icc (k * L / N) ((k + 1) * L / N),
        γ t ∈ (chartAt H (bp k)).source := by
  classical
  -- The chart-source cover of `Icc 0 L` indexed by `τ : ℝ`.
  set c : ℝ → Set ℝ := fun τ => γ ⁻¹' (chartAt H (γ τ)).source with hc_def
  have hc_open : ∀ τ, IsOpen (c τ) := fun τ =>
    (chartAt H (γ τ)).open_source.preimage hγ
  have hcover : Set.Icc (0 : ℝ) L ⊆ ⋃ τ, c τ := by
    intro x _hx
    exact Set.mem_iUnion.2 ⟨x, by simp only [hc_def, Set.mem_preimage]; exact mem_chart_source H (γ x)⟩
  -- Lebesgue number `δ`.
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := L)) hc_open hcover
  -- Choose `N` with mesh `L / N < δ`.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (L / δ)
  set N : ℕ := N₀ + 1 with hN_def
  have hN_pos : 0 < N := Nat.succ_pos _
  have hN_pos_real : (0 : ℝ) < N := by exact_mod_cast hN_pos
  -- Mesh bound: `L / N < δ`.
  have hmesh : L / N < δ := by
    have hN_gt : L / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast Nat.le_succ N₀)
    rw [div_lt_iff₀ hN_pos_real]
    rw [div_lt_iff₀ hδ_pos] at hN_gt
    linarith
  -- Basepoint chooser: midpoint of the `k`-th grid interval lies in `Icc 0 L`.
  have hmid_mem : ∀ k : ℕ, k < N →
      ((k * L / N + (k + 1) * L / N) / 2) ∈ Set.Icc (0 : ℝ) L := by
    intro k hk
    constructor
    · have h1 : 0 ≤ (k : ℝ) * L / N := by positivity
      have h2 : 0 ≤ ((k : ℝ) + 1) * L / N := by positivity
      linarith
    · -- `(k+1)·L/N ≤ L` since `k+1 ≤ N`.
      have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
      have hub1 : ((k : ℝ) + 1) * L / N ≤ L := by
        rw [div_le_iff₀ hN_pos_real]
        nlinarith [hL.le, hk1]
      have hub0 : (k : ℝ) * L / N ≤ ((k : ℝ) + 1) * L / N := by
        apply div_le_div_of_nonneg_right ?_ hN_pos_real.le
        nlinarith [hL.le]
      linarith
  -- For each `k < N`, pick a basepoint time whose `δ`-ball covers the grid interval.
  have hchoose : ∀ k : ℕ, k < N → ∃ τ : ℝ,
      ∀ t ∈ Set.Icc ((k : ℝ) * L / N) (((k : ℝ) + 1) * L / N),
        γ t ∈ (chartAt H (γ τ)).source := by
    intro k hk
    obtain ⟨τ, hτ⟩ := hδ _ (hmid_mem k hk)
    refine ⟨τ, fun t ht => ?_⟩
    have htball : t ∈ Metric.ball ((k * L / N + (k + 1) * L / N) / 2) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      obtain ⟨htl, htr⟩ := ht
      -- `(k+1)L/N - kL/N = L/N < δ`; `t` within the closed interval, midpoint centre.
      have hwidth : ((k : ℝ) + 1) * L / N - (k : ℝ) * L / N = L / N := by
        field_simp; ring
      have hmid_lo : (k * L / N + (k + 1) * L / N) / 2 - t ≤ L / N := by
        have : (k * L / N + (k + 1) * L / N) / 2 ≤ ((k : ℝ) + 1) * L / N := by linarith
        nlinarith [htl, this, hwidth]
      have hmid_hi : t - (k * L / N + (k + 1) * L / N) / 2 ≤ L / N := by
        have : (k : ℝ) * L / N ≤ (k * L / N + (k + 1) * L / N) / 2 := by linarith
        nlinarith [htr, this, hwidth]
      have habs : |t - (k * L / N + (k + 1) * L / N) / 2| ≤ L / N := by
        rw [abs_le]; constructor <;> linarith
      exact lt_of_le_of_lt habs hmesh
    have := hτ htball
    simp only [hc_def, Set.mem_preimage] at this
    exact this
  -- Assemble the basepoint function via choice.
  choose! tp htp using hchoose
  exact ⟨N, fun k => γ (tp k), hN_pos, fun k hk t ht => htp k hk t ht⟩

/-! ### Continuity of the chart-curve on a chart-source piece

A small helper: when `γ` stays inside the chart source of `α` on a compact
interval, the chart-curve `extChartAt I α ∘ γ` and its velocity are
continuous there — the input regularity the single-chart ODE primitive
`parallel_local_existence_on_Icc` consumes. -/

/-- The chart-curve `chartCurve α γ` is continuous on a compact interval on
which `γ` stays inside the chart source of `α`. -/
theorem chartCurve_continuousOn_of_mapsTo
    (α : M) (γ : ℝ → M) (hγ : Continuous γ) {a b : ℝ}
    (hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b) := by
  have hφ : ContinuousOn (extChartAt I α) (extChartAt I α).source :=
    continuousOn_extChartAt (I := I) α
  have hmaps : Set.MapsTo γ (Set.Icc a b) (extChartAt I α).source := by
    intro t ht
    rw [extChartAt_source (I := I) α]
    exact hsrc t ht
  exact hφ.comp hγ.continuousOn hmaps

/-! ### Single-piece parallel transport as a bundle section

On a compact sub-interval `[a, b]` on which `γ` stays in one chart source
`α`, the single-chart `parallel_local_existence_on_Icc` produces an
`E`-valued solution `Y` of the chart-`α` parallel-transport ODE with
prescribed value at `a`. Wrapping `Y` through the inverse trivialisation
`(triv α).symmL (γ s)` turns it into a genuine fibre-valued section
`s ↦ V s ∈ T_{γ s} M` that is parallel — in the intrinsic moving-foot
sense — at every interior point of `[a, b]`. -/

/-- **Single-piece existence of an intrinsically-parallel bundle section.**
On a compact interval `[a, b]` with `a < b` on which `γ` (smooth) stays in
the chart source of `α`, given any initial fibre vector `v₀ ∈ T_{γ a} M`,
there is a fibre-valued section `V : ∀ t, T_{γ t} M` with `V a = v₀` whose
chart-`(γ t)`-coordinate representation is differentiable at every
`t ∈ Ioo a b`, whose intrinsic covariant derivative vanishes on `Ioo a b`,
and which preserves the genuine Riemannian inner product of two such sections
across `[a, b]`. The section's fibre value is `(triv α).symmL (γ s)` of the
single-chart ODE solution `Y s`. -/
theorem exists_piece_parallel_section [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Set.Icc a b)
    (hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : TangentSpace I (γ t₀)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V t₀ = v₀ ∧
      (∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo a b, covDerivAlong (I := I) g γ V t = 0) := by
  classical
  -- Velocity of the chart-α curve.
  set uPrime : ℝ → E := fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t with huPrime_def
  -- Continuity inputs for the single-chart ODE primitive.
  have hcurveCont : ContinuousOn (AlongCurve.chartCurve (I := I) α γ) (Set.Icc a b) :=
    chartCurve_continuousOn_of_mapsTo (I := I) α γ hγ.continuous hsrc
  -- The chart-α curve is `C^∞` on the open neighbourhood `U` where `γ` is in source.
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
  have hUcd : ContDiffOn ℝ ∞ (AlongCurve.chartCurve (I := I) α γ) U := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      exact hφ.comp hγ.contMDiffOn (fun s hs => hs)
    have hfun : (AlongCurve.chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  -- `uPrime` is continuous on `Icc a b` (⊆ U).
  have hIcc_sub_U : Set.Icc a b ⊆ U := fun t ht => hsrc t ht
  have huPrimeCont : ContinuousOn uPrime (Set.Icc a b) := by
    have hderiv_cd : ContDiffOn ℝ ∞ (deriv (AlongCurve.chartCurve (I := I) α γ)) U :=
      hUcd.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
    exact (hderiv_cd.continuousOn).mono hIcc_sub_U
  -- `γ t₀ ∈ chart source`; the chart-α coordinate of `v₀`.
  have hγa_src : γ t₀ ∈ (chartAt H α).source := hsrc t₀ ht₀
  -- Initial value for the chart-α ODE: the chart-α coordinate of `v₀`.
  set y₀ : E := (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t₀) v₀ with hy₀_def
  -- The single-chart ODE solution `Y` on `[a, b]`.
  obtain ⟨Y, hY_deriv, hY_init⟩ :=
    parallel_local_existence_on_Icc (I := I) g α γ uPrime hab.le ht₀
      huPrimeCont hcurveCont hsrc y₀
  -- The fibre-valued section: invert the trivialisation at the foot `γ s`.
  set V : ∀ t, TangentSpace I (γ t) := fun s =>
    (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Y s) with hV_def
  -- ### Shared infrastructure.
  -- `Icc a b ∈ 𝓝 t` for `t ∈ Ioo a b`, so `HasDerivWithinAt (Icc)` upgrades to `HasDerivAt`.
  have hIccNhds : ∀ t ∈ Set.Ioo a b, Set.Icc a b ∈ 𝓝 t := fun t ht =>
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  -- The chart-α curve has `HasDerivAt (uPrime t) t` at interior points.
  have hcurveDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (AlongCurve.chartCurve (I := I) α γ) (uPrime t) t := by
    intro t ht
    have ht_U : t ∈ U := hIcc_sub_U (Set.mem_Icc_of_Ioo ht)
    have : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hUcd.differentiableOn (by simp) t ht_U).differentiableAt (hU_open.mem_nhds ht_U)
    exact this.hasDerivAt
  -- `Y` is parallel in the chart at `α` on `Ioo a b`.
  have hY_par_Ioo : IsParallelChart (I := I) g α γ uPrime Y (Set.Ioo a b) := by
    refine ⟨fun t ht => hcurveDeriv t ht, ?_⟩
    intro t ht
    have hd := (hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)
    simpa using hd
  -- The moving-foot chart rep equals the transition-push of `Y` near each `t ∈ Ioo a b`.
  have hrep_eq : ∀ t ∈ Set.Ioo a b,
      chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
        (fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
          (AlongCurve.chartCurve (I := I) α γ s) (Y s)) := by
    intro t ht
    -- Near `t`, `γ s` lies in both chart sources of `α` and `γ t`.
    set W : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H (γ t)).source) with hW_def
    have hW_open : IsOpen W :=
      ((chartAt H α).open_source.inter (chartAt H (γ t)).open_source).preimage hγ.continuous
    have htW : t ∈ W := ⟨hsrc t (Set.mem_Icc_of_Ioo ht), mem_chart_source H (γ t)⟩
    filter_upwards [hW_open.mem_nhds htW] with s hs
    obtain ⟨hsα, hsβ⟩ := hs
    rw [chartRepAt_apply, hV_def]
    simp only
    rw [trivCoord_comp_symmL_eq_chartTransitionAt (I := I) α (γ t) hsα hsβ (Y s)]
    rw [AlongCurve.chartCurve_def]
  refine ⟨V, ?_, ?_, ?_⟩
  · -- `V t₀ = v₀`: `symmL (γ t₀) (Y t₀) = symmL (γ t₀) (y₀) = v₀`.
    rw [hV_def]
    simp only
    rw [hY_init, hy₀_def]
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hγa_src
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase v₀
  · -- Differentiability of the moving-foot chart rep at interior points.
    intro t ht
    -- Transfer to the transition-push representation, differentiable by chain/product rule.
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ (hrep_eq t ht))
    -- `s ↦ chartTransitionAt α (γt) (chartCurve α γ s) (Y s)` is differentiable at `t`.
    set Tαβ : E → (E →L[ℝ] E) := fun x => Geodesic.chartTransitionAt (I := I) α (γ t) x
      with hTαβ_def
    -- `chartTransitionAt` is smooth on the transition source, which contains `chartCurve α γ t`.
    have hsrc_t : AlongCurve.chartCurve (I := I) α γ t ∈
        Geodesic.chartTransitionSource (I := I) α (γ t) :=
      Geodesic.extChartAt_mem_chartTransitionSource (I := I) α (γ t)
        (hsrc t (Set.mem_Icc_of_Ioo ht)) (mem_chart_source H (γ t))
    have hTopen : IsOpen (Geodesic.chartTransitionSource (I := I) α (γ t)) :=
      Geodesic.chartTransitionSource_isOpen (I := I) α (γ t)
    have hTdiff : DifferentiableAt ℝ Tαβ (AlongCurve.chartCurve (I := I) α γ t) :=
      ((Geodesic.chartTransitionAt_smooth (I := I) α (γ t)).contDiffAt
        (hTopen.mem_nhds hsrc_t)).differentiableAt (by simp)
    -- `chartCurve α γ` is differentiable at `t`; `Y` is differentiable at `t`.
    have hcurve_diff : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hcurveDeriv t ht).differentiableAt
    have hY_diff : DifferentiableAt ℝ Y t :=
      ((hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)).differentiableAt
    -- The CLM-valued map `s ↦ Tαβ (chartCurve α γ s)` is differentiable at `t`.
    have hTcomp_diff : DifferentiableAt ℝ
        (fun s => (Tαβ (AlongCurve.chartCurve (I := I) α γ s) : E →L[ℝ] E)) t :=
      hTdiff.comp t hcurve_diff
    -- Apply the bilinear CLM-application differentiability.
    exact hTcomp_diff.clm_apply hY_diff
  · -- Intrinsic covariant derivative vanishes at interior points.
    intro t ht
    -- Reduce to the chart-`(γ t)` covariant derivative.
    rw [covDerivAlong_eq_zero_iff (I := I) g γ V t]
    -- Work on a small open neighbourhood `o ⊆ Ioo a b` on which `γ` is in both
    -- chart sources (`α` and `γ t`).
    set o : Set ℝ := Set.Ioo a b ∩ γ ⁻¹' (chartAt H (γ t)).source with ho_def
    have ho_open : IsOpen o :=
      isOpen_Ioo.inter ((chartAt H (γ t)).open_source.preimage hγ.continuous)
    have hto : t ∈ o := ⟨ht, mem_chart_source H (γ t)⟩
    have ho_sub : o ⊆ Set.Ioo a b := fun s hs => hs.1
    -- On `o`, `γ s` is in both chart sources.
    have hoverlap : ∀ s ∈ o, γ s ∈ (chartAt H α).source ∩ (chartAt H (γ t)).source :=
      fun s hs => ⟨hsrc s (Set.mem_Icc_of_Ioo (ho_sub hs)), hs.2⟩
    -- `Y` is parallel in chart `α` on `o`.
    have hY_par_o : IsParallelChart (I := I) g α γ uPrime Y o :=
      ⟨fun s hs => hY_par_Ioo.1 s (ho_sub hs), fun s hs => hY_par_Ioo.2 s (ho_sub hs)⟩
    -- The transition-pushed representation is parallel in the chart at `γ t` on `o`.
    have hpush_par := parallel_chart_overlap_consistency (I := I) g α (γ t) γ hγ.continuous
      uPrime Y o hoverlap hY_par_o
    -- The pushed velocity equals `deriv (chartCurve (γ t) γ)` pointwise on `o`.
    set Yβ : ℝ → E := fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
      (AlongCurve.chartCurve (I := I) α γ s) (Y s) with hYβ_def
    have hvel_eq : ∀ s ∈ o,
        deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s =
          Geodesic.chartTransitionAt (I := I) α (γ t)
            (AlongCurve.chartCurve (I := I) α γ s) (uPrime s) := by
      intro s hs
      exact (hpush_par.1 s hs).deriv
    -- Rewrite the push's `IsParallelChart` to the canonical foot velocity.
    have hpush_par' : IsParallelChart (I := I) g (γ t) γ
        (fun s => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s) Yβ o := by
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · have h1 := hpush_par.1 s hs
        simp only []
        rw [hvel_eq s hs]; exact h1
      · have h2 := hpush_par.2 s hs
        simp only [hvel_eq s hs]
        exact h2
    -- The centered foot bridge: `chartCovDerivAlong g (γ t) γ Yβ t = 0`.
    -- (Inlined: the parallel-transport ODE at `t` gives `deriv Yβ t = -Γ(…)`,
    --  which cancels the Christoffel term of `chartCovDerivAlong`.)
    have hYβ_zero : chartCovDerivAlong (I := I) g (γ t) γ Yβ t = 0 := by
      have hd := hpush_par'.hasDerivAt hto
      rw [chartCovDerivAlong_def, hd.deriv]
      abel
    -- `chartRepAt γ V t =ᶠ Yβ` near `t`, so their chart covariant derivatives agree at `t`.
    have hrep_eqβ : chartRepAt (I := I) γ V t =ᶠ[𝓝 t] Yβ := hrep_eq t ht
    -- `chartCovDerivAlong` depends only on `deriv X t` and `X t`, both local in `X`.
    have hgoal : chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t =
        chartCovDerivAlong (I := I) g (γ t) γ Yβ t := by
      rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
      rw [hrep_eqβ.deriv_eq, hrep_eqβ.eq_of_nhds]
    rw [hgoal, hYβ_zero]

/-! ### Inner-product preservation for intrinsically-parallel sections

Two sections `V`, `W` along `γ` whose intrinsic covariant derivatives vanish
on `Icc lo hi` (and whose chart representations are differentiable there)
preserve the genuine Riemannian inner product `g(γ t)(V t, W t)`: it is
constant in `t`, equal to its value at `lo`. This is the metric-compatibility
constancy argument, with both covariant-correction terms vanishing because
both sections are parallel. -/

set_option linter.unusedVariables false in
/-- **Global parallel transport preserves the inner product.** If two sections
`V`, `W` along the smooth curve `γ` have vanishing intrinsic covariant
derivative `covDerivAlong g γ · = 0` on `Icc lo hi` and differentiable
chart-`(γ t)`-coordinate representations there, then the genuine Riemannian
inner product `t ↦ g(γ t)(V t, W t)` is constant on `Icc lo hi` (equal to its
value at `lo`). -/
theorem global_parallel_transport_preserves_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {lo hi : ℝ} (hlohi : lo ≤ hi)
    (V W : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hWdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t)
    (hVpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ V t = 0)
    (hWpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ W t = 0) :
    ∀ t ∈ Set.Icc lo hi,
      g.inner (γ t) (V t) (W t) = g.inner (γ lo) (V lo) (W lo) := by
  classical
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t) (W t) with hf_def
  -- At every `t₀ ∈ Icc lo hi`, `f` has derivative `0` (chart pinned at the foot `γ t₀`).
  have hlocal : ∀ t₀ ∈ Set.Icc lo hi, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set Wrep : ℝ → E := chartRepAt (I := I) γ W t₀ with hWrep_def
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t₀)
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
    -- Round trips for `V` and `W` near `t₀`.
    have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
      intro s hs
      simpa [hVrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (V s)
    have hWround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s) = W s := by
      intro s hs
      simpa [hWrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (W s)
    -- `f` agrees with the chart-Gram form of `Vrep`, `Wrep` near `t₀`.
    have hf_eq : f =ᶠ[𝓝 t₀]
        fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s := by
      filter_upwards [hsrc_mem] with s hs
      have hVs := hVround s hs
      have hWs := hWround s hs
      have hfs : f s = g.inner (γ s)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s)) := by
        rw [hf_def]; rw [hVs, hWs]
      rw [hfs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (Wrep s)]
      rw [AlongCurve.chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
        rw [chartCurve_def]
        refine (extChartAt I α).left_inv ?_
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        rw [TangentBundle.trivializationAt_baseSet] at hs
        exact hs
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
    -- The chart trajectory has the prescribed velocity at `t₀`, in the interior of the target.
    have hu_hasDerivAt : HasDerivAt (chartCurve (I := I) α γ)
        (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ ∞ (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (γ t₀) :=
            contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by simp)).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ := (hVdiff t₀ ht₀).hasDerivAt
    have hWrep_hasDerivAt : HasDerivAt Wrep (deriv Wrep t₀) t₀ := (hWdiff t₀ ht₀).hasDerivAt
    -- The chart-Gram form has derivative `0` at `t₀` by the covariant product rule.
    have hgram := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep Wrep
      (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
      (Vprime := fun _ => deriv Vrep t₀)
      (Wprime := fun _ => deriv Wrep t₀)
      hu_hasDerivAt hmem_int hVrep_hasDerivAt hWrep_hasDerivAt
    -- Both covariant-correction terms vanish because both sections are parallel.
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this; exact this
    have hcorrW :
        deriv Wrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Wrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Wrep t₀ = 0 := by
        rw [hα_def, hWrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ W t₀).mp (hWpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this; exact this
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s) 0 t₀ := by
      convert hgram using 1
      simp only [hcorrV, hcorrW]
      simp
    exact hderiv0.congr_of_eventuallyEq hf_eq
  -- `f` continuous, zero right-derivative, hence constant on `Icc lo hi`.
  have hcont : ContinuousOn f (Set.Icc lo hi) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico lo hi, HasDerivWithinAt f 0 (Set.Ici x) x :=
    fun x hx => (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  have hconst : ∀ x ∈ Set.Icc lo hi, f x = f lo :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  intro t ht
  exact hconst t ht

/-! ### Intrinsic uniqueness of parallel transport

Two intrinsically-parallel sections that agree at one point of `Icc lo hi` agree
everywhere on `Icc lo hi`. The mechanism is metric compatibility together with
positive-definiteness: the difference `D := V - W` is itself parallel (covariant
derivative is ℝ-linear), so its squared `g`-length is constant; vanishing at the
agreement point forces `D ≡ 0`. -/

/-- **Intrinsic uniqueness of parallel transport.** If `V` and `W` are sections
along the smooth curve `γ` with vanishing intrinsic covariant derivative on
`Icc lo hi` and differentiable chart representations there, and `V t₀ = W t₀` for
some `t₀ ∈ Icc lo hi`, then `V t = W t` for every `t ∈ Icc lo hi`. -/
theorem parallel_transport_unique_of_agree [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {lo hi : ℝ} (hlohi : lo ≤ hi)
    (V W : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hWdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t)
    (hVpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ V t = 0)
    (hWpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ W t = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc lo hi) (hagree : V t₀ = W t₀) :
    ∀ t ∈ Set.Icc lo hi, V t = W t := by
  classical
  -- The difference section `D := V - W`.
  set D : ∀ t, TangentSpace I (γ t) := fun s => V s - W s with hD_def
  -- `D = V + (-1) • W`; its chart rep is differentiable, and it is parallel.
  have hDdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ D t) t := by
    intro t ht
    have heq : chartRepAt (I := I) γ D t =
        fun s => chartRepAt (I := I) γ V t s - chartRepAt (I := I) γ W t s := by
      funext s; rw [hD_def]; simp only [chartRepAt_apply, map_sub]
    rw [heq]
    exact (hVdiff t ht).sub (hWdiff t ht)
  have hDpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ D t = 0 := by
    intro t ht
    -- `D s = V s + (-1 : ℝ) • W s`.
    have hDfun : D = fun s => V s + ((-1 : ℝ) • W s) := by
      funext s; rw [hD_def]; simp [sub_eq_add_neg]
    rw [hDfun]
    have hWsmul_diff : DifferentiableAt ℝ
        (chartRepAt (I := I) γ (fun s => (-1 : ℝ) • W s) t) t := by
      have heq : chartRepAt (I := I) γ (fun s => (-1 : ℝ) • W s) t =
          fun s => (-1 : ℝ) • chartRepAt (I := I) γ W t s := by
        funext s; simp only [chartRepAt_apply, map_smul]
      rw [heq]; exact (hWdiff t ht).const_smul (-1 : ℝ)
    rw [covDerivAlong_add (I := I) g γ V (fun s => (-1 : ℝ) • W s) t (hVdiff t ht) hWsmul_diff]
    rw [covDerivAlong_smul (I := I) g γ (-1 : ℝ) W t]
    rw [hVpar t ht, hWpar t ht]
    simp
  -- The squared `g`-length of `D` is constant, hence `0` everywhere (since `D t₀ = 0`).
  have hDt₀ : D t₀ = 0 := by rw [hD_def]; simp only; rw [hagree]; abel
  have hconst := global_parallel_transport_preserves_inner (I := I) g γ hγ hlohi D D
    hDdiff hDdiff hDpar hDpar
  intro t ht
  -- `g.inner (γ t) (D t) (D t) = g.inner (γ lo) (D lo) (D lo)`... pin to `t₀`.
  have hzero_t₀ : g.inner (γ t₀) (D t₀) (D t₀) = 0 := by
    rw [hDt₀]; simp
  -- `g.inner (γ t) (D t) (D t) = g.inner (γ lo) (D lo) (D lo) = g.inner (γ t₀) (D t₀) (D t₀)`.
  have hval_t : g.inner (γ t) (D t) (D t) = g.inner (γ lo) (D lo) (D lo) := hconst t ht
  have hval_t₀ : g.inner (γ t₀) (D t₀) (D t₀) = g.inner (γ lo) (D lo) (D lo) := hconst t₀ ht₀
  have hDt_sq : g.inner (γ t) (D t) (D t) = 0 := by
    rw [hval_t, ← hval_t₀, hzero_t₀]
  -- Positive-definiteness: squared length `0` forces `D t = 0`.
  have hDt : D t = 0 := by
    by_contra hne
    exact absurd hDt_sq (ne_of_gt (g.pos (γ t) (D t) hne))
  -- Conclude `V t = W t`.
  have : V t - W t = 0 := hDt
  rw [sub_eq_zero] at this
  exact this

/-- **Locality of the chart representation.** If two sections agree on a
neighbourhood of `t`, their chart-`(γ t)`-coordinate representations agree on a
neighbourhood of `t`. -/
theorem chartRepAt_eventuallyEq_of_eventuallyEq (γ : ℝ → M)
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ W t := by
  filter_upwards [h] with s hs
  rw [chartRepAt_apply, chartRepAt_apply, hs]

/-- **Locality of the intrinsic covariant derivative.** If two sections agree on
a neighbourhood of `t`, their intrinsic covariant derivatives at `t` coincide. -/
theorem covDerivAlong_congr_of_eventuallyEq (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    covDerivAlong (I := I) g γ V t = covDerivAlong (I := I) g γ W t := by
  have hrep := chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ h
  rw [covDerivAlong_def, covDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [hrep.deriv_eq, hrep.eq_of_nhds]

/-- **Uniform chart radius along a curve.** For a continuous curve `γ` and
`L > 0`, there is a radius `r > 0` such that for every `t ∈ Icc 0 L` some chart
basepoint `α` has `γ` inside its source on the whole window `[t - r, t + r]`.
This is the Lebesgue number of the chart-source cover of the compact curve
image over the slightly enlarged interval `[-1, L + 1]`. -/
theorem exists_uniform_chart_radius
    (γ : ℝ → M) (hγ : Continuous γ) (L : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ α : M,
      ∀ s ∈ Set.Icc (t - r) (t + r), γ s ∈ (chartAt H α).source := by
  classical
  set c : ℝ → Set ℝ := fun τ => γ ⁻¹' (chartAt H (γ τ)).source with hc_def
  have hc_open : ∀ τ, IsOpen (c τ) := fun τ => (chartAt H (γ τ)).open_source.preimage hγ
  have hcover : Set.Icc (-1 : ℝ) (L + 1) ⊆ ⋃ τ, c τ := by
    intro x _hx
    exact Set.mem_iUnion.2 ⟨x, by simp only [hc_def, Set.mem_preimage]; exact mem_chart_source H (γ x)⟩
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc (a := (-1 : ℝ)) (b := L + 1)) hc_open hcover
  refine ⟨min (δ / 2) 1, lt_min (by positivity) one_pos, ?_⟩
  intro t ht
  -- `t ∈ Icc 0 L ⊆ Icc (-1) (L+1)`.
  have ht_in : t ∈ Set.Icc (-1 : ℝ) (L + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨τ, hτ⟩ := hδ t ht_in
  refine ⟨γ τ, fun s hs => ?_⟩
  have hsball : s ∈ Metric.ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    obtain ⟨hsl, hsr⟩ := hs
    have hr_le : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
    have habs : |s - t| ≤ min (δ / 2) 1 := by
      rw [abs_le]; constructor <;> linarith
    have : |s - t| ≤ δ / 2 := le_trans habs hr_le
    linarith [this]
  have := hτ hsball
  simp only [hc_def, Set.mem_preimage] at this
  exact this

/-! ### Global parallel transport on a compact interval

Assembling the single-chart pieces into one globally-defined parallel section.
The construction proceeds by induction on the partition: at each step the
section already built on `[0, sₖ]` is extended over the next chart-piece, the
overlap pinned by `parallel_transport_unique_of_agree`. Because every point of
`Icc 0 L` lies in the open interior of some chart-piece, the intrinsic
parallelism and chart-rep differentiability hold at every `t ∈ Icc 0 L`. -/

/-- **Existence of global parallel transport on `Icc 0 L`.** For a smooth curve
`γ`, `L > 0`, and any initial tangent vector `v₀ ∈ T_{γ 0} M`, there is a
fibre-valued section `V : ∀ t, T_{γ t} M` along `γ` with `V 0 = v₀`, whose
chart-`(γ t)`-coordinate representation is differentiable at every
`t ∈ Icc 0 L`, and whose intrinsic covariant derivative vanishes on `Icc 0 L`.

The section is glued from single-chart parallel-transport solutions
(`exists_piece_parallel_section`) across a uniform chart cover of the compact
curve image (`exists_uniform_chart_radius`), with uniqueness
(`parallel_transport_unique_of_agree`) ensuring consistency across overlaps.

The construction is a `Nat.rec` over reach times `c n := min L (n · r/4)`: given
the section already parallel on the open window `Ioo (-step) (c n + step)`, the
next step solves a chart-piece centred at `c n` on `[c n - step, c n + 2 step]`
(within a single chart by the uniform radius), pins the overlap
`[c n - step/2, c n]` by `parallel_transport_unique_of_agree`, and glues with an
`if t ≤ c n` cut; the locality of `chartRepAt` / `covDerivAlong` then transfers
differentiability and parallelism to the extended window. Termination is reached
once `n · step ≥ L`, where the window covers `Icc 0 L`. -/
theorem exists_global_parallel_transport_on_Icc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ,ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, covDerivAlong (I := I) g γ V t = 0) := by
  classical
  -- Uniform chart radius `r`; step `= r / 4`.
  obtain ⟨r, hr_pos, hr⟩ := exists_uniform_chart_radius (H := H) γ hγ.continuous L
  set step : ℝ := r / 4 with hstep_def
  have hstep_pos : 0 < step := by rw [hstep_def]; positivity
  -- Reach after `n` steps (capped at `L`).
  set c : ℕ → ℝ := fun n => min L (n * step) with hc_def
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => le_min hL.le (by positivity)
  have hc_le : ∀ n, c n ≤ L := fun n => min_le_left _ _
  have hc_mono : ∀ n, c n ≤ c (n + 1) := by
    intro n
    have hstep : c n = min L ((n : ℝ) * step) := rfl
    have hstep1 : c (n + 1) = min L (((n : ℝ) + 1) * step) := by
      rw [hc_def]; push_cast; ring_nf
    rw [hstep, hstep1]
    refine le_min (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
    have : (n : ℝ) * step ≤ ((n : ℝ) + 1) * step := by nlinarith [hstep_pos]
    exact this
  -- If `c n = L` then `c (n+1) = L`.
  have hc_stuck : ∀ n, c n = L → c (n + 1) = L := fun n hn =>
    le_antisymm (hc_le (n + 1)) (hn ▸ hc_mono n)
  -- The inductive predicate: a parallel section on `Ioo (-step) (c n + step)`.
  set Q : ℕ → Prop := fun n => ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Ioo (-step) (c n + step),
        DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo (-step) (c n + step), covDerivAlong (I := I) g γ V t = 0)
    with hQ_def
  -- A single chart-piece centred at a point `p ∈ Icc 0 L`, valid on `Ioo (p-step) (p+2 step)`.
  have hpiece : ∀ p ∈ Set.Icc (0 : ℝ) L, ∀ w : TangentSpace I (γ p),
      ∃ Vp : ∀ t, TangentSpace I (γ t), Vp p = w ∧
        (∀ t ∈ Set.Ioo (p - step) (p + 2 * step),
          DifferentiableAt ℝ (chartRepAt (I := I) γ Vp t) t) ∧
        (∀ t ∈ Set.Ioo (p - step) (p + 2 * step),
          covDerivAlong (I := I) g γ Vp t = 0) := by
    intro p hp w
    obtain ⟨α, hα⟩ := hr p hp
    -- The piece interval `[p - step, p + 2 step]` is inside `[p - r, p + r]`.
    have hsub : Set.Icc (p - step) (p + 2 * step) ⊆ Set.Icc (p - r) (p + r) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : p - r ≤ p - step := by rw [hstep_def]; linarith [hr_pos]
        linarith [hs.1]
      · have : p + 2 * step ≤ p + r := by rw [hstep_def]; linarith [hr_pos]
        linarith [hs.2]
    have hsrc' : ∀ t ∈ Set.Icc (p - step) (p + 2 * step), γ t ∈ (chartAt H α).source :=
      fun t ht => hα t (hsub ht)
    have hlt : p - step < p + 2 * step := by linarith [hstep_pos]
    have hp_mem : p ∈ Set.Icc (p - step) (p + 2 * step) := ⟨by linarith [hstep_pos], by linarith [hstep_pos]⟩
    obtain ⟨Vp, hVp_init, hVp_diff, hVp_par⟩ :=
      exists_piece_parallel_section (I := I) g α γ hγ hlt hp_mem hsrc' w
    exact ⟨Vp, hVp_init, hVp_diff, hVp_par⟩
  -- ### Base case: `Q 0`.
  have hc0 : c 0 = 0 := by
    change min L ((0 : ℕ) * step) = 0
    rw [Nat.cast_zero, zero_mul]; exact min_eq_right hL.le
  have hQ0 : Q 0 := by
    have h0L : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, hL.le⟩
    obtain ⟨V0, hV0_init, hV0_diff, hV0_par⟩ := hpiece 0 h0L v₀
    refine ⟨V0, hV0_init, ?_, ?_⟩
    · intro t ht
      rw [hc0] at ht
      refine hV0_diff t ⟨by linarith [ht.1], by linarith [ht.2, hstep_pos]⟩
    · intro t ht
      rw [hc0] at ht
      refine hV0_par t ⟨by linarith [ht.1], by linarith [ht.2, hstep_pos]⟩
  -- ### Inductive step: `Q n → Q (n+1)`.
  have hQstep : ∀ n, Q n → Q (n + 1) := by
    intro n hn
    obtain ⟨Vn, hVn_init, hVn_diff, hVn_par⟩ := hn
    -- If already at `L`, the predicate is unchanged.
    by_cases hcL : c n = L
    · have hcn1L : c (n + 1) = L := hc_stuck n hcL
      refine ⟨Vn, hVn_init, ?_, ?_⟩
      · intro t ht
        refine hVn_diff t ⟨ht.1, ?_⟩
        rw [hcn1L] at ht; rw [hcL]; exact ht.2
      · intro t ht
        refine hVn_par t ⟨ht.1, ?_⟩
        rw [hcn1L] at ht; rw [hcL]; exact ht.2
    · -- Genuine extension. `c n < L`, so `c n = n * step`.
      have hcn_lt : c n < L := lt_of_le_of_ne (hc_le n) hcL
      have hcn_def : c n = min L ((n : ℝ) * step) := rfl
      have hns_lt : (n : ℝ) * step < L := by
        have : min L ((n : ℝ) * step) < L := by rw [← hcn_def]; exact hcn_lt
        rcases min_lt_iff.mp this with h | h
        · exact absurd h (lt_irrefl _)
        · exact h
      have hcn_eq : c n = (n : ℝ) * step := by
        rw [hcn_def]; exact min_eq_right (le_of_lt hns_lt)
      have hcn_mem : c n ∈ Set.Icc (0 : ℝ) L := ⟨hc_nonneg n, hc_le n⟩
      -- The centred piece at `c n` with the value `Vn (c n)`.
      obtain ⟨Vp, hVp_init, hVp_diff, hVp_par⟩ := hpiece (c n) hcn_mem (Vn (c n))
      -- Overlap interval `[c n - step/2, c n]`, where both `Vn` and `Vp` are parallel + diff.
      set ov_lo : ℝ := c n - step / 2 with hov_lo
      have hov_lo_lt : ov_lo ≤ c n := by rw [hov_lo]; linarith [hstep_pos]
      have hVn_dom : Set.Icc ov_lo (c n) ⊆ Set.Ioo (-step) (c n + step) := by
        intro s hs
        rw [hov_lo] at hs
        refine ⟨by linarith [hs.1, hstep_pos, hc_nonneg n], by linarith [hs.2, hstep_pos]⟩
      have hVp_dom : Set.Icc ov_lo (c n) ⊆ Set.Ioo (c n - step) (c n + 2 * step) := by
        intro s hs
        rw [hov_lo] at hs
        refine ⟨by linarith [hs.1, hstep_pos], by linarith [hs.2, hstep_pos]⟩
      -- Uniqueness on the overlap: `Vn = Vp` there (they agree at `c n`).
      have hagree : ∀ s ∈ Set.Icc ov_lo (c n), Vn s = Vp s := by
        refine parallel_transport_unique_of_agree (I := I) g γ hγ hov_lo_lt Vn Vp
          (fun s hs => hVn_diff s (hVn_dom hs)) (fun s hs => hVp_diff s (hVp_dom hs))
          (fun s hs => hVn_par s (hVn_dom hs)) (fun s hs => hVp_par s (hVp_dom hs))
          ⟨hov_lo_lt, le_refl _⟩ ?_
        rw [hVp_init]
      -- The glued section.
      set Vc : ∀ t, TangentSpace I (γ t) := fun s => if s ≤ c n then Vn s else Vp s with hVc_def
      have hVc0 : Vc 0 = v₀ := by
        rw [hVc_def]; simp only
        rw [if_pos (by linarith [hc_nonneg n] : (0 : ℝ) ≤ c n)]
        exact hVn_init
      -- Range facts for `c (n+1)`.
      have hcast : ((n + 1 : ℕ) : ℝ) * step = (n : ℝ) * step + step := by
        push_cast; ring
      have hcn1_eq : c (n + 1) = min L ((n : ℝ) * step + step) := by
        change min L (((n + 1 : ℕ) : ℝ) * step) = min L ((n : ℝ) * step + step)
        rw [hcast]
      have hcn1_le : c (n + 1) ≤ c n + step := by
        rw [hcn1_eq, hcn_eq]; exact min_le_right _ _
      -- The glue equals `Vn` near points left of `c n`, and `Vp` near points right of `ov_lo`.
      refine ⟨Vc, hVc0, ?_, ?_⟩
      · -- Differentiability on `Ioo (-step) (c (n+1) + step)`.
        intro t ht
        by_cases htc : t < c n
        · -- Left region: `Vc =ᶠ Vn`.
          have heq : ∀ᶠ s in 𝓝 t, Vc s = Vn s := by
            filter_upwards [eventually_lt_nhds htc] with s hs
            rw [hVc_def]; simp only; rw [if_pos (le_of_lt hs)]
          rw [(chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ heq).differentiableAt_iff]
          exact hVn_diff t ⟨ht.1, by linarith [htc, hstep_pos]⟩
        · -- Right region (including the junction): `Vc =ᶠ Vp`.
          replace htc := not_lt.mp htc
          have ht_gt : ov_lo < t := by rw [hov_lo]; linarith [htc, hstep_pos]
          have heq : ∀ᶠ s in 𝓝 t, Vc s = Vp s := by
            filter_upwards [eventually_gt_nhds ht_gt] with s hs
            rw [hVc_def]; simp only
            by_cases hsc : s ≤ c n
            · rw [if_pos hsc]; exact hagree s ⟨le_of_lt hs, hsc⟩
            · rw [if_neg hsc]
          rw [(chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ heq).differentiableAt_iff]
          refine hVp_diff t ⟨by linarith [htc, hstep_pos], ?_⟩
          have : c (n + 1) + step ≤ c n + 2 * step := by linarith [hcn1_le, hstep_pos]
          linarith [ht.2, this]
      · -- Parallelism on `Ioo (-step) (c (n+1) + step)`.
        intro t ht
        by_cases htc : t < c n
        · have heq : ∀ᶠ s in 𝓝 t, Vc s = Vn s := by
            filter_upwards [eventually_lt_nhds htc] with s hs
            rw [hVc_def]; simp only; rw [if_pos (le_of_lt hs)]
          rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
          exact hVn_par t ⟨ht.1, by linarith [htc, hstep_pos]⟩
        · replace htc := not_lt.mp htc
          have ht_gt : ov_lo < t := by rw [hov_lo]; linarith [htc, hstep_pos]
          have heq : ∀ᶠ s in 𝓝 t, Vc s = Vp s := by
            filter_upwards [eventually_gt_nhds ht_gt] with s hs
            rw [hVc_def]; simp only
            by_cases hsc : s ≤ c n
            · rw [if_pos hsc]; exact hagree s ⟨le_of_lt hs, hsc⟩
            · rw [if_neg hsc]
          rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
          refine hVp_par t ⟨by linarith [htc, hstep_pos], ?_⟩
          have : c (n + 1) + step ≤ c n + 2 * step := by linarith [hcn1_le, hstep_pos]
          linarith [ht.2, this]
  -- ### Assemble: `Q n` for all `n`, then take `n` large enough that `c n = L`.
  have hQall : ∀ n, Q n := fun n => Nat.rec hQ0 hQstep n
  -- Choose `N` with `N * step ≥ L`.
  obtain ⟨N, hN⟩ := exists_nat_gt (L / step)
  have hN_ge : (N : ℝ) * step ≥ L := by
    rw [ge_iff_le, ← div_le_iff₀ hstep_pos]; exact le_of_lt hN
  have hcN : c N = L := by
    rw [hc_def]; exact min_eq_left hN_ge
  obtain ⟨V, hV_init, hV_diff, hV_par⟩ := hQall N
  rw [hcN] at hV_diff hV_par
  refine ⟨V, hV_init, ?_, ?_⟩
  · intro t ht
    exact hV_diff t ⟨by linarith [ht.1, hstep_pos], by linarith [ht.2, hstep_pos]⟩
  · intro t ht
    exact hV_par t ⟨by linarith [ht.1, hstep_pos], by linarith [ht.2, hstep_pos]⟩

/-! ## Parallel orthonormal frame on `(γ')⊥`

Given a unit-speed geodesic, pick an orthonormal basis of the
orthogonal complement of `γ'(0)` in `T_{γ 0} M` and parallel-transport
it. Orthogonality to `γ'` is preserved because `γ'` itself is parallel
(geodesic equation `∇_{γ'} γ' = 0`); orthonormality is preserved by
the previous theorem. -/

/-- **parallel-on-frame-perp-to-geodesic.** For a unit-speed geodesic
`γ` on `[0, L]` with velocity `uPrime t = γ'(t) := mfderiv γ t (1)`,
there is a family `e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve
I M γ` that, at every time `t ∈ [0, L]`, is

* parallel along `γ`: the moving-foot chart covariant derivative
  `chartCovDerivAlong g (γ t) γ (e i).toFun t` vanishes (the foot of the
  chart is the curve point `γ t`, matching the form consumed by the
  second-variation index-form engine);
* orthonormal: `g(γ t)((e i) t, (e j) t) = δ_{ij}`;
* perpendicular to the velocity: `g(γ t)((e i) t, uPrime t) = 0`.

The inner-product picture is uniform throughout: the orthonormality and
perpendicularity clauses use the *genuine Riemannian inner product*
`g.inner (γ t)` of the raw tangent-bundle fibre vectors (the same
`g.inner (γ t)` consumed by `sum_index_form_integrand_eval` /
`length_bound_contradiction_assembly`), while parallelism is the
*intrinsic* covariant derivative `covDerivAlong g γ (e i) t = 0` consumed by
those same engines.

The perpendicularity clause is against the *velocity* `uPrime`, not an
unconstrained function: `huPrimeEq` pins `uPrime` to the manifold
velocity `mfderiv γ t (1)` and `hUnit` records unit speed. This is the
honest statement; on a unit-speed geodesic the velocity field is itself
parallel (`∇_{γ'} γ' = 0`), so the constancy-of-inner-product argument
propagates orthogonality from `t = 0` to all of `[0, L]`.

The proof is the genuine Gram–Schmidt-of-an-orthonormal-basis-of
`(γ'(0))^⊥`-then-parallel-transport construction together with the
metric-compatibility constancy argument (already available as
`chartGramAlongCurve_hasDerivAt_zero_of_parallel` /
`parallelTransport_preserves_inner_product`) and the
`chartGramAlongCurve`-to-`g.inner` bridge
(`inner_eq_chartGramOnE_bilinear_on_baseSet`); it is left as a marked
`sorry` (Phase-3 construction). -/
theorem parallel_on_frame_perp_to_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (_hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (_hL : 0 < L)
    (uPrime : ℝ → E)
    (_huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (uPrime t) (uPrime t) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (e i).toFun t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (uPrime t) = 0) :=
  -- Missing construction: an orthonormal basis of `(γ'(0))^⊥ ⊆ T_{γ 0} M`,
  -- parallel-transported along `γ`, with the intrinsic `covDerivAlong`
  -- parallelism and `g.inner`-orthonormality/perpendicularity assembled from
  -- the metric-compatibility constancy engine and the chart-Gram-to-`g.inner`
  -- bridge. (Gram–Schmidt-then-parallel-transport.)
  sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
