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

open DifferentialGeometry.Geometry.Riemannian.Geodesic in
/-- **Coordinate of the foot-slot derivative of the transition Jacobian.**
For `x` in the chart-transition source, the `a`-th chart coordinate of the
foot-slot derivative `(fderiv (chartTransitionAt α β ·) x v) w` equals the
second-derivative sum `∑_{i,j} (∂_i J^a_j x) vⁱ wʲ`, where
`J = chartTransitionJacEntry α β`. General-basepoint analogue of the
chart-`p.proj` form used in the geodesic-spray reduction. -/
private lemma chartCoord_fderiv_chartTransitionAt_general [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β)
    (a : Fin (Module.finrank ℝ E)) (v w : E) :
    chartCoord (E := E) a
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z a j) x *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  set A : E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) α β z with hA
  have hcA : DifferentiableAt ℝ A x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
      chartTransitionSource_isOpen (I := I) α β
    have hcd : ContDiffOn ℝ ∞
        (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
        (chartTransitionSource (I := I) α β) :=
      chartTransitionAt_smooth (I := I) α β
    exact (hcd.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)
  -- The evaluation CLM `eval : (E →L E) →L ℝ`, `L ↦ chartCoord a (L w)`.
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  set eval : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp (ContinuousLinearMap.apply ℝ E w) with heval
  -- `chartCoord a ((fderiv A x v) w) = eval (fderiv A x v)`.
  have hstep1 :
      chartCoord (E := E) a ((fderiv ℝ A x v) w) = eval (fderiv ℝ A x v) := by
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    rfl
  -- `eval (fderiv A x v) = fderiv (eval ∘ A) x v` (eval is a CLM).
  have hstep2 : eval (fderiv ℝ A x v) = fderiv ℝ (fun z => eval (A z)) x v := by
    have hcomp_hasD : HasFDerivAt (fun z => eval (A z))
        (eval.comp (fderiv ℝ A x)) x :=
      eval.hasFDerivAt.comp x hcA.hasFDerivAt
    rw [hcomp_hasD.fderiv]
    rfl
  -- `eval (A z) = chartCoord a (chartTransitionAt α β z w) = ∑_j J^a_j(z) wʲ`.
  have heval_eq : (fun z => eval (A z)) =
      (fun z => ∑ j : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β z a j * chartCoord (E := E) j w) := by
    funext z
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hA,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    change chartCoord (E := E) a (chartTransitionAt (I := I) α β z w) = _
    exact chartCoord_chartTransitionAt (I := I) α β z w a
  rw [hstep1, hstep2, heval_eq]
  -- Differentiate the finite sum.
  have hsum_fderiv :
      fderiv ℝ (fun z => ∑ j : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) α β z a j * chartCoord (E := E) j w) x v =
        ∑ j : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
            chartCoord (E := E) j w) x v := by
    have hdiff : ∀ j : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
          chartCoord (E := E) j w) x := by
      intro j
      exact (chartTransitionJacEntry_differentiableAt (I := I) α β a j hx).mul_const _
    rw [fderiv_fun_sum (fun j _ => hdiff j)]
    rw [ContinuousLinearMap.sum_apply]
  rw [hsum_fderiv]
  -- Each summand: `fderiv (J^a_j · wʲ) x v = (fderiv J^a_j x v) · wʲ`,
  -- and `fderiv J^a_j x v = ∑_i vⁱ ∂_i J^a_j x`.
  have hLHS_expand :
      (∑ j : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
            chartCoord (E := E) j w) x v) =
        ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z a j) x *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fderiv_mul_const (chartTransitionJacEntry_differentiableAt (I := I) α β a j hx) _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) α β a j x v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hLHS_expand]
  -- Swap the two outer sums `∑_j ∑_i` to `∑_i ∑_j`.
  rw [Finset.sum_comm]

open DifferentialGeometry.Geometry.Riemannian.Geodesic in
/-- **Foot-slot derivative of the transition Jacobian = pushforward of the
second-derivative correction.** For `x` in the chart-transition source, the
foot-slot derivative `(fderiv (chartTransitionAt α β ·) x v) w` equals the
forward Jacobian `chartTransitionAt α β x` applied to the second-derivative
correction `chartTransitionSecondDerivCorrection α β v w x`. This is the
vector-valued cancellation identity that converts the moving-foot Jacobian
derivative into the Christoffel-transformation correction term. -/
private lemma fderiv_chartTransitionAt_apply_eq_pushCorrection [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) (v w : E) :
    (fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w =
      chartTransitionAt (I := I) α β x
        (chartTransitionSecondDerivCorrection (I := I) α β v w x) := by
  classical
  refine (chartModelBasis E).ext_elem (fun a => ?_)
  -- Both sides as chart coordinate `a`.
  change chartCoord (E := E) a
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w) =
    chartCoord (E := E) a
      (chartTransitionAt (I := I) α β x
        (chartTransitionSecondDerivCorrection (I := I) α β v w x))
  rw [chartCoord_fderiv_chartTransitionAt_general (I := I) α β hx a v w]
  -- RHS: `∑_c J^a_c(x) · chartCoord c (correction)`.
  rw [chartCoord_chartTransitionAt (I := I) α β x
    (chartTransitionSecondDerivCorrection (I := I) α β v w x) a]
  -- Coordinate `c` of the correction.
  have hcorrCoord : ∀ c : Fin (Module.finrank ℝ E),
      chartCoord (E := E) c
          (chartTransitionSecondDerivCorrection (I := I) α β v w x) =
        ∑ d : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) c d *
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z d j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w) := by
    intro c
    rw [chartTransitionSecondDerivCorrection_def, chartCoord, map_sum,
      Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply c c, if_pos rfl, mul_one]
    · intro k _ hkc
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply k c, if_neg hkc, mul_zero]
  -- Substitute the coordinate expansion of the correction.
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => chartTransitionJacEntry (I := I) α β x a c * t) (hcorrCoord c))]
  -- Now reorder so the Jacobian-collapse `∑_c J^a_c(x) J^c_d(Tx) = δ_{ad}` applies.
  set D : Fin (Module.finrank ℝ E) → ℝ := fun d =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
        (fun z => chartTransitionJacEntry (I := I) α β z d j) x *
        chartCoord (E := E) i v * chartCoord (E := E) j w with hD_def
  -- The goal is now `D a = ∑_c J^a_c(x) · (∑_d J^c_d(Tx) · D d)`.
  symm
  calc
    (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a c *
          (∑ d : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) β α
              (chartTransitionMap (I := I) α β x) c d * D d))
        = ∑ d : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α β x a c *
                chartTransitionJacEntry (I := I) β α
                  (chartTransitionMap (I := I) α β x) c d) * D d := by
          -- Distribute `J^a_c` into the inner `∑_d`, then swap the two sums.
          rw [show (∑ c : Fin (Module.finrank ℝ E),
                chartTransitionJacEntry (I := I) α β x a c *
                  (∑ d : Fin (Module.finrank ℝ E),
                    chartTransitionJacEntry (I := I) β α
                      (chartTransitionMap (I := I) α β x) c d * D d)) =
              ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                chartTransitionJacEntry (I := I) α β x a c *
                  (chartTransitionJacEntry (I := I) β α
                    (chartTransitionMap (I := I) α β x) c d * D d) from by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [Finset.mul_sum]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          ring
    _ = ∑ d : Fin (Module.finrank ℝ E),
            (if a = d then (1 : ℝ) else 0) * D d := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [chartTransitionJacEntry_mul_sum' (I := I) α β hx a d]
    _ = D a := by
          rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
          · rw [if_pos rfl, one_mul]
          · intro k _ hka
            rw [if_neg (fun h => hka h.symm), zero_mul]

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
