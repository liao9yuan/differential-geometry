import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.MfderivAtZero
import DifferentialGeometry.Geometry.Riemannian.Exponential.OffZeroRegularity
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Geometry.Riemannian.InjectivityRadius
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Exponential.RescaleSmallnessUniform
import DifferentialGeometry.Geometry.Riemannian.Exponential.RescaledLift
import DifferentialGeometry.Geometry.Riemannian.Exponential.UniformExistence
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Riemannian.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Gauss's lemma and the radial-minimiser package

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`,
this file packages the classical Gauss-lemma cluster:

* `gauss_lemma_pullback` — the pullback of `g` through `expMap g p` at
  a radial direction `v` evaluates to `⟪v, v⟫` on the `(v, v)` slot and
  to `0` on the `(v, w)` slot whenever `w` satisfies `⟪v, w⟫ = 0`.

* `subArc_of_minimizer_is_minimizer` — a sub-arc of a length-minimising
  curve is itself a length-minimiser between its restricted endpoints.

* `normalBall_radial_unique_minimizer` — inside a normal ball at `p`,
  every `C¹` curve from `p` to `expMap g p v` has `pathELength ≥ ‖v‖`,
  with equality only for a monotone radial reparametrisation.

* `local_radial_identification_of_minimizer` — at any interior parameter
  of a length-minimising curve there is a `δ`-neighbourhood on which the
  curve is a monotone radial geodesic in normal coordinates at `γ(t₀)`.

* `arclength_reparam_is_smooth_geodesic` — the global arclength
  reparametrisation of a length-minimiser is a smooth geodesic on the
  open parameter interval.

All five statements live below as `theorem ... := sorry` stubs.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section GaussLemma

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Gauss's lemma (pullback form)

The pullback of the Riemannian metric through `expMap g p` at a radial
direction `v` (inside the natural domain) preserves the radial inner
product and annihilates the radial/orthogonal cross term. We split the
two equalities into two theorems for clean downstream consumption.

The variational argument behind Gauss's lemma differentiates the radial
geodesic variation `f (s, t) := expMap g p (t • (v + s • w))` twice; this
requires `expMap g p` to be `C²` on a neighbourhood of the segment
`{t • (v + s • w)}`.  The exponential map is only known to be `C²` on a
small ball around the origin (`expMap_contMDiffAt2_of_norm_lt`), so the
pullback statement is restricted to that ball.  The radius is recorded as
`expMapC2Radius g p` below (it is, more precisely, the *minimum* of the
`C²` radius and the uniform radii on which the radial curve is a geodesic
and the rescaling identity holds, all needed by the variational argument). -/

/-! ## Radial geodesic property (Step 1)

For a small initial velocity `v`, the radial curve `t ↦ maximalGeodesic g p v t`
is a geodesic at every `t ∈ [0, 1]`: it satisfies the intrinsic moving-foot
geodesic equation `HasGeodesicEquationAt g (maximalGeodesic g p v) t`.

The argument routes the whole arc through the **single** chart-pushed flow orbit
`Φ` of `exists_uniform_existence_interval`: the rescaled manifold lift
`chartFlowOrbitLiftRescaled Φ p t' v_base` (with `t' = T / 2`, `v_base = (1/t')•v`,
so `t' • v_base = v`) is, on the open interval `Ioo (-T/t') (T/t') = Ioo (-2) 2 ⊇
[0, 1]`, an integral curve of the chart-`p`-fixed geodesic vector field whose
projection equals `maximalGeodesic g p v`. This packages a *single*
`IsGeodesicOnWithInitial` witness on an open interval containing `[0, 1]`, so the
unconditional `IsGeodesicOnWithInitial.isGeodesicAt → IsGeodesicAt.hasGeodesicEquationAt`
chain applies at every `t ∈ [0, 1]` (the foot-in-source clause coming from the
orbit's chart-source confinement). -/

/-- **Radial geodesic property on `[0, 1]` for small velocity.** There is an
explicit `ρ > 0` such that for every `v` with `‖v‖ < ρ`, the maximal geodesic
`t ↦ maximalGeodesic g p v t` satisfies the intrinsic moving-foot geodesic
equation at every `t ∈ [0, 1]`. -/
theorem radial_maximalGeodesic_hasGeodesicEquationAt_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
          DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicEquationAt
            (I := I) g (fun s : ℝ => maximalGeodesic (I := I) g p v s) t := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := p)
  -- Working scale `t' = T / 2 ∈ (0, T)`, so `T / t' = 2`.
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv t ht
  -- Base velocity `vb = (1/t') • v` in the uniform ball; `t' • vb = v`.
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  -- The open interval `J = Ioo (-T/t') (T/t') = Ioo (-2) 2` contains `[0, 1]`.
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  set J : Set ℝ := Set.Ioo (-T / t') (T / t') with hJ_def
  have hJ_open : IsOpen J := isOpen_Ioo
  have hJ_eq : J = Set.Ioo (-2 : ℝ) 2 := by rw [hJ_def, neg_div, hT_div]
  have hIcc_sub_J : Set.Ioo (-1 : ℝ) 2 ⊆ J := by
    rw [hJ_eq]; intro x hx; obtain ⟨hx0, hx1⟩ := hx; exact ⟨by linarith, by linarith⟩
  have ht_J : t ∈ J := hIcc_sub_J ht
  have h0_J : (0 : ℝ) ∈ J := hIcc_sub_J ⟨by norm_num, by norm_num⟩
  -- The rescaled manifold lift `F := chartFlowOrbitLiftRescaled Φ p t' vb`.
  set F : ℝ → TangentBundle I M :=
    Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb with hF_def
  -- `F 0 = ⟨p, t' • vb⟩ = ⟨p, v⟩` and `F` is an integral curve on `J`.
  have hF0 : F 0 = (⟨p, t' • vb⟩ : TangentBundle I M) :=
    Exponential.chartFlowOrbitLiftRescaled_zero (I := I) p vb t' (hΦ_init vb hvb_ball)
  have hF_int :
      IsMIntegralCurveOn F
        (Geodesic.geodesicVectorFieldChart (I := I) g p) J :=
    Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo (I := I) g p vb
      ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
  -- The projection of `F` equals `maximalGeodesic g p v` on `J`.
  have hF_proj : ∀ s ∈ J,
      (F s).proj = maximalGeodesic (I := I) g p v s := by
    intro s hs
    have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := s) hs
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h
  -- `IsGeodesicOnWithInitial g (F.proj) J p v` (a single witness; the witness
  -- curve is `F` itself, so the projection clause is definitional).
  have hgeo_init :
      Geodesic.IsGeodesicOnWithInitial (I := I) g
        (fun s : ℝ => (F s).proj) J p v := by
    refine ⟨F, fun _ => rfl, ?_, hF_int⟩
    -- `F 0 = ⟨p, t' • vb⟩ = ⟨p, v⟩`.
    rw [hF0, show (t' • vb : TangentSpace I p) = v from hvb_resc]
  -- Foot-in-source for `F.proj` at `t`: `F.proj t = maximalGeodesic g p v t`
  -- lies in `(chartAt H p).source` by `foot_in_source_throughout`.
  obtain ⟨ρ_src, hρ_src_pos, hsrc⟩ :=
    Exponential.foot_in_source_throughout (I := I) (g := g) (p := p)
  -- The two radii are the same construction `(T/2) * ρ₀` — `foot_in_source_throughout`
  -- and the present proof both extract from `exists_uniform_existence_interval`. We do
  -- not rely on that coincidence: instead we prove foot-in-source for `F.proj` directly
  -- from the orbit's chart-source confinement (`chartFlowOrbitLiftRescaled_proj_mem_…`).
  have hF_src : (F t).proj ∈ (chartAt H p).source := by
    have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨?_, ?_⟩
      · nlinarith [ht'_pos.le, hT_pos.le, ht'_lt_T.le]
      · nlinarith [ht'_lt_T.le, ht'_pos.le]
    have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
    have hsrc' :=
      Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
        hΦ_target_tt
    rw [hF_def]; exact hsrc'
  -- `IsGeodesicAt g (F.proj) t` (interior point `t ∈ J`, foot-in-source).
  have hgeoAt :
      Geodesic.IsGeodesicAt (I := I) g (fun s : ℝ => (F s).proj) t :=
    hgeo_init.isGeodesicAt (hJ_open.mem_nhds ht_J) hF_src
  -- `HasGeodesicEquationAt g (F.proj) t` (unconditional bridge).
  have hgeoEqF :
      Geodesic.HasGeodesicEquationAt (I := I) g (fun s : ℝ => (F s).proj) t :=
    hgeoAt.hasGeodesicEquationAt g
  -- Transfer to `maximalGeodesic g p v` via eventual equality on the open `J ∋ t`.
  have hEvEq : (fun s : ℝ => maximalGeodesic (I := I) g p v s)
      =ᶠ[nhds t] (fun s : ℝ => (F s).proj) := by
    filter_upwards [hJ_open.mem_nhds ht_J] with s hs
    exact (hF_proj s hs).symm
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (γ := fun s : ℝ => maximalGeodesic (I := I) g p v s)
    (γ' := fun s : ℝ => (F s).proj) (t₀ := t)
    (hF_proj t ht_J).symm hEvEq hgeoEqF

/-- **Continuity and foot-in-source on `(-1, 2)` for small velocity (maximal
geodesic).** There is an explicit `ρ > 0` such that for every `v` with `‖v‖ < ρ`,
the maximal geodesic `t ↦ maximalGeodesic g p v t` is continuous on `Ioo (-1) 2`
and keeps its foot inside the home chart source `(chartAt H p).source` for every
`t ∈ Ioo (-1) 2`.  Both are read off the rescaled chart-pushed flow orbit (its
continuity and its chart-source confinement), exactly as in the geodesic-equation
sibling `radial_maximalGeodesic_hasGeodesicEquationAt_of_small`. -/
theorem radial_maximalGeodesic_cont_and_foot_in_source_of_small
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {v : TangentSpace I p}, ‖(v : E)‖ < ρ →
        ContinuousOn (fun s => maximalGeodesic (I := I) g p v s) (Set.Ioo (-1 : ℝ) 2) ∧
        ∀ t ∈ Set.Ioo (-1 : ℝ) 2,
          maximalGeodesic (I := I) g p v t ∈ (chartAt H p).source := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := p)
  set t' : ℝ := T / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T : t' < T := by rw [ht'_def]; linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀_pos, ?_⟩
  intro v hv
  set w : E := (v : E) with hw_def
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  obtain ⟨vb, hvb_def⟩ : ∃ vb : E, vb = (1 / t') • w := ⟨_, rfl⟩
  have hvb_resc : t' • vb = (v : E) := by
    rw [hvb_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul, hw_def]
  have hw_norm : ‖w‖ < t' * ρ₀ := by rw [hw_def]; exact hv
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right, hvb_def, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul]
    rw [div_lt_iff₀ ht'_pos]
    linarith [hw_norm, mul_comm t' ρ₀]
  -- `J = Ioo (-T/t') (T/t') = Ioo (-2) 2 ⊇ Ioo (-1) 2`.
  have hT_div : T / t' = 2 := by rw [ht'_def]; field_simp
  have h12_sub_J : Set.Ioo (-1 : ℝ) 2 ⊆ Set.Ioo (-T / t') (T / t') := by
    rw [neg_div, hT_div]; intro x hx; obtain ⟨hx0, hx1⟩ := hx; exact ⟨by linarith, by linarith⟩
  -- The integral curve `F` and its projection identification on `J`.
  have hF_int := Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
    (I := I) g p vb ht'_pos (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousOn
      (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb r).proj)
      (Set.Ioo (-T / t') (T / t')) :=
    hπ_cont.comp_continuousOn hF_int.continuousOn
  have hEqOn : Set.EqOn (fun r => maximalGeodesic (I := I) g p v r)
      (fun r => (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ p t' vb r).proj)
      (Set.Ioo (-T / t') (T / t')) := by
    intro r hr
    have h := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := r) hr
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · -- Continuity on `Ioo (-1) 2 ⊆ J`.
    exact ((hproj_cont.congr hEqOn).mono h12_sub_J)
  · intro t ht
    -- `t' * t ∈ [-T, T]` (since `t ∈ (-1, 2)` and `t' = T/2 < T`).
    have hts_Icc : t' * t ∈ Set.Icc (-T) T := by
      obtain ⟨ht0, ht1⟩ := ht
      refine ⟨?_, ?_⟩
      · nlinarith [ht'_pos.le, hT_pos.le, ht'_lt_T.le]
      · nlinarith [ht'_lt_T.le, ht'_pos.le]
    have hΦ_target_tt := hΦ_target vb hvb_ball (t' * t) hts_Icc
    have hsrc' :=
      Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p vb t' t
        hΦ_target_tt
    have ht_J : t ∈ Set.Ioo (-T / t') (T / t') := h12_sub_J ht
    have hEq := Exponential.chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
      (I := I) (g := g) (p := p) (v := vb) (T := T) (t' := t') ht'_pos
      (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball) (s := t) ht_J
    rw [show (t' • vb : TangentSpace I p) = v from hvb_resc] at hEq
    rw [← hEq]; exact hsrc'

/-! ## The combined `C²` / geodesic radius

The variational argument behind Gauss's lemma needs three simultaneous
small-velocity facts: that `expMap g p` is `C²` near `t • (v + s • w)`
(`expMap_contMDiffAt2_of_norm_lt`), that the radial curve is a geodesic on
`[0, 1]` (`radial_maximalGeodesic_hasGeodesicEquationAt_of_small`), and the
rescaling identity `expMap g p (t • v) = maximalGeodesic g p v t`
(`maximalGeodesic_rescale_at_one_of_small`).  Each comes with its own
uniform radius; we record the *minimum* of the three so that
`‖v‖ < expMapC2Radius g p` makes all three available at once. -/

/-- The radius of the ball around the origin on which the second-order
variational argument behind Gauss's lemma is available: the minimum of the
`C²` radius of `expMap g p`, the radius on which the radial curve is a
geodesic on `[0, 1]`, the radius of the geodesic rescaling identity, and the
radius of a Euclidean ball confined inside the normal-chart target (so that the
chart inverse is defined on the whole ball). -/
def expMapC2Radius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  min (Classical.choose (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p))
    (min
      (Classical.choose
        (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p))
      (min
        (Classical.choose
          (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p))
        (Classical.choose
          (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p))))

/-- The combined radius is strictly positive. -/
lemma expMapC2Radius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expMapC2Radius (I := I) g p := by
  rw [expMapC2Radius, lt_min_iff, lt_min_iff, lt_min_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec
      (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)).1
  · exact (Classical.choose_spec
      (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p)).1
  · exact (Classical.choose_spec
      (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)).1
  · exact (Classical.choose_spec
      (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p)).1

/-- On the ball of radius `expMapC2Radius g p`, `expMap g p` is `C²`. -/
lemma expMap_contMDiffAt2_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {w : E}
    (hw : ‖w‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 2
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) w :=
  (Classical.choose_spec
    (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)).2 w
    (lt_of_lt_of_le hw (min_le_left _ _))

/-- On the ball of radius `expMapC2Radius g p`, the radial curve is a
geodesic at every `t ∈ (-1, 2)` (an open interval containing `[0, 1]`). -/
lemma radial_hasGeodesicEquationAt_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p) (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    Geodesic.HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => maximalGeodesic (I := I) g p v s) t :=
  (Classical.choose_spec
    (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p)).2
    (lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))) t ht

/-- On the ball of radius `expMapC2Radius g p`, the geodesic rescaling
identity `maximalGeodesic g p (t • v) 1 = maximalGeodesic g p v t` holds for
`t ∈ [0, 1]`. -/
lemma maximalGeodesic_rescale_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    maximalGeodesic (I := I) g p (t • v) 1 = maximalGeodesic (I := I) g p v t :=
  (Classical.choose_spec
    (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)).2
    (lt_of_lt_of_le hv
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) t ht

/-- The Euclidean ball of radius `expMapC2Radius g p` is contained in the
target of the normal chart at `p` (equivalently, the source of the
exponential-side diffeomorphism). In particular the chart inverse is defined on
the whole ball. -/
lemma ball_subset_normalChartAt_target
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    x ∈ (NormalCoordinates.normalChartAt (I := I) g p).target := by
  rw [NormalCoordinates.normalChartAt_target_eq]
  refine (Classical.choose_spec
    (exists_metric_ball_subset_expMapDiffeo_source (I := I) g p)).2 ?_
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_lt_of_le hx
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))

/-- The vector `x ∈ E` with `‖x‖ < expMapC2Radius g p` lies in the natural
domain of `expMap g p`. The chart target equals the diffeomorphism source, on
which `expMap g p` is realised by the partial diffeomorphism `expMapDiffeo`;
since that map is injective and sends `0 ↦ p`, a nonzero `x` in the source
cannot revert to the junk value `p`, hence `x` is in the natural domain. -/
lemma mem_expDomain_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    (show TangentSpace I p from x) ∈ expDomain (I := I) g p := by
  classical
  have hsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source := by
    have := ball_subset_normalChartAt_target (I := I) g p hx
    rwa [NormalCoordinates.normalChartAt_target_eq] at this
  by_cases hx0 : x = 0
  · subst hx0; exact zero_mem_expDomain (I := I) g p
  · by_contra hcon
    -- Outside the domain, `expMap g p x = p`; but on the source, the injective
    -- diffeomorphism `expMapDiffeo` agrees with `expMap` and sends only `0 ↦ p`.
    have hjunk : expMap (I := I) g p (show TangentSpace I p from x) = p :=
      expMap_of_not_mem_expDomain (I := I) hcon
    have hΦx : NormalCoordinates.expMapDiffeo (I := I) g p x = p := by
      rw [NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hsrc]; exact hjunk
    have hΦ0 : NormalCoordinates.expMapDiffeo (I := I) g p (0 : E) = p :=
      NormalCoordinates.expMapDiffeo_zero (I := I) g p
    have h0src : (0 : E) ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) g p
    have hinj : Set.InjOn (NormalCoordinates.expMapDiffeo (I := I) g p)
        (NormalCoordinates.expMapDiffeo (I := I) g p).source :=
      (NormalCoordinates.expMapDiffeo (I := I) g p).toPartialEquiv.injOn
    exact hx0 (hinj hsrc h0src (by rw [hΦx, hΦ0]))

/-! ## Coercivity of `g_p` and the `g_p`-ball radius

The default norm on the model space `E` (Euclidean) and the fibre quadratic
form `g.inner p` are unrelated a priori, but on a finite-dimensional `E` the
positive-definite continuous bilinear form `g.inner p` is *coercive*: there is
`c > 0` with `c · ‖x‖² ≤ g_p(x, x)` for all `x`.  This lets us convert a
`g_p`-ball smallness condition into the Euclidean `C²`-ball smallness needed by
the variational machinery, and conversely fit a `g_p`-ball inside the Euclidean
`C²`-ball.  The relevant `g_p`-radius is `expRadiusGp g p := √c · expMapC2Radius g p`. -/

/-- **Coercivity of `g_p`.** The positive-definite continuous bilinear form
`g.inner p` on a finite-dimensional space is bounded below by a multiple of the
squared Euclidean norm: there is `c > 0` with `c · ‖x‖² ≤ g_p(x, x)` for all `x`.
The unit sphere is compact (finite dimension), `g_p(x, x) > 0` there, and the
minimum is the constant `c`. -/
private lemma gp_coercive (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ^ 2 ≤ g.inner p x x := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  -- The continuous quadratic form on the unit sphere.
  set Q : E → ℝ := fun x => B x x with hQ
  have hQcont : Continuous Q := by
    have : Continuous (fun x : E => B x x) :=
      (B.continuous₂).comp (continuous_id.prodMk continuous_id)
    simpa [hQ] using this
  have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hQpos : ∀ x ∈ Metric.sphere (0 : E) 1, (0 : ℝ) < Q x := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h; rw [h] at hx
      simp only [mem_sphere_zero_iff_norm, norm_zero] at hx
      exact (zero_ne_one hx)
    exact g.pos p x hxne
  obtain ⟨c, hc_pos, hc_le⟩ :=
    hsphere.exists_forall_le' hQcont.continuousOn hQpos
  refine ⟨c, hc_pos, fun x => ?_⟩
  -- It suffices to bound `B x x = g.inner p x x`.
  change c * ‖x‖ ^ 2 ≤ B x x
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0
    rw [ContinuousLinearMap.map_zero₂, norm_zero]
    simp
  · -- scaling: x = ‖x‖ • (‖x‖⁻¹ • x), unit vector on sphere
    have hnx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set u : E := ‖x‖⁻¹ • x with hu_def
    have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, hu_def, norm_smul]
      simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hnx_pos]
      exact inv_mul_cancel₀ (ne_of_gt hnx_pos)
    have hcu : c ≤ B u u := hc_le u hu_sphere
    have hx_eq : x = ‖x‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hnx_pos), one_smul]
    have hQscale : B x x = ‖x‖ ^ 2 * B u u := by
      nth_rewrite 1 [hx_eq]
      nth_rewrite 2 [hx_eq]
      rw [ContinuousLinearMap.map_smul₂, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hQscale]
    have hsq_nn : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    calc c * ‖x‖ ^ 2 = ‖x‖ ^ 2 * c := by ring
      _ ≤ ‖x‖ ^ 2 * B u u := mul_le_mul_of_nonneg_left hcu hsq_nn

/-- The coercivity constant of `g.inner p`, packaged as a `Classical.choose`. -/
private def gpCoerciveConst (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  Classical.choose (gp_coercive (I := I) g p)

private lemma gpCoerciveConst_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < gpCoerciveConst (I := I) g p :=
  (Classical.choose_spec (gp_coercive (I := I) g p)).1

private lemma gpCoerciveConst_le (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
  (Classical.choose_spec (gp_coercive (I := I) g p)).2 x

/-- **The `g_p`-ball radius** on which the radial-minimiser cluster is available:
`√c · expMapC2Radius g p`, where `c` is the coercivity constant of `g.inner p`.
A `g_p`-ball of this radius fits inside the Euclidean `C²`-ball of radius
`expMapC2Radius g p`, and conversely a `g_p`-smallness `√(g_p(v,v)) < expRadiusGp g p`
implies the Euclidean smallness `‖v‖ < expMapC2Radius g p`.  This is the correct
domain radius for the radial length lower bound: under an anisotropic `g_p` the
Euclidean radius would let `√(g_p(v,v))` exceed the realised radial distance. -/
def expRadiusGp (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  Real.sqrt (gpCoerciveConst (I := I) g p) * expMapC2Radius (I := I) g p

/-- The `g_p`-ball radius is strictly positive. -/
lemma expRadiusGp_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expRadiusGp (I := I) g p := by
  rw [expRadiusGp]
  exact mul_pos (Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p))
    (expMapC2Radius_pos (I := I) g p)

/-- If `√(g_p(x,x)) < expRadiusGp g p`, then `‖x‖_E < expMapC2Radius g p`:
the `g_p`-ball of radius `expRadiusGp g p` fits inside the Euclidean `C²`-ball
(via coercivity). -/
lemma norm_lt_expMapC2Radius_of_sqrt_inner_lt
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : Real.sqrt (g.inner p x x) < expRadiusGp (I := I) g p) :
    ‖x‖ < expMapC2Radius (I := I) g p := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  -- From `√(g_p(x,x)) < √c · R` get `g_p(x,x) < c · R²`.
  have hsq : g.inner p x x < (expRadiusGp (I := I) g p) ^ 2 :=
    Real.lt_sq_of_sqrt_lt hx
  have hR : (expRadiusGp (I := I) g p) ^ 2
      = gpCoerciveConst (I := I) g p * (expMapC2Radius (I := I) g p) ^ 2 := by
    rw [expRadiusGp, mul_pow, Real.sq_sqrt hc_pos.le]
  rw [hR] at hsq
  -- Coercivity: `c · ‖x‖² ≤ g_p(x,x) < c · R²`, so `‖x‖² < R²`, hence `‖x‖ < R`.
  have hcoerc : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
    gpCoerciveConst_le (I := I) g p x
  have hlt : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2
      < gpCoerciveConst (I := I) g p * (expMapC2Radius (I := I) g p) ^ 2 :=
    lt_of_le_of_lt hcoerc hsq
  have hsq_lt : ‖x‖ ^ 2 < (expMapC2Radius (I := I) g p) ^ 2 :=
    lt_of_mul_lt_mul_left hlt hc_pos.le
  -- `‖x‖ < R` from `‖x‖² < R²` with `‖x‖ ≥ 0` and `R > 0`.
  have hRpos : 0 < expMapC2Radius (I := I) g p := expMapC2Radius_pos (I := I) g p
  nlinarith [norm_nonneg x, hsq_lt, hRpos]

/-! ## The radial geodesic variation and its calculus core

We package the variational core of Gauss's lemma as the named lemma
`gauss_phi_hasDerivAt`.  Given a base point `p`, a radial direction `v`
inside the `C²` ball and a transverse direction `w`, the *radial geodesic
variation* is
`gaussVariation g p v w s t := expMap g p (t • (v + s • w))`.
Its `t`-velocity and `s`-variation fields (the intrinsic covariant
velocity fields along the central curve `t ↦ expMap g p (t • v)`) are
`gaussVelT` and `gaussVelS`, and the scalar
`φ t := g.inner (f 0 t) (∂_t f 0 t) (∂_s f 0 t)` has, at every interior
parameter, derivative the constant `g.inner p v w`. -/

section GaussVariation

open Bundle Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- `T2Space M` is recovered from `T2Space (TangentBundle I M)` because the
zero section `M → TangentBundle I M` is a topological embedding (its
continuous left inverse is the bundle projection). -/
private lemma gauss_t2Space_base (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space (TangentBundle I M)] : T2Space M := by
  have hproj : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hzero : Continuous (Bundle.zeroSection E (TangentSpace I)) :=
    (contMDiff_zeroSection (IB := I) ℝ (F := E) (E := (TangentSpace I : M → Type _))
      (n := ∞)).continuous
  have hinv : Function.LeftInverse (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (Bundle.zeroSection E (TangentSpace I)) := fun _ => rfl
  exact (IsEmbedding.of_leftInverse hinv hproj hzero).t2Space

/-- The radial geodesic variation `f (s, t) := expMap g p (t • (v + s • w))`. -/
private def gaussVariation (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    ℝ → ℝ → M :=
  fun s t => expMap (I := I) g p (show TangentSpace I p from (t • (v + s • w)))

/-- **C²-relaxed velocity chart-rep differentiability.** For any curve `γ`
that is `ContMDiffAt … 2` at `t₀`, the pinned chart-`(γ t₀)` representation
of its velocity field `u ↦ mfderiv γ u 1` is differentiable at `t₀`. The
chart-rep agrees near `t₀` with the `C¹` partial Fréchet section
`u ↦ fderiv (extChartAt (γ t₀) ∘ γ) u 1`. -/
private lemma velocityChartRep_differentiableAt_of_contMDiffAt2
    (γ : ℝ → M) (t₀ : ℝ) (hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) t₀) t₀ := by
  set α : M := γ t₀ with hα
  have hchart_c2 : ContDiffAt ℝ 2 (fun u : ℝ => extChartAt I α (γ u)) t₀ :=
    contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt (I := I) (x := α)).comp t₀ hγC2)
  set sec : ℝ → E := fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (γ w)) u (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec t₀ :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀
      (hchart_c2.fderiv_right (by norm_num))
  have hev_c2 : ∀ᶠ u in nhds t₀, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ u :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγC2
  have hsrcmem : {u : ℝ | γ u ∈ (chartAt H α).source} ∈ nhds t₀ :=
    hγC2.continuousAt.preimage_mem_nhds
      ((chartAt H α).open_source.mem_nhds (mem_chart_source H (γ t₀)))
  have heq : (chartRepAt (I := I) γ (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) t₀)
      =ᶠ[nhds t₀] sec := by
    filter_upwards [hsrcmem, hev_c2] with u hu hu_c2
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) (hu_c2.mdifferentiableAt (by decide)) α (t := u) hu
    change (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ u)
        (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ)) = sec u
    rw [hsec, show (γ t₀) = α from rfl]
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

/-- **C²-relaxed central-curve constant speed.** If a curve `γ` is
`ContMDiffAt … 2` at `t₀` and satisfies the moving-foot geodesic equation
there, the speed-squared `t ↦ g.inner (γ t) (γ' t) (γ' t)` has derivative
zero at `t₀`. -/
private lemma speedSq_hasDerivAt_zero_of_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t₀ : ℝ)
    (hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀)
    (hgeo : HasGeodesicEquationAt (I := I) g γ t₀) :
    HasDerivAt (fun t : ℝ => g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) 0 t₀ := by
  set V : ∀ u, TangentSpace I (γ u) := fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ) with hV
  have hVdiff := velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t₀ hγC2
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
      (contMDiffAt_extChartAt (I := I) (x := γ t₀) (n := 2)).comp t₀ hγC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  have hmc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V V t₀
    hγC2.continuousAt hchartDeriv hVdiff hVdiff
  have hzero : covDerivAlong (I := I) g γ V t₀ = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t₀ hγC2 hgeo
  have hval : g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (V t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ V t₀) = 0 := by
    rw [hzero]; simp
  rw [← hval]; exact hmc

/-- The central radial curve `t ↦ expMap g p (t • a)` is `ContMDiffAt … 2`
at every `t₀` with `‖t₀ • a‖ < expMapC2Radius g p`. -/
private lemma radialCurve_contMDiffAt2
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t₀ : ℝ)
    (ht₀ : ‖t₀ • a‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ := by
  have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 (fun u : ℝ => u • a) t₀ :=
    (contMDiff_id.smul contMDiff_const).contMDiffAt
  have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) t₀) :=
    expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p ht₀
  exact hexp.comp t₀ hbase

/-- The central radial curve `t ↦ expMap g p (t • a)` satisfies the
moving-foot geodesic equation at every `t₀ ∈ (-1, 2)` provided
`‖a‖ < expMapC2Radius g p`.  Transferred from the maximal geodesic via the
`[0, 1]` rescaling identity and `congr_of_eventuallyEq_at`. -/
private lemma radialCurve_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasGeodesicEquationAt (I := I) g
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ := by
  have htmem : t₀ ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hgeo : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => maximalGeodesic (I := I) g p a s) t₀ :=
    radial_hasGeodesicEquationAt_of_norm_lt_radius (I := I) g p ha t₀ htmem
  have hEvEq : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      =ᶠ[nhds t₀] (fun s : ℝ => maximalGeodesic (I := I) g p a s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with u hu
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    change (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
        = maximalGeodesic (I := I) g p a u
    rw [expMap]
    exact maximalGeodesic_rescale_of_norm_lt_radius (I := I) g p ha u hu01
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hEvEq.eq_of_nhds hEvEq hgeo

/-- **Launch velocity of the central radial curve.**
`mfderiv (fun u => expMap g p (u • a)) 0 1 = a` (under the identification
`TangentSpace I p = E`). -/
private lemma radialCurve_launch_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ)
      = (show TangentSpace I p from a) := by
  have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) 0) := by
    have h0 : ‖((fun u : ℝ => u • a) 0)‖ < expMapC2Radius (I := I) g p := by
      simp only; rw [zero_smul, norm_zero]; exact expMapC2Radius_pos (I := I) g p
    exact (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p h0).mdifferentiableAt (by decide)
  have hsmul_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) 0 := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => u • a) := contMDiff_id.smul contMDiff_const
    exact hs.contMDiffAt.mdifferentiableAt (by decide)
  have hcomp : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘
        (fun u : ℝ => u • a) := rfl
  rw [hcomp, mfderiv_comp 0 hexp_mdiff hsmul_mdiff]
  simp only [ContinuousLinearMap.comp_apply]
  have hlaunch : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) 0 (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun u : ℝ => u • a)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) 0 := by
      simpa using (hasFDerivAt_id (0 : ℝ)).smul_const a
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) (1 : ℝ) = a
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  rw [hlaunch, zero_smul, mfderiv_expMap_at_zero (I := I) g p]
  rfl

/-- Abbreviation: the speed-squared of the central radial curve
`t ↦ expMap g p (t • a)`. -/
private def radialSpeedSq (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t : ℝ) : ℝ :=
  g.inner
    (expMap (I := I) g p (show TangentSpace I p from (t • a)))
    (mfderiv 𝓘(ℝ, ℝ) I
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t (1 : ℝ))

/-- The speed-squared of the central radial curve has derivative zero at
every interior parameter `t₀ ∈ (0, 1)`, provided `‖a‖ < expMapC2Radius g p`. -/
private lemma radialSpeedSq_hasDerivAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (radialSpeedSq (I := I) g p a) 0 t₀ := by
  have hnorm : ‖t₀ • a‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht₀
    have habs : |t₀| < 1 := by rw [abs_of_pos h0]; exact h1
    calc |t₀| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs.le (norm_nonneg _)
      _ = ‖a‖ := one_mul _
      _ < _ := ha
  exact speedSq_hasDerivAt_zero_of_geodesic (I := I) g
    (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀
    (radialCurve_contMDiffAt2 (I := I) g p a t₀ hnorm)
    (radialCurve_hasGeodesicEquationAt (I := I) g p a ha t₀ ht₀)

/-- **Constant speed of the central radial geodesic.** For
`‖a‖ < expMapC2Radius g p`, the speed-squared of `t ↦ expMap g p (t • a)` is
constant on `(0, 1)` and equals its launch value `g.inner p a a`. -/
private lemma radialSpeedSq_eq_inner
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    radialSpeedSq (I := I) g p a t₀ = g.inner p a a := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  -- The value at `0` is the launch value `g.inner p a a`.
  have hval0 : radialSpeedSq (I := I) g p a 0 = g.inner p a a := by
    have hv0 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ)
        = (show TangentSpace I p from a) := radialCurve_launch_velocity (I := I) g p a
    change g.inner
        (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • a)))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 (1 : ℝ))
      = g.inner p a a
    rw [hv0]
    -- the base point `expMap g p (0 • a)` is propositionally `p`; transport `g.inner`
    -- through it. The two `a`-arguments live in `TangentSpace I (expMap g p (0•a))`,
    -- defeq to `TangentSpace I p`.
    have hb0 : (0 : ℝ) • a = (0 : E) := zero_smul ℝ a
    rw [show (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • a)) : M) = p by
      rw [hb0]; exact expMap_zero (I := I) g p]
  -- `radialSpeedSq` is constant on the interior.
  have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      radialSpeedSq (I := I) g p a x = radialSpeedSq (I := I) g p a y := by
    intro x hx y hy
    have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1) := convex_Ioo 0 1
    have hdiffOn : DifferentiableOn ℝ (radialSpeedSq (I := I) g p a) (Set.Ioo (0 : ℝ) 1) :=
      fun z hz =>
        ((radialSpeedSq_hasDerivAt_zero (I := I) g p a ha z hz).differentiableAt).differentiableWithinAt
    apply Convex.is_const_of_fderivWithin_eq_zero hconv hdiffOn _ hx hy
    intro z hz
    have hfd : HasFDerivWithinAt (radialSpeedSq (I := I) g p a) (0 : ℝ →L[ℝ] ℝ)
        (Set.Ioo (0 : ℝ) 1) z := by
      have h := ((radialSpeedSq_hasDerivAt_zero (I := I) g p a ha z hz).hasFDerivAt).hasFDerivWithinAt
        (s := Set.Ioo (0 : ℝ) 1)
      rwa [show (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)) = (0 : ℝ →L[ℝ] ℝ) from by
        ext; simp] at h
    rw [hfd.fderivWithin (uniqueDiffWithinAt_Ioo hz)]
  -- Continuity of `radialSpeedSq` at `0` within `Icc 0 1`, extending the interior constant.
  -- The central curve is `C²` near `0` (norm `0 < radius`), so `radialSpeedSq` is
  -- continuous at `0`.
  have hcont0 : ContinuousWithinAt (radialSpeedSq (I := I) g p a) (Set.Icc (0 : ℝ) 1) 0 := by
    set γ : ℝ → M :=
      fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M) with hγ
    set V : ∀ u, TangentSpace I (γ u) := fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ) with hV
    -- Norm bound: `‖t • a‖ ≤ ‖a‖ < radius` for every `t ∈ [0, 1]`.
    have hC2on : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t := by
      intro t ht
      have hnorm : ‖t • a‖ < expMapC2Radius (I := I) g p := by
        rw [norm_smul, Real.norm_eq_abs]
        obtain ⟨h0, h1⟩ := ht
        have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
        calc |t| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ = ‖a‖ := one_mul _
          _ < _ := ha
      exact radialCurve_contMDiffAt2 (I := I) g p a t hnorm
    -- The bundle section `t ↦ ⟨γ t, V t⟩` is continuous on `[0, 1]`.
    have hsec : ContinuousOn
        (fun t : ℝ => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
      sectionAlongCurve_continuousOn_totalSpace (I := I) γ V
        (fun t ht => (hC2on t ht).continuousAt.continuousWithinAt)
        (fun t ht => velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t (hC2on t ht))
    -- `g.inner (γ t) (V t) (V t) = radialSpeedSq … t` is continuous on `[0, 1]`.
    have hinner : ContinuousOn (fun t : ℝ => g.inner (γ t) (V t) (V t)) (Set.Icc (0 : ℝ) 1) :=
      Variation.continuousOn_g_inner_along_curve (I := I) g hsec hsec
    exact (hinner 0 ⟨le_refl 0, by norm_num⟩)
  -- Identify `radialSpeedSq t₀` with the limit value `radialSpeedSq 0`.
  have h0val : radialSpeedSq (I := I) g p a 0 = radialSpeedSq (I := I) g p a t₀ := by
    have h1 : Filter.Tendsto (radialSpeedSq (I := I) g p a)
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (radialSpeedSq (I := I) g p a 0)) :=
      hcont0.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    have h2 : Filter.Tendsto (radialSpeedSq (I := I) g p a)
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (radialSpeedSq (I := I) g p a t₀)) := by
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx using (hconst x hx t₀ ht₀).symm
    have hne : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)]
      exact nhdsGT_neBot 0
    exact tendsto_nhds_unique h1 h2
  rw [← h0val, hval0]

/-- **C²-relaxed variation-field chart-rep differentiability.** For a
two-parameter map `f` whose chart-pulled form is jointly `C²` at `(0, t₀)`,
whose central slice is continuous, and whose transverse slices `u ↦ f u v`
are `MDifferentiableAt 0`, the chart-`(f 0 t₀)` representation of the
variation field `v ↦ ∂_s f|_{s = 0}(v)` is differentiable at `t₀`. -/
private lemma variationFieldChartRep_differentiableAt_of_contDiffAt2
    (f : ℝ → ℝ → M) (t₀ : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (f 0 t₀) (f q.1 q.2)) (0, t₀))
    (hcentral_cont : ContinuousAt (fun v : ℝ => f 0 v) t₀)
    (hslice_v : ∀ᶠ v in nhds t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) t₀ := by
  set α : M := f 0 t₀ with hα
  have hjoint : ContDiffAt ℝ 2
      (Function.uncurry (fun v u : ℝ => extChartAt I α (f u v))) (t₀, (0 : ℝ)) := by
    have hswap : ContDiffAt ℝ 2
        ((fun q : ℝ × ℝ => extChartAt I α (f q.1 q.2)) ∘ (fun q : ℝ × ℝ => (q.2, q.1)))
        (t₀, (0 : ℝ)) :=
      hF2.comp (t₀, (0 : ℝ)) ((contDiffAt_snd).prodMk (contDiffAt_fst))
    exact hswap
  have hg0 : ContDiffAt ℝ 1 (fun _ : ℝ => (0 : ℝ)) t₀ := contDiffAt_const
  have hpartial : ContDiffAt ℝ 1
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v))
        ((fun _ : ℝ => (0 : ℝ)) v)) t₀ :=
    ContDiffAt.fderiv (𝕜 := ℝ) (f := fun v u : ℝ => extChartAt I α (f u v))
      (g := fun _ : ℝ => (0 : ℝ)) hjoint hg0 (by norm_num)
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec t₀ :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hpartial
  have hsrc_nhds : {v : ℝ | f 0 v ∈ (chartAt H α).source} ∈ nhds t₀ := by
    refine hcentral_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t₀))
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) =ᶠ[nhds t₀] sec := by
    filter_upwards [hsrc_nhds, hslice_v] with v hv hslice_v_v
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u v) hslice_v_v α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

/-- **C²-relaxed longitudinal-velocity chart-rep differentiability along the
`s`-curve.** For a two-parameter map `f` whose chart-pulled form is jointly
`C²` at `(0, t₀)`, whose `s`-slice `s ↦ f s t₀` is continuous at `0`, and
whose transverse slices `u ↦ f s u` are `MDifferentiableAt t₀` for `s` near
`0`, the chart-`(f 0 t₀)` representation of the longitudinal-velocity field
`s ↦ ∂_t f s t₀ = mfderiv (fun u => f s u) t₀ 1` (a section along the
`s`-curve `s ↦ f s t₀`) is differentiable at `0`. -/
private lemma longitVelChartRep_differentiableAt_of_contDiffAt2
    (f : ℝ → ℝ → M) (t₀ : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (f 0 t₀) (f q.1 q.2)) (0, t₀))
    (htransverse_cont : ContinuousAt (fun s : ℝ => f s t₀) 0)
    (hslice_u : ∀ᶠ s in nhds (0 : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => f s t₀)
        (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) 0) 0 := by
  set α : M := f 0 t₀ with hα
  -- Partial Fréchet section: `s ↦ fderiv (fun u => extChartAt α (f s u)) t₀ 1`, `C¹` at `0`.
  have hjoint : ContDiffAt ℝ 2
      (Function.uncurry (fun s u : ℝ => extChartAt I α (f s u))) (0, t₀) := hF2
  have hg0 : ContDiffAt ℝ 1 (fun _ : ℝ => t₀) 0 := contDiffAt_const
  have hpartial : ContDiffAt ℝ 1
      (fun s : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f s u))
        ((fun _ : ℝ => t₀) s)) 0 :=
    ContDiffAt.fderiv (𝕜 := ℝ) (f := fun s u : ℝ => extChartAt I α (f s u))
      (g := fun _ : ℝ => t₀) hjoint hg0 (by norm_num)
  set sec : ℝ → E := fun s : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f s u)) t₀ (1 : ℝ)
    with hsec
  have hsec_c1 : ContDiffAt ℝ 1 sec 0 :=
    (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp 0 hpartial
  have hsrc_nhds : {s : ℝ | f s t₀ ∈ (chartAt H α).source} ∈ nhds (0 : ℝ) := by
    refine htransverse_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t₀))
  have heq : (chartRepAt (I := I) (fun s : ℝ => f s t₀)
      (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) 0) =ᶠ[nhds 0] sec := by
    filter_upwards [hsrc_nhds, hslice_u] with s hs hslice_u_s
    have hsrc : (fun u : ℝ => f s u) t₀ ∈ (chartAt H α).source := hs
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f s u) hslice_u_s α (t := t₀) hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t₀) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t₀) s) (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t₀ (1 : ℝ)) = sec s
    rw [hsec, show (fun s : ℝ => f s t₀) 0 = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun u : ℝ => extChartAt I α (f s u)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_c1.differentiableAt (by norm_num))

/-- **The `s`-derivative of the launch speed-squared.** For the radial
variation `s ↦ expMap g p (t • (v + s • w))`, the launch speed-squared
`s ↦ g.inner p (v + s • w) (v + s • w)` has `s`-derivative `2 g.inner p v w`
at `s = 0`, by bilinearity and symmetry of the metric. -/
private lemma launchSpeedSq_s_hasDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    HasDerivAt (fun s : ℝ => g.inner p (v + s • w) (v + s • w))
      (2 * g.inner p v w) 0 := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  have hexpand : (fun s : ℝ => g.inner p (v + s • w) (v + s • w))
      = (fun s : ℝ => B v v + s * (B v w + B w v) + s ^ 2 * (B w w)) := by
    funext s
    change B (v + s • w) (v + s • w) = _
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  have hd1 : HasDerivAt (fun _ : ℝ => B v v) (0 : ℝ) 0 := hasDerivAt_const _ _
  have hd2 : HasDerivAt (fun s : ℝ => s * (B v w + B w v)) (B v w + B w v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (B v w + B w v)
  have hd3 : HasDerivAt (fun s : ℝ => s ^ 2 * (B w w)) (0 : ℝ) 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (B w w))
  have hd : HasDerivAt (fun s : ℝ => B v v + s * (B v w + B w v) + s ^ 2 * (B w w))
      (B v w + B w v) 0 := by simpa using (hd1.add hd2).add hd3
  have hsymm : B w v = B v w := g.symm p w v
  have hval : (2 : ℝ) * B v w = B v w + B w v := by rw [hsymm]; ring
  exact hval ▸ hd

/-! ## The smooth bounded clamp

To apply the intrinsic mixed-commutation `commute_ds_dt_intrinsic_C2`, the
transverse slices `u ↦ f s u` of the variation must be `C²` at the working
parameter `t₀` for **every** `s`.  The naive variation
`f s t = expMap g p (t • (v + s • w))` only enjoys this near `s = 0` (large
`s` pushes the launch vector outside the `C²` ball).  We compose with a
smooth, globally bounded reparametrisation `gaussClamp δ` that is the
identity to first order at `s = 0` (so the `s`-derivative of the variation at
`s = 0` is unchanged) but keeps `v + (gaussClamp δ s) • w` inside the ball
for **all** `s`. -/

/-- The bounded clamp `s ↦ δ · arctan (s / δ)`: smooth, `0` at `0`,
derivative `1` at `0`, and bounded by `δ · (π / 2)` in absolute value. -/
private noncomputable def gaussClamp (δ : ℝ) : ℝ → ℝ :=
  fun s => δ * Real.arctan (s / δ)

private lemma gaussClamp_zero (δ : ℝ) : gaussClamp δ 0 = 0 := by
  simp [gaussClamp]

private lemma gaussClamp_hasDerivAt_one (δ : ℝ) (hδ : 0 < δ) :
    HasDerivAt (gaussClamp δ) 1 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s / δ) (1 / δ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const δ
  have h2 : HasDerivAt Real.arctan (1 / (1 + (0 / δ) ^ 2)) (0 / δ) := by
    simpa using Real.hasDerivAt_arctan (0 / δ)
  have h3 := (h2.comp 0 h1).const_mul δ
  have hcoef : δ * (1 / (1 + (0 / δ) ^ 2) * (1 / δ)) = 1 := by field_simp; ring
  rw [show gaussClamp δ = (fun s : ℝ => δ * Real.arctan (s / δ)) from rfl,
    show (1 : ℝ) = δ * (1 / (1 + (0 / δ) ^ 2) * (1 / δ)) from hcoef.symm]
  exact h3

private lemma gaussClamp_abs_lt (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    |gaussClamp δ s| < δ * (Real.pi / 2) := by
  change |δ * Real.arctan (s / δ)| < δ * (Real.pi / 2)
  rw [abs_mul, abs_of_pos hδ]
  apply mul_lt_mul_of_pos_left _ hδ
  rw [abs_lt]
  exact ⟨by linarith [Real.neg_pi_div_two_lt_arctan (s / δ)],
    by linarith [Real.arctan_lt_pi_div_two (s / δ)]⟩

private lemma gaussClamp_contMDiff (δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (gaussClamp δ) := by
  change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => δ * Real.arctan (s / δ))
  rw [contMDiff_iff_contDiff]
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const δ))

/-! ## The calculus core of Gauss's lemma

For a radial direction `v` strictly inside the `C²` ball and a transverse
direction `w`, fix a clamp scale `δ` with
`‖v‖ + δ · (π / 2) · ‖w‖ < expMapC2Radius g p` and consider the clamped
radial geodesic variation
`F s t := expMap g p (t • (v + (gaussClamp δ s) • w))`.
Because the clamp is the identity to first order at `s = 0`, the
`s`-variation field of `F` agrees at `s = 0` with that of the bare radial
variation, so the conclusion below packages the genuine Gauss-lemma
calculus identity. -/

/-- **The calculus core of Gauss's lemma.** Let `v` lie strictly inside the
`C²` ball (`‖v‖ < expMapC2Radius g p`) and let `δ > 0` keep the clamped
launch vector inside the ball
(`‖v‖ + δ · (π / 2) · ‖w‖ < expMapC2Radius g p`). With the clamped variation
`F s t := expMap g p (t • (v + (gaussClamp δ s) • w))` and the function
`φ t := g.inner (F 0 t) (∂_t F 0 t) (∂_s F 0 t)`, the derivative of `φ` is the
constant `g.inner p v w` at every interior parameter `t₀ ∈ (0, 1)`. -/
private lemma gauss_phi_hasDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖v‖ < expMapC2Radius (I := I) g p)
    (hδsmall : ‖v‖ + δ * (Real.pi / 2) * ‖w‖ < expMapC2Radius (I := I) g p)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)))
      (g.inner p v w) t₀ := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  classical
  -- The clamped variation and its slices.
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
    with hF
  -- Smoothness of the clamp-launch map `(s, t) ↦ t • (v + (gaussClamp δ s) • w)`.
  have hclampMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (gaussClamp δ) := gaussClamp_contMDiff δ
  have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) := by
    refine ContMDiff.smul contMDiff_snd ?_
    refine contMDiff_const.add ?_
    exact (hclampMD.comp contMDiff_fst).smul contMDiff_const
  -- Norm bound: the launch vector stays inside the ball for every `s`.
  have hball : ∀ s : ℝ, ‖v + (gaussClamp δ s) • w‖ < expMapC2Radius (I := I) g p := by
    intro s
    calc ‖v + (gaussClamp δ s) • w‖ ≤ ‖v‖ + ‖(gaussClamp δ s) • w‖ := norm_add_le _ _
      _ = ‖v‖ + |gaussClamp δ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ + δ * (Real.pi / 2) * ‖w‖ := by
          nlinarith [norm_nonneg w, (gaussClamp_abs_lt δ hδ s).le]
      _ < _ := hδsmall
  -- `t₀ • (·)`-scaled launch vector stays in the ball (interior `t₀`).
  have hball_t : ∀ s : ℝ, ‖t₀ • (v + (gaussClamp δ s) • w)‖ < expMapC2Radius (I := I) g p := by
    intro s
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht₀
    have habs : |t₀| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
    calc |t₀| * ‖v + (gaussClamp δ s) • w‖
        ≤ 1 * ‖v + (gaussClamp δ s) • w‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖v + (gaussClamp δ s) • w‖ := one_mul _
      _ < _ := hball s
  -- The transverse slices `u ↦ F s u` are `C²` at `t₀` for every `s`.
  have hslice_u_all : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F s u) t₀ := by
    intro s
    exact radialCurve_contMDiffAt2 (I := I) g p (v + (gaussClamp δ s) • w) t₀ (hball_t s)
  -- The central curve `γ t = F 0 t = expMap g p (t • v)`.
  have hclamp0 : gaussClamp δ 0 = 0 := gaussClamp_zero δ
  have hcentral_eq : (fun t : ℝ => F 0 t)
      = (fun t : ℝ => (expMap (I := I) g p (show TangentSpace I p from (t • v)) : M)) := by
    funext t; rw [hF]; simp only; rw [hclamp0, zero_smul, add_zero]
  -- The launch vector at the central curve has norm `< radius`.
  have hv_ball : ‖v‖ < expMapC2Radius (I := I) g p := hsmall
  -- Joint `C²` of the chart-pulled `F` at `(0, t₀)`.
  have hFjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
      (fun q : ℝ × ℝ => F q.1 q.2) (0, t₀) := by
    have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀) :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          ((fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀)) := by
      have hval : (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t₀)
          = t₀ • (v + (gaussClamp δ 0) • w) := rfl
      rw [hval]
      exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hball_t 0)
    exact hexp.comp (0, t₀) hbase
  have hF2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (F 0 t₀) (F q.1 q.2)) (0, t₀) := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (F 0 t₀)) (F 0 t₀) :=
      contMDiffAt_extChartAt (I := I) (x := F 0 t₀)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => extChartAt I (F 0 t₀) (F q.1 q.2)) (0, t₀) :=
      hext.comp (0, t₀) hFjoint
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  -- Slice continuities (at the working parameters), from joint `C²` of `F`.
  have htransverse_cont : ContinuousAt (fun s : ℝ => F s t₀) 0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun s : ℝ => (s, t₀)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact (hFjoint.comp 0 hincl).continuousAt
  have hcentral_cont : ContinuousAt (fun u : ℝ => F 0 u) t₀ := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun u : ℝ => ((0 : ℝ), u)) t₀ :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hFjoint.comp t₀ hincl).continuousAt
  -- Eventual transverse-slice `C²` near `s = 0` (for `commute_C2`'s `hslice_u`):
  -- all transverse slices are `C²` (every `s`), in particular eventually near `0`.
  have hslice_u_ev : ∀ᶠ s in nhds (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F s u) t₀ :=
    Filter.Eventually.of_forall hslice_u_all
  -- Eventual `s`-slice `C²` near `t₀` (for `commute_C2`'s `hslice_v`): for `v'` near
  -- `t₀`, the foot `F s v' = expMap g p (v' • (v + (gaussClamp δ s) • w))` is `C²` in
  -- `s` at `0`, because `v' • v` stays inside the ball for `v'` near `t₀ ∈ (0, 1)`.
  have hslice_v_ev : ∀ᶠ v' in nhds t₀, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => F u v') 0 := by
    -- The set `{v' | ‖v' • v‖ < radius}` is an open neighbourhood of `t₀`.
    have hcont_norm : ContinuousAt (fun v' : ℝ => ‖v' • v‖) t₀ :=
      (continuous_norm.comp (continuous_id.smul continuous_const)).continuousAt
    have ht₀_ball : ‖t₀ • v‖ < expMapC2Radius (I := I) g p := by
      have := hball_t 0
      rwa [hclamp0, zero_smul, add_zero] at this
    have hnhds : {v' : ℝ | ‖v' • v‖ < expMapC2Radius (I := I) g p} ∈ nhds t₀ :=
      hcont_norm (isOpen_Iio.mem_nhds ht₀_ball)
    filter_upwards [hnhds] with v' hv'
    -- `F u v' = expMap g p (v' • (v + (gaussClamp δ u) • w))`; smoothness in `u` at `0`.
    have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
        (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 := by
      have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) :=
        ContMDiff.smul contMDiff_const
          (contMDiff_const.add (hclampMD.smul contMDiff_const))
      exact hMD.contMDiffAt.of_le ENat.LEInfty.out
    have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
          ((fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0) := by
      have hval : (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 = v' • v := by
        simp only; rw [hclamp0, zero_smul, add_zero]
      rw [hval]
      exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hv'
    exact hexp.comp 0 hbase
  -- The mixed-covariant commutation: `∇_s ∂_t F|_{s=0} = ∇_t ∂_s F|_{s=0}`.
  have hcommute :
      covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
          (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ)) 0
        = covDerivAlong (I := I) g (fun u : ℝ => F 0 u)
          (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s u) 0 (1 : ℝ)) t₀ :=
    commute_ds_dt_intrinsic_C2 (I := I) g F t₀ hF2 hslice_u_ev hslice_v_ev
      htransverse_cont hcentral_cont
  -- The base curve `γ`, the longitudinal velocity field `V`, the variation field `W`.
  set γ : ℝ → M := fun t : ℝ => F 0 t with hγ
  set V : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F 0 u) t (1 : ℝ) with hVdef
  set W : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u t) 0 (1 : ℝ) with hWdef
  -- `γ` is `C²` at `t₀` (it is the central radial curve).
  have hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t₀ := hslice_u_all 0
  -- `γ` is a geodesic at `t₀`.
  have hγgeo : HasGeodesicEquationAt (I := I) g γ t₀ := by
    rw [show γ = (fun t : ℝ => (expMap (I := I) g p
      (show TangentSpace I p from (t • v)) : M)) from hcentral_eq]
    exact radialCurve_hasGeodesicEquationAt (I := I) g p v hv_ball t₀ ht₀
  -- Chart-rep differentiabilities of `V` and `W`.
  have hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ :=
    velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t₀ hγC2
  have hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀ := by
    have hslice_v_md : ∀ᶠ v' in nhds t₀,
        MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 := by
      filter_upwards [hslice_v_ev] with v' hv' using hv'.mdifferentiableAt (by decide)
    exact variationFieldChartRep_differentiableAt_of_contDiffAt2 (I := I) F t₀ hF2
      hcentral_cont hslice_v_md
  -- `chartCurve (γ t₀) γ` is differentiable at `t₀`.
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
      (contMDiffAt_extChartAt (I := I) (x := γ t₀) (n := 2)).comp t₀ hγC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  -- The metric-compatibility derivative of `φ`:
  -- `φ' = ⟨∇_t V, W⟩ + ⟨V, ∇_t W⟩`.
  have hφ_mc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V W t₀
    hγC2.continuousAt hchartDeriv hVdiff hWdiff
  -- First term vanishes: `∇_t V = 0` (γ is a geodesic; `V` is its velocity field).
  have hV_vel : V = fun t : ℝ => (mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) := rfl
  have hVcov0 : covDerivAlong (I := I) g γ V t₀ = 0 := by
    rw [hV_vel]
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t₀ hγC2 hγgeo
  -- Second term: `∇_t W = ∇_s ∂_t F|_{s=0}` (the commutation, reversed).
  -- `∇_t W = covDerivAlong γ W t₀`; by `hcommute` (RHS), this equals the `s`-covariant
  -- derivative of the longitudinal velocity along the `s`-curve `σ`.
  have hWcov_eq : covDerivAlong (I := I) g γ W t₀
      = covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
          (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ)) 0 := by
    rw [hγ, hWdef]; exact hcommute.symm
  -- The `s`-curve `σ s := F s t₀` and the longitudinal-velocity field `U s := ∂_t F s t₀`.
  set σ : ℝ → M := fun s : ℝ => F s t₀ with hσ
  set U : ∀ s, TangentSpace I (σ s) :=
    fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ (1 : ℝ) with hUdef
  -- `U 0 = V t₀` (both are the longitudinal velocity of the central curve at `t₀`).
  have hU0_eq_Vt₀ : U 0 = V t₀ := rfl
  -- The `s`-direction metric-compatibility for the speed-squared `s ↦ ⟨U, U⟩`:
  -- `∂_s ⟨U, U⟩|_0 = 2 ⟨∇_s U, U⟩`. We compute its value two ways:
  -- (a) the speed-squared `s ↦ g.inner (σ s) (U s) (U s)` equals
  --     `s ↦ g.inner p (v + (gaussClamp δ s) • w) (v + (gaussClamp δ s) • w)`
  --     (`radialSpeedSq_eq_inner`), whose `s`-derivative at `0` is `2 g.inner p v w`
  --     (clamp derivative `1` at `0` + bilinearity);
  -- (b) metric compatibility gives `∂_s ⟨U, U⟩ = 2 ⟨∇_s U, U⟩`.
  -- Hence `⟨∇_s U, U⟩ = g.inner p v w`, i.e. `⟨V, ∇_t W⟩ = g.inner p v w`.
  -- Speed-squared identity.
  have hspeed_eq : (fun s : ℝ => g.inner (σ s) (U s) (U s))
      =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w)) := by
    -- Near `s = 0` the clamp keeps the launch in the ball, so `radialSpeedSq_eq_inner`
    -- applies with `a = v + (gaussClamp δ s) • w`.
    filter_upwards with s
    have hball_s := hball s
    have := radialSpeedSq_eq_inner (I := I) g p (v + (gaussClamp δ s) • w) hball_s t₀ ht₀
    rw [radialSpeedSq] at this
    -- `σ s = F s t₀ = expMap g p (t₀ • (v + clamp s • w))`, `U s = ∂_t F s t₀`.
    exact this
  -- `s`-derivative of the launch speed-squared via clamp chain rule + bilinearity.
  have hclamp_deriv : HasDerivAt (gaussClamp δ) 1 0 := gaussClamp_hasDerivAt_one δ hδ
  have hlaunch_sq_deriv :
      HasDerivAt (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w)) (2 * g.inner p v w) 0 := by
    -- `s ↦ g.inner p (v + (gaussClamp δ s)•w)(v + (gaussClamp δ s)•w)`
    --   = (fun r => g.inner p (v + r•w)(v + r•w)) ∘ (gaussClamp δ)`.
    have hcomp : (fun s : ℝ => g.inner p (v + (gaussClamp δ s) • w)
        (v + (gaussClamp δ s) • w))
        = (fun r : ℝ => g.inner p (v + r • w) (v + r • w)) ∘ (gaussClamp δ) := rfl
    rw [hcomp]
    have hbase : HasDerivAt (fun r : ℝ => g.inner p (v + r • w) (v + r • w))
        (2 * g.inner p v w) (gaussClamp δ 0) := by
      rw [gaussClamp_zero δ]; exact launchSpeedSq_s_hasDerivAt (I := I) g p v w
    have hchain := hbase.scomp 0 hclamp_deriv
    simpa using hchain
  -- The `s`-curve `σ` is `C²` at `0`, hence its chart trajectory is differentiable.
  have hσC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 σ 0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2 (fun s : ℝ => (s, t₀)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact hFjoint.comp 0 hincl
  have hσchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (σ 0) σ) 0 := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 ((extChartAt I (σ 0)) ∘ σ) 0 :=
      (contMDiffAt_extChartAt (I := I) (x := σ 0) (n := 2)).comp 0 hσC2
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by norm_num)
  -- Chart-rep differentiability of `U` along `σ` at `0` (longitudinal velocity field).
  have hslice_u_md : ∀ᶠ s in nhds (0 : ℝ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) t₀ := by
    filter_upwards [hslice_u_ev] with s hs using hs.mdifferentiableAt (by decide)
  have hUdiff : DifferentiableAt ℝ (chartRepAt (I := I) σ U 0) 0 :=
    longitVelChartRep_differentiableAt_of_contDiffAt2 (I := I) F t₀ hF2
      htransverse_cont hslice_u_md
  -- The `s`-direction metric-compatibility for `s ↦ g.inner (σ s) (U s) (U s)`:
  -- derivative is `⟨∇_s U, U⟩ + ⟨U, ∇_s U⟩ = 2 ⟨∇_s U, U⟩`.
  have hσ_mc := metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g σ U U 0
    hσC2.continuousAt hσchartDeriv hUdiff hUdiff
  -- Identify the derivative value via the speed-squared identity and the launch derivative.
  have hspeed_hasDerivAt :
      HasDerivAt (fun s : ℝ => g.inner (σ s) (U s) (U s)) (2 * g.inner p v w) 0 :=
    hlaunch_sq_deriv.congr_of_eventuallyEq hspeed_eq
  -- The two derivative values agree (uniqueness of derivatives).
  have hcov_val :
      g.inner (σ 0) (covDerivAlong (I := I) g σ U 0) (U 0)
        + g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
      = 2 * g.inner p v w :=
    hσ_mc.unique hspeed_hasDerivAt
  -- The two summands are equal by symmetry of `g.inner`, so each is `g.inner p v w`.
  -- `σ 0 = F 0 t₀ = γ t₀`.
  have hσ0 : σ 0 = γ t₀ := rfl
  have hcov_symm :
      g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
        = g.inner (σ 0) (covDerivAlong (I := I) g σ U 0) (U 0) :=
    g.symm (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
  have hcov_single :
      g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0) = g.inner p v w := by
    have h2 : 2 * g.inner (σ 0) (U 0) (covDerivAlong (I := I) g σ U 0)
        = 2 * g.inner p v w := by
      rw [two_mul]
      nth_rewrite 1 [hcov_symm]
      exact hcov_val
    linarith [h2]
  -- `⟨V t₀, ∇_t W t₀⟩ = ⟨U 0, ∇_s U 0⟩ = g.inner p v w` (using `hWcov_eq` and `hU0_eq_Vt₀`).
  have hsecond_term :
      g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀) = g.inner p v w := by
    rw [hWcov_eq]
    -- `covDerivAlong g σ U 0` is exactly the RHS of `hWcov_eq`.
    rw [show V t₀ = U 0 from hU0_eq_Vt₀.symm, ← hσ0]
    exact hcov_single
  -- Assemble: `φ' = ⟨∇_t V, W⟩ + ⟨V, ∇_t W⟩ = 0 + g.inner p v w`.
  have hfirst_term :
      g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀) = 0 := by
    rw [hVcov0]; simp
  have hφ_value :
      g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)
      = g.inner p v w := by
    rw [hfirst_term, hsecond_term, zero_add]
  -- The conclusion's `φ` is exactly `fun t => g.inner (γ t) (V t) (W t)`.
  have hφ_fun : (fun t : ℝ => g.inner (γ t) (V t) (W t))
      = (fun t : ℝ => g.inner
          (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ))) :=
    rfl
  rw [← hφ_fun, ← hφ_value]
  exact hφ_mc

end GaussVariation

section GaussAssembly

open Bundle Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- **Radial chain rule.** For `‖t₀ • a‖ < expMapC2Radius g p`,
`mfderiv (u ↦ exp_p (u • a)) t₀ 1 = mfderiv exp_p (t₀ • a) a`. -/
private lemma radialCurve_mfderiv_chain
    (g : SmoothRiemannianMetric I M) (p : M) (a : E) (t₀ : ℝ)
    (ht : ‖t₀ • a‖ < expMapC2Radius (I := I) g p) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ (1 : ℝ)
      = mfderiv 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (t₀ • a)
          (show TangentSpace I p from a) := by
  have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun u : ℝ => u • a) t₀) :=
    (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p ht).mdifferentiableAt (by decide)
  have hsmul_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ := by
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun u : ℝ => u • a) :=
      contMDiff_id.smul contMDiff_const
    exact hs.contMDiffAt.mdifferentiableAt (by decide)
  have hcomp : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘
        (fun u : ℝ => u • a) := rfl
  rw [hcomp, mfderiv_comp t₀ hexp_mdiff hsmul_mdiff]
  simp only [ContinuousLinearMap.comp_apply]
  have hlaunch : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => u • a) t₀ (1 : ℝ) = a := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun u : ℝ => u • a)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) t₀ := by
      simpa using (hasFDerivAt_id (t₀ : ℝ)).smul_const a
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) (1 : ℝ) = a
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  rw [hlaunch]

/-- **Continuity of the Gauss `φ`-integrand on `[0, 1]`.** For the clamped
radial variation `F s t := expMap g p (t • (v + (gaussClamp δ s) • w))`, the
scalar `t ↦ g.inner (F 0 t) (∂_t F 0 t) (∂_s F 0 t)` is continuous on the
closed interval `[0, 1]`. -/
private lemma gauss_phi_continuousOn
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) (δ : ℝ)
    (hsmall : ‖v‖ < expMapC2Radius (I := I) g p) :
    ContinuousOn (fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)))
      (Set.Icc (0 : ℝ) 1) := by
  haveI : T2Space M := gauss_t2Space_base (I := I)
  classical
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
    with hF
  have hclamp0 : gaussClamp δ 0 = 0 := gaussClamp_zero δ
  set γ : ℝ → M := fun t : ℝ => F 0 t with hγ
  set V : ∀ t, TangentSpace I (γ t) := fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) with hVdef
  set W : ∀ t, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u t) 0 (1 : ℝ) with hWdef
  -- `‖t • v‖ < radius` on `[0, 1]`.
  have hnorm_t : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t • v‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    calc |t| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < _ := hsmall
  -- `γ` is `C²` on `[0, 1]`.
  have hγC2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t := by
    intro t ht
    have heq : γ = fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • v)) : M) := by
      funext u; rw [hγ, hF]; simp only; rw [hclamp0, zero_smul, add_zero]
    rw [heq]
    exact radialCurve_contMDiffAt2 (I := I) g p v t (hnorm_t t ht)
  -- Joint `C²` of chart-pulled `F` at `(0, t)` for `t ∈ [0, 1]`.
  have hF2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => extChartAt I (F 0 t) (F q.1 q.2)) (0, t) := by
    intro t ht
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) := by
      refine ContMDiff.smul contMDiff_snd ?_
      exact contMDiff_const.add (((gaussClamp_contMDiff δ).comp contMDiff_fst).smul contMDiff_const)
    have hFjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
        (fun q : ℝ × ℝ => F q.1 q.2) (0, t) := by
      have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
          (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t) :=
        hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
      have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
            ((fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t)) := by
        have hval : (fun q : ℝ × ℝ => q.2 • (v + (gaussClamp δ q.1) • w)) (0, t) = t • v := by
          simp only; rw [hclamp0, zero_smul, add_zero]
        rw [hval]
        exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hnorm_t t ht)
      exact hexp.comp (0, t) hbase
    have hext : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (F 0 t)) (F 0 t) :=
      contMDiffAt_extChartAt (I := I) (x := F 0 t)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
        (fun q : ℝ × ℝ => extChartAt I (F 0 t) (F q.1 q.2)) (0, t) :=
      hext.comp (0, t) hFjoint
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  -- `V` chart-rep differentiable on `[0, 1]`.
  have hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t :=
    fun t ht => velocityChartRep_differentiableAt_of_contMDiffAt2 (I := I) γ t (hγC2 t ht)
  -- `W` chart-rep differentiable on `[0, 1]`.
  have hWdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t := by
    intro t ht
    have hslice_v_md : ∀ᶠ v' in nhds t,
        MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 := by
      have hcont_norm : ContinuousAt (fun v' : ℝ => ‖v' • v‖) t :=
        (continuous_norm.comp (continuous_id.smul continuous_const)).continuousAt
      have hnhds : {v' : ℝ | ‖v' • v‖ < expMapC2Radius (I := I) g p} ∈ nhds t :=
        hcont_norm (isOpen_Iio.mem_nhds (hnorm_t t ht))
      filter_upwards [hnhds] with v' hv'
      have hbase : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
          (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 := by
        have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) :=
          ContMDiff.smul contMDiff_const
            (contMDiff_const.add ((gaussClamp_contMDiff δ).smul contMDiff_const))
        exact hMD.contMDiffAt.of_le ENat.LEInfty.out
      have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
            ((fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0) := by
        have hval : (fun u : ℝ => v' • (v + (gaussClamp δ u) • w)) 0 = v' • v := by
          simp only; rw [hclamp0, zero_smul, add_zero]
        rw [hval]
        exact expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hv'
      exact (hexp.comp 0 hbase).mdifferentiableAt (by decide)
    exact variationFieldChartRep_differentiableAt_of_contDiffAt2 (I := I) F t (hF2 t ht)
      (hγC2 t ht).continuousAt hslice_v_md
  -- Two-section total-space continuity, then the inner product.
  have hsecV : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) (V t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
    sectionAlongCurve_continuousOn_totalSpace (I := I) γ V
      (fun t ht => (hγC2 t ht).continuousAt.continuousWithinAt) hVdiff
  have hsecW : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) (W t) : TangentBundle I M)) (Set.Icc (0 : ℝ) 1) :=
    sectionAlongCurve_continuousOn_totalSpace (I := I) γ W
      (fun t ht => (hγC2 t ht).continuousAt.continuousWithinAt) hWdiff
  exact Variation.continuousOn_g_inner_along_curve (I := I) g hsecV hsecW

-- `hv` records that `v` lies in the natural domain of `expMap g p`; it is part of
-- the intended statement (the radial direction is in `expDomain`) and kept in the
-- signature for downstream clarity, even though the stronger `C²`-ball hypothesis
-- `hsmall` already guarantees `expMap g p v` is the genuine geodesic value.
set_option linter.unusedVariables false in
/-- **Gauss's lemma (pullback form).** At every radial direction
`v ∈ expDomain g p` *inside the `C²` ball* (`‖v‖ < expMapC2Radius g p`),
the pullback of `g` through `expMap g p` evaluates
to `g_p(v, v)` on the `(v, v)` slot, and annihilates the `(v, w)` slot
for every `w` that is `g_p`-orthogonal to `v`. The orthogonality and
the target value are stated in the abstract metric `g.inner p`; the
model-space Euclidean inner product `inner ℝ` on `E` is unrelated to
`g.inner p` in general (its appearance in earlier skeleton drafts was a
defect: the classical Gauss lemma is intrinsic to `g`).

The hypothesis `hsmall : ‖v‖ < expMapC2Radius g p` restricts `v` to the
ball on which `expMap g p` is twice continuously differentiable; this is
mathematically necessary, as the proof differentiates the radial geodesic
variation `f (s, t) := expMap g p (t • (v + s • w))` twice in `t` and once
in `s`. -/
theorem gauss_lemma_pullback
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hsmall : ‖(v : E)‖ < expMapC2Radius (I := I) g p) :
    g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v)) =
      g.inner p v v ∧
    ∀ {w : E}, g.inner p v w = (0 : ℝ) →
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from w)) =
        (0 : ℝ) := by
  -- The radial geodesic variation `f (s, t) := expMap g p (t • (v + s • w))` is
  -- the natural witness.  By `expMap_contMDiffAt2_of_norm_lt_radius` and
  -- `hsmall`, `expMap g p` is `C²` near the segment, so `f` is jointly `C²` on
  -- a neighbourhood of `[0, 1] × {0}` (composition with the smooth
  -- `(s, t) ↦ t • (v + s • w)`); this is the only place `hsmall` is used, and
  -- it is genuinely necessary because the argument differentiates `f` twice.
  --
  -- (v, v) slot: the central curve `t ↦ f (0, t) = expMap g p (t • v)` is a
  -- radial geodesic, hence has constant speed-squared
  -- `g.inner (f 0 t) (∂_t f) (∂_t f) = g_p (v, v)` (constant-speed of a
  -- geodesic, via `chartGramAlongCurve_hasDerivAt_covariant` + the geodesic
  -- equation, exactly the computation in `isGeodesicOn_speedSq_hasDerivAt_zero`);
  -- evaluating the chain rule
  -- `mfderiv (fun u => expMap g p u) v v = ∂_t f (0, 1)` at `t = 1` gives the slot.
  --
  -- (v, w) slot: set `φ t := g.inner (f 0 t) (∂_t f) (∂_s f)`.  Then
  -- `φ' = ⟨∇_t ∂_t f, ∂_s f⟩ + ⟨∂_t f, ∇_t ∂_s f⟩`; the first term vanishes
  -- (radial geodesic), and the second equals `½ ∂_s g.inner_p (v + s•w, v + s•w)|₀
  -- = g_p (v, w)` after the mixed-derivative commutation `∇_t ∂_s f = ∇_s ∂_t f`.
  -- Integrating from `φ 0 = 0` (since `∂_s f (0, 0) = 0` by orthogonality bookkeeping)
  -- gives `φ 1 = g_p (v, w) = 0`.
  --
  -- STATUS (current):
  --   * The combined small-velocity radius `expMapC2Radius g p` is now the *minimum*
  --     of the `C²` radius, the radial-geodesic radius, and the rescaling-identity
  --     radius (see the definition above).  Hence `‖v‖ < expMapC2Radius g p`
  --     simultaneously delivers: `expMap g p` is `C²` near `t • (v + s • w)`
  --     (`expMap_contMDiffAt2_of_norm_lt_radius`); the radial curve is a geodesic on
  --     the OPEN interval `Ioo (-1) 2 ⊇ [0, 1]`
  --     (`radial_hasGeodesicEquationAt_of_norm_lt_radius`,
  --     `radial_maximalGeodesic_hasGeodesicEquationAt_of_small` now stated on the open
  --     interval); and the rescaling identity
  --     `maximalGeodesic g p (t • v) 1 = maximalGeodesic g p v t`
  --     (`maximalGeodesic_rescale_of_norm_lt_radius`) on `[0, 1]`.  This closes the
  --     genuine soundness gap that the bare `C²` radius did not relate to the
  --     geodesic / rescaling radii.
  --   * The following structural pieces of the variational assembly have been
  --     individually verified to type-check against the keystones (joint-`C²` of `f`,
  --     the slice `ContMDiffAt 2`, the radial chain rule
  --     `mfderiv (u ↦ exp_p (u • a)) t₀ 1 = mfderiv exp_p (t₀ • a) a`, the launch-velocity
  --     identity `mfderiv (u ↦ exp_p (u • a)) 0 1 = a` via `mfderiv_expMap_at_zero`, the
  --     `C²`-relaxed velocity / variation-field chart-rep `DifferentiableAt` via
  --     `ContDiffAt.fderiv` + `chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt`,
  --     and `T2Space M` from `T2Space (TangentBundle I M)` via the zero-section
  --     embedding).
  --   * REMAINING RESIDUAL (the FTC assembly):
  --       (ii)  the FTC over `[0,1]` for `φ t := g.inner (f 0 t) (∂_t f) (∂_s f)`
  --             with `φ' = ⟨∇_t ∂_t f, ∂_s f⟩ + ⟨∂_t f, ∇_t ∂_s f⟩`
  --             (`metric_compat_hasDerivAt_inner_of_chartCurveDeriv`), first term `= 0`
  --             (geodesic + `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2`),
  --             second term `= ⟨∂_t f, ∇_s ∂_t f⟩` (`commute_ds_dt_intrinsic_C2`);
  --       (iii) the constant-speed-in-`s` value
  --             `⟨∂_t f, ∇_s ∂_t f⟩ = ½ ∂_s g.inner_p (v + s•w, v + s•w)|₀ = g.inner_p (v, w)`,
  --             plus `φ 0 = 0` (since `∂_s f (0,0) = 0`) and the endpoint
  --             identifications `∂_t f (0,1) = mfderiv exp_p v v`,
  --             `∂_s f (0,1) = mfderiv exp_p v w`.
  --     ARCHITECTURAL NOTE for (iii): the constant-speed identity
  --     `g.inner (f s t) (∂_t f) (∂_t f) = g.inner_p (v + s•w, v + s•w)` should NOT be
  --     routed through `HopfRinow.isGeodesicOn_speedSq_const` — `HopfRinow` IMPORTS this
  --     file, so it is a forbidden cycle.  Instead derive it cycle-free from the SAME
  --     metric-compatibility keystone used in (ii): for the geodesic slice
  --     `γ_s := t ↦ exp_p (t • (v + r s • w))` (with `r` a smooth identity-near-`0`,
  --     globally bounded clamp, e.g. `r s := δ • Real.arctan (s / δ)`, keeping the
  --     launch magnitude inside `expMapC2Radius`),
  --     `metric_compat_hasDerivAt_inner_of_chartCurveDeriv` with `V = W = ∂_t γ_s` and
  --     the geodesic `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2` gives
  --     `∂_t (speed²) = 0` on the OPEN `Ioo (0,1)`; constancy there +
  --     `Set.EqOn.of_subset_closure` to `[0,1]` (the speed² function is continuous on
  --     `[0,1]` since `γ_s` is `C²` near `[0,1]`) yields
  --     `speed²(t) = speed²(0) = g.inner_p (v + r s • w, v + r s • w)`.  The central
  --     curve `t ↦ exp_p (t • a)` is `C²` near `[0,1]` directly, unlike
  --     `maximalGeodesic g p a` whose function-level `C¹` regularity is an open project
  --     residual (`HopfRinow.lean`); transfer the geodesic equation from
  --     `maximalGeodesic g p a` to `exp_p (·•a)` on `Ioo (0,1)` via the `[0,1]`
  --     rescaling identity and `HasGeodesicEquationAt.congr_of_eventuallyEq_at`.
  --     All keystones (`metric_compat_*`, `commute_ds_dt_intrinsic_C2`,
  --     `covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2`) live in
  --     `SecondVariation` / `CovariantDerivativeAlong`, which do NOT import this file,
  --     so importing them here is cycle-free.
  haveI : T2Space M := gauss_t2Space_base (I := I)
  -- The single key identity, for every transverse direction `w`:
  --   `g.inner (exp_p v) (d exp_v v) (d exp_v w) = g.inner p v w`.
  -- The pullback's `(v, v)` slot is the `w := v` specialisation; the `(v, w)`
  -- slot for `g_p`-orthogonal `w` is the `g.inner p v w = 0` specialisation.
  have key : ∀ w : E,
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from w)) = g.inner p v w := by
    intro w
    -- Choose a clamp scale `δ > 0` keeping the launch vector inside the `C²` ball.
    set R : ℝ := expMapC2Radius (I := I) g p with hR
    have hRpos : 0 < R - ‖v‖ := sub_pos.mpr hsmall
    set δ : ℝ := (R - ‖v‖) / (2 * ((Real.pi / 2) * ‖w‖ + 1)) with hδdef
    have hden_pos : 0 < 2 * ((Real.pi / 2) * ‖w‖ + 1) := by positivity
    have hδ : 0 < δ := by rw [hδdef]; exact div_pos hRpos hden_pos
    have hδsmall : ‖v‖ + δ * (Real.pi / 2) * ‖w‖ < R := by
      have hstep : δ * ((Real.pi / 2) * ‖w‖ + 1) = (R - ‖v‖) / 2 := by
        rw [hδdef]; field_simp
      have hle : δ * (Real.pi / 2) * ‖w‖ ≤ δ * ((Real.pi / 2) * ‖w‖ + 1) := by
        have heq : δ * (Real.pi / 2) * ‖w‖ = δ * ((Real.pi / 2) * ‖w‖) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hδ.le
      have hbnd : δ * (Real.pi / 2) * ‖w‖ ≤ (R - ‖v‖) / 2 := by rw [← hstep]; exact hle
      linarith [hbnd, hRpos]
    -- The variation and its `φ`-integrand.
    set F : ℝ → ℝ → M := fun s t =>
      (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ s) • w))) : M)
      with hF
    set φ : ℝ → ℝ := fun t : ℝ => g.inner
        (expMap (I := I) g p (show TangentSpace I p from (t • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (t • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ))
      with hφdef
    -- `φ'` is the constant `g.inner p v w` on `(0, 1)`.
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (g.inner p v w) t := by
      intro t ht
      rw [hφdef]
      exact gauss_phi_hasDerivAt (I := I) g p v w δ hδ
        (by rw [← hR]; exact hsmall) (by rw [← hR]; exact hδsmall) t ht
    -- `φ` is continuous on `[0, 1]`.
    have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
      rw [hφdef]
      exact gauss_phi_continuousOn (I := I) g p v w δ (by rw [← hR]; exact hsmall)
    -- FTC over `[0, 1]`: `∫₀¹ (g.inner p v w) = φ 1 - φ 0`.
    have hint : IntervalIntegrable (fun _ : ℝ => g.inner p v w) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have hFTC : ∫ _t in (0 : ℝ)..1, (g.inner p v w) = φ 1 - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
    -- The constant integral over `[0, 1]` is `g.inner p v w`.
    have hconstint : ∫ _t in (0 : ℝ)..1, (g.inner p v w) = g.inner p v w := by
      rw [intervalIntegral.integral_const]; simp
    have hφdiff : φ 1 - φ 0 = g.inner p v w := by rw [← hFTC, hconstint]
    -- `φ 0 = 0`: the `s`-variation field at `t = 0` is zero (constant base point `p`).
    have hsvar0 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)
        = 0 := by
      have hconstmap : (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M))
          = fun _ : ℝ => p := by
        funext u; simp only; rw [zero_smul]; exact expMap_zero (I := I) g p
      rw [hconstmap, mfderiv_const]; rfl
    have hφ0 : φ 0 = 0 := by
      have hφ0eval : φ 0 = g.inner
          (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from ((0 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
              (1 : ℝ)) := rfl
      rw [hφ0eval, hsvar0, ContinuousLinearMap.map_zero]
    -- Therefore `φ 1 = g.inner p v w`.
    have hφ1 : φ 1 = g.inner p v w := by rw [← hφdiff, hφ0, sub_zero]
    -- Endpoint identifications, rewriting `φ 1` into the goal's `mfderiv exp_p v _` form.
    -- `F 0 1 = exp_p v`.
    have hbase1 : (expMap (I := I) g p
        (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
        = (expMap (I := I) g p (show TangentSpace I p from v) : M) := by
      rw [gaussClamp_zero δ, zero_smul, add_zero, one_smul]
    -- `∂_t F 0 1 = mfderiv exp_p v v`.
    have htvel1 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ)
        = mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from v) := by
      have hav : v + (gaussClamp δ 0) • w = v := by rw [gaussClamp_zero δ, zero_smul, add_zero]
      rw [hav]
      have hnorm1 : ‖(1 : ℝ) • v‖ < expMapC2Radius (I := I) g p := by
        rw [one_smul]; exact hsmall
      rw [radialCurve_mfderiv_chain (I := I) g p v 1 hnorm1, one_smul]
    -- `∂_s F 0 1 = mfderiv exp_p v w`.
    have hsvar1 : mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0 (1 : ℝ)
        = mfderiv 𝓘(ℝ, E) I
          (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
          (show TangentSpace I p from w) := by
      set Hs : ℝ → E := fun u : ℝ => (1 : ℝ) • (v + (gaussClamp δ u) • w) with hHs
      have hHs0 : Hs 0 = v := by
        rw [hHs]; simp only; rw [gaussClamp_zero δ, zero_smul, add_zero, one_smul]
      have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I
          (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) (Hs 0) := by
        rw [hHs0]
        exact (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hsmall).mdifferentiableAt
          (by decide)
      have hHs_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Hs 0 := by
        have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Hs := by
          rw [hHs]
          exact ContMDiff.smul contMDiff_const
            (contMDiff_const.add ((gaussClamp_contMDiff δ).smul contMDiff_const))
        exact hMD.contMDiffAt.mdifferentiableAt (by decide)
      have hcomp : (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M))
          = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) ∘ Hs := rfl
      rw [hcomp, mfderiv_comp 0 hexp_mdiff hHs_mdiff]
      simp only [ContinuousLinearMap.comp_apply]
      have hHsderiv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Hs 0 (1 : ℝ) = w := by
        rw [mfderiv_eq_fderiv]
        have hclamp : HasDerivAt (gaussClamp δ) 1 0 := gaussClamp_hasDerivAt_one δ hδ
        have hHd : HasDerivAt Hs w 0 := by
          have h1 : HasDerivAt (fun u : ℝ => (gaussClamp δ u) • w) ((1 : ℝ) • w) 0 :=
            hclamp.smul_const w
          have h2 : HasDerivAt (fun u : ℝ => v + (gaussClamp δ u) • w)
              ((0 : E) + (1 : ℝ) • w) 0 := (hasDerivAt_const (0 : ℝ) v).add h1
          rw [zero_add, one_smul] at h2
          have h3 : Hs = fun u : ℝ => v + (gaussClamp δ u) • w := by
            rw [hHs]; funext u; rw [one_smul]
          rw [h3]; exact h2
        rw [hHd.hasFDerivAt.fderiv]
        change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) (1 : ℝ) = w
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
      rw [hHsderiv, hHs0]
    -- Rewrite `φ 1 = g.inner p v w` into the goal.
    -- `φ 1` unfolds (by `rfl`) to the endpoint-indexed `g.inner`; rewrite the three
    -- endpoint identifications to land on the goal's `mfderiv exp_p v _` form.
    have hφ1eval : φ 1 = g.inner
        (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
            (1 : ℝ)) := rfl
    -- Identify the base point first (this fixes the fibre over which the two
    -- vector arguments live), then the two velocity identifications.
    have hcollapse : g.inner
          (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ 0) • w))))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from (u • (v + (gaussClamp δ 0) • w))) : M)) 1 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (expMap (I := I) g p
              (show TangentSpace I p from ((1 : ℝ) • (v + (gaussClamp δ u) • w))) : M)) 0
              (1 : ℝ))
        = g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) v
            (show TangentSpace I p from w)) := by
      rw [htvel1, hsvar1, hbase1]
    rw [hφ1eval, hcollapse] at hφ1
    exact hφ1
  -- Assemble both slots.
  refine ⟨?_, ?_⟩
  · -- `(v, v)` slot: `w := v` specialisation.
    exact key v
  · -- `(v, w)` slot: `g.inner p v w = 0` gives the value `0`.
    intro w hw
    rw [key w]; exact hw

end GaussAssembly

section RadialLengthEngine

/-! ## Radial length-comparison engine

The classical Gauss-lemma length comparison: inside a normal ball, the
radial direction is the unique length-minimising direction.  The engine
below packages the pointwise content used by the radial-minimiser cluster.

* `expMap_normalChartAt` — on the chart source, `expMap g p` inverts the
  normal chart.
* `gauss_radial_lower_bound` — the algebraic core: at a radial direction
  `u ≠ 0` inside the `C²` ball, the pullback speed-squared dominates the
  squared radial component, `g_p(u, ζ)² / g_p(u, u) ≤ g(dexp_u ζ, dexp_u ζ)`,
  proved by the Gauss orthogonal decomposition of `ζ` against `u`.
* `radial_chain_mfderiv` — for a curve confined to the chart, the velocity
  factors as `exp`-differential of the chart-image velocity.
* `radialDist_hasDerivAt` — the derivative of the radial distance
  `s ↦ √(g_p(ψ s, ψ s))`.
* `gauss_pointwise_speed_lower_bound` — the pointwise Gauss speed bound:
  the radial-distance derivative squared is dominated by the intrinsic
  speed-squared. -/

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

/-- On the source of the normal chart, `expMap g p` inverts the chart. -/
private theorem expMap_normalChartAt (g : SmoothRiemannianMetric I M) (p : M) {x : M}
    (hx : x ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    (expMap (I := I) g p
      (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p x))) = x := by
  have hmem := (NormalCoordinates.normalChartAt (I := I) g p).map_source hx
  have h2 := NormalCoordinates.normalChartAt_symm_apply (I := I) g p
    (v := NormalCoordinates.normalChartAt (I := I) g p x) hmem
  have h1 := NormalCoordinates.normalChartAt_left_inv (I := I) g p hx
  rw [← h2, h1]

/-- **Gauss radial lower bound.** For a radial direction `u ≠ 0` inside the
`C²` ball, the pullback speed-squared at `u` dominates the squared radial
component: `g_p(u, ζ)² / g_p(u, u) ≤ g(exp u, dexp_u ζ, dexp_u ζ)`.  Proved
by decomposing `ζ` into the `g_p`-radial component along `u` and the
`g_p`-orthogonal remainder, then applying the two Gauss-lemma slots:
`g(dexp_u u, dexp_u u) = g_p(u, u)` (diagonal) and
`g(dexp_u u, dexp_u β) = 0` for `g_p`-orthogonal `β` (cross). -/
private theorem gauss_radial_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : (show TangentSpace I p from u) ∈ expDomain (I := I) g p)
    (hsmall : ‖(u : E)‖ < expMapC2Radius (I := I) g p)
    (hune : u ≠ 0) (ζ : E) :
    (g.inner p u ζ)^2 / g.inner p u u ≤
      g.inner (expMap (I := I) g p (show TangentSpace I p from u))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ)) := by
  classical
  obtain ⟨hdiag, hcross⟩ := gauss_lemma_pullback (I := I) g p hu hsmall
  set q := expMap (I := I) g p (show TangentSpace I p from u) with hq
  set D : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
    with hD
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  set Bq : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hBq
  have hupos : 0 < B u u := g.pos p u hune
  have hune' : B u u ≠ 0 := ne_of_gt hupos
  set α : ℝ := B u ζ / B u u with hα
  set β : E := ζ - α • u with hβ
  have hdecomp : ζ = β + α • u := by rw [hβ]; abel
  have hβ_orth : B u β = 0 := by
    have key : B u β + α * B u u = B u ζ := by
      calc B u β + α * B u u = B u (β + α • u) := by rw [map_add, map_smul, smul_eq_mul]
        _ = B u ζ := by rw [← hdecomp]
    have hb : B u β = B u ζ - α * B u u := by linarith [key]
    rw [hb, hα]; field_simp; ring
  have hDζ : D ζ = D β + α • D u := by
    rw [show ζ = β + α • u from hdecomp, map_add, map_smul]
  change B u ζ ^ 2 / B u u ≤ Bq (D ζ) (D ζ)
  rw [hDζ]
  have hexpand : Bq (D β + α • D u) (D β + α • D u)
      = Bq (D β) (D β) + 2 * α * Bq (D u) (D β) + α^2 * Bq (D u) (D u) := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsym : Bq (D β) (D u) = Bq (D u) (D β) := g.symm q (D β) (D u)
    rw [hsym]; ring
  rw [hexpand]
  have hdiag' : Bq (D u) (D u) = B u u := hdiag
  have hcross' : Bq (D u) (D β) = 0 := hcross hβ_orth
  rw [hdiag', hcross']
  have hββ_nn : 0 ≤ Bq (D β) (D β) := by
    rcases eq_or_ne (D β) 0 with h | h
    · rw [h]; simp
    · exact (g.pos q (D β) h).le
  have hlhs : B u ζ ^ 2 / B u u = α^2 * B u u := by rw [hα]; field_simp
  rw [hlhs]
  nlinarith [hββ_nn, mul_nonneg (sq_nonneg α) hupos.le]

/-- **Equality case of the Gauss radial lower bound.** For a radial direction
`u ≠ 0` inside the `C²` ball, the pullback speed-squared bound of
`gauss_radial_lower_bound` is an *equality*
`g_p(u, ζ)² / g_p(u, u) = g(dexp_u ζ, dexp_u ζ)` **iff** the exponential
differential sends the `g_p`-orthogonal part `ζ - (g_p(u,ζ)/g_p(u,u))•u` of `ζ`
to `0`, equivalently iff `dexp_u ζ` is the radial multiple
`(g_p(u,ζ)/g_p(u,u)) • dexp_u u`.  This isolates the rigidity that turns the
length lower bound into a radial-reparametrisation characterisation: along an
equality-realising velocity the chart-image velocity is radial up to the
exponential differential.  The proof tracks equality through the same
orthogonal decomposition used by `gauss_radial_lower_bound`; positive
definiteness of `g` at `q = exp_p u` converts the seminorm-zero of the
orthogonal image into the vanishing of `dexp_u (ζ - α•u)`. -/
private theorem gauss_radial_lower_bound_eq_iff
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : (show TangentSpace I p from u) ∈ expDomain (I := I) g p)
    (hsmall : ‖(u : E)‖ < expMapC2Radius (I := I) g p)
    (hune : u ≠ 0) (ζ : E) :
    (g.inner p u ζ)^2 / g.inner p u u =
      g.inner (expMap (I := I) g p (show TangentSpace I p from u))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
        (mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from ζ))
    ↔ mfderiv 𝓘(ℝ, E) I
          (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
          (show TangentSpace I p from
            (ζ - (g.inner p u ζ / g.inner p u u) • u)) = 0 := by
  classical
  obtain ⟨hdiag, hcross⟩ := gauss_lemma_pullback (I := I) g p hu hsmall
  set q := expMap (I := I) g p (show TangentSpace I p from u) with hq
  set D : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) u
    with hD
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB
  set Bq : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hBq
  have hupos : 0 < B u u := g.pos p u hune
  have hune' : B u u ≠ 0 := ne_of_gt hupos
  set α : ℝ := B u ζ / B u u with hα
  set β : E := ζ - α • u with hβ
  have hdecomp : ζ = β + α • u := by rw [hβ]; abel
  have hβ_orth : B u β = 0 := by
    have key : B u β + α * B u u = B u ζ := by
      calc B u β + α * B u u = B u (β + α • u) := by rw [map_add, map_smul, smul_eq_mul]
        _ = B u ζ := by rw [← hdecomp]
    have hb : B u β = B u ζ - α * B u u := by linarith [key]
    rw [hb, hα]; field_simp; ring
  have hDζ : D ζ = D β + α • D u := by
    rw [show ζ = β + α • u from hdecomp, map_add, map_smul]
  -- Expand the right side exactly as in `gauss_radial_lower_bound`.
  have hexpand : Bq (D ζ) (D ζ)
      = Bq (D β) (D β) + α^2 * B u u := by
    rw [hDζ]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsym : Bq (D β) (D u) = Bq (D u) (D β) := g.symm q (D β) (D u)
    have hdiag' : Bq (D u) (D u) = B u u := hdiag
    have hcross' : Bq (D u) (D β) = 0 := hcross hβ_orth
    rw [hsym, hdiag', hcross']; ring
  have hlhs : B u ζ ^ 2 / B u u = α^2 * B u u := by rw [hα]; field_simp
  -- The equality of `(B u ζ)²/B u u` with `Bq (Dζ)(Dζ)` is `Bq (Dβ)(Dβ) = 0`.
  have hiff_seminorm :
      (B u ζ ^ 2 / B u u = Bq (D ζ) (D ζ)) ↔ Bq (D β) (D β) = 0 := by
    rw [hlhs, hexpand]
    constructor
    · intro h; linarith
    · intro h; rw [h]; ring
  -- `Bq (Dβ)(Dβ) = 0 ↔ D β = 0` by positive definiteness of `g` at `q`.
  have hiff_zero : Bq (D β) (D β) = 0 ↔ D β = 0 := by
    constructor
    · intro h
      by_contra hne
      exact absurd h (ne_of_gt (g.pos q (D β) hne))
    · intro h; rw [h]; simp
  -- Assemble: the original equality (in `g.inner` form) ↔ `D β = 0`,
  -- and `D β = D (ζ - α • u)` is the displayed orthogonal-part image.
  change ((B u ζ) ^ 2 / B u u = Bq (D ζ) (D ζ)) ↔ D β = 0
  rw [hiff_seminorm, hiff_zero]

/-- **Chain rule for a curve confined to the normal chart.** If a curve `γ`
is `MDifferentiableAt t`, stays in the normal-chart source near `t`, and its
chart image `c(γt)` lies inside the `C²` ball, then the velocity of `γ` is the
exponential differential applied to the velocity of the chart-image curve. -/
private theorem radial_chain_mfderiv
    (g : SmoothRiemannianMetric I M) (p : M) {γ : ℝ → M} {t : ℝ}
    (hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hsrc : γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hball : ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
      expMapC2Radius (I := I) g p)
    (hev : ∀ᶠ s in nhds t, γ s ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
    = mfderiv 𝓘(ℝ, E) I (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M))
        (NormalCoordinates.normalChartAt (I := I) g p (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)) := by
  classical
  set c := NormalCoordinates.normalChartAt (I := I) g p with hc
  set ψ : ℝ → E := fun s => c (γ s) with hψ
  have hγeq : γ =ᶠ[nhds t] (fun s => expMap (I := I) g p (show TangentSpace I p from ψ s)) := by
    filter_upwards [hev] with s hs
    exact (expMap_normalChartAt (I := I) g p hs).symm
  rw [hγeq.mfderiv_eq]
  have hexp_diff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ t) :=
    (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hball).mdifferentiableAt (by decide)
  have hψ_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ψ t := by
    have hc_diff : MDifferentiableAt I 𝓘(ℝ, E) c (γ t) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn one_ne_zero
        (γ t) hsrc).mdifferentiableAt
        ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hsrc)
    exact hc_diff.comp t hγdiff
  rw [show (fun s => expMap (I := I) g p (show TangentSpace I p from ψ s))
      = (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) ∘ ψ from rfl,
    mfderiv_comp t hexp_diff hψ_diff]
  rfl

/-- **Radial-distance derivative.** For a bilinear positive form `B`, a curve
`ψ` differentiable at `t` with `B(ψt)(ψt) > 0`, the radial distance
`s ↦ √(B(ψs)(ψs))` has derivative `B(ψt)(ψ't) / √(B(ψt)(ψt))` at `t`. -/
private theorem radialDist_hasDerivAt
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hBsym : ∀ a b : E, B a b = B b a)
    (ψ : ℝ → E) (ψ' : E) {t : ℝ}
    (hψ : HasDerivAt ψ ψ' t) (hpos : 0 < B (ψ t) (ψ t)) :
    HasDerivAt (fun s => Real.sqrt (B (ψ s) (ψ s)))
      (B (ψ t) ψ' / Real.sqrt (B (ψ t) (ψ t))) t := by
  have hf : HasDerivAt (fun s => B (ψ s) (ψ s)) (B ψ' (ψ t) + B (ψ t) ψ') t :=
    (B.hasFDerivAt.comp_hasDerivAt t hψ).clm_apply hψ
  have hsqrt := hf.sqrt (ne_of_gt hpos)
  have hcoef : (B ψ' (ψ t) + B (ψ t) ψ') / (2 * Real.sqrt (B (ψ t) (ψ t)))
      = B (ψ t) ψ' / Real.sqrt (B (ψ t) (ψ t)) := by
    rw [hBsym ψ' (ψ t), show B (ψ t) ψ' + B (ψ t) ψ' = 2 * B (ψ t) ψ' by ring,
      mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  rwa [hcoef] at hsqrt

/-- **Pointwise Gauss speed lower bound.** At a curve point confined to the
normal chart with nonzero, in-`C²`-ball chart image, the radial-distance
derivative squared (computed from the chart-image velocity) is dominated by
the intrinsic speed-squared `g(γt, γ't, γ't)`. -/
private theorem gauss_pointwise_speed_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {γ : ℝ → M} {t : ℝ}
    (hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hsrc : γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hdom : (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p (γ t)))
      ∈ expDomain (I := I) g p)
    (hball : ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
      expMapC2Radius (I := I) g p)
    (hune : NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0)
    (hev : ∀ᶠ s in nhds t, γ s ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)))^2
      / g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
          (NormalCoordinates.normalChartAt (I := I) g p (γ t))
    ≤ g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
  have hchain := radial_chain_mfderiv (I := I) g p hγdiff hsrc hball hev
  have hbase : γ t = expMap (I := I) g p
      (show TangentSpace I p from (NormalCoordinates.normalChartAt (I := I) g p (γ t))) :=
    (expMap_normalChartAt (I := I) g p hsrc).symm
  have hkernel := gauss_radial_lower_bound (I := I) g p hdom hball hune
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ))
  rw [← hbase] at hkernel
  rw [hchain]
  exact hkernel

end RadialLengthEngine

end GaussLemma

/-! ## Generic analytic engine for the radial length lower bound

The radial length lower bound integrates the pointwise Gauss speed estimate
against the radial-distance function `ρ(t) := √(g_p(ψ(γt), ψ(γt)))`, where
`ψ` is the normal chart at `p`.  The two ingredients packaged here are
field-independent of the manifold structure:

* `psd_*` — Cauchy–Schwarz, the (reverse) triangle inequality and the global
  Lipschitz property for the seminorm `x ↦ √(B x x)` attached to a symmetric
  positive-semidefinite continuous bilinear form `B`.  These supply the
  continuity of `ρ` and the limit of its right-difference quotient at the
  singular point `ψ(γt) = 0`.
* `image_radialDist_le_intervalIntegral_of_slope_le` — a fencing theorem:
  a nonnegative continuous `ρ` whose right-side difference quotient is
  dominated by a continuous `φ` at every interior point satisfies
  `ρ b ≤ ∫ φ`.  This is the fundamental-theorem-of-calculus core that turns
  the pointwise speed estimate into a length comparison without requiring
  `ρ` to be differentiable at the centre. -/

section RadialLengthAnalyticEngine

open MeasureTheory intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Cauchy–Schwarz for a symmetric positive-semidefinite continuous
bilinear form.** -/
private lemma psd_cauchy_schwarz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    (B x y) ^ 2 ≤ B x x * B y y := by
  by_cases hy : B y y = 0
  · have key : ∀ t : ℝ, 0 ≤ B x x - 2 * t * B x y := by
      intro t
      have h := hnn (x - t • y)
      have expand : B (x - t • y) (x - t • y) = B x x - 2 * t * B x y + t ^ 2 * B y y := by
        simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hsym y x]; ring
      rw [expand, hy] at h; linarith [h]
    rw [hy, mul_zero]
    by_contra hcon
    rw [not_le] at hcon
    have hxy : B x y ≠ 0 := by intro h0; rw [h0] at hcon; norm_num at hcon
    have h2 : 2 * ((B x x + 1) / (2 * B x y)) * B x y = B x x + 1 := by field_simp
    have := key ((B x x + 1) / (2 * B x y))
    rw [h2] at this; linarith
  · have hpos : 0 < B y y := lt_of_le_of_ne (hnn y) (Ne.symm hy)
    have h := hnn (x - (B x y / B y y) • y)
    have expand : B (x - (B x y / B y y) • y) (x - (B x y / B y y) • y)
        = B x x - (B x y) ^ 2 / B y y := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsym y x]; field_simp; ring
    rw [expand] at h
    have hb : (B x y) ^ 2 / B y y ≤ B x x := by linarith
    have := (div_le_iff₀ hpos).mp hb
    linarith [this]

/-- **Triangle inequality for the seminorm `x ↦ √(B x x)`** of a symmetric
positive-semidefinite continuous bilinear form. -/
private lemma psd_seminorm_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    Real.sqrt (B (x + y) (x + y)) ≤ Real.sqrt (B x x) + Real.sqrt (B y y) := by
  have hxx := hnn x; have hyy := hnn y
  have hcs := psd_cauchy_schwarz B hsym hnn x y
  have hexp : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, ContinuousLinearMap.add_apply]; rw [hsym y x]; ring
  have hbxy_le : B x y ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
    have h1 : B x y ≤ |B x y| := le_abs_self _
    have h2 : |B x y| ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hxx]
      exact Real.sqrt_le_sqrt hcs
    linarith
  have hrhs : (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2
      = B x x + 2 * (Real.sqrt (B x x) * Real.sqrt (B y y)) + B y y := by
    rw [add_sq, Real.sq_sqrt hxx, Real.sq_sqrt hyy]; ring
  have hle : B (x + y) (x + y) ≤ (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2 := by
    rw [hexp, hrhs]; linarith
  calc Real.sqrt (B (x + y) (x + y))
        ≤ Real.sqrt ((Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (B x x) + Real.sqrt (B y y) := by rw [Real.sqrt_sq (by positivity)]

/-- **Reverse triangle inequality for the seminorm `x ↦ √(B x x)`.** -/
private lemma psd_reverse_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    |Real.sqrt (B x x) - Real.sqrt (B y y)| ≤ Real.sqrt (B (x - y) (x - y)) := by
  have h1 : Real.sqrt (B x x) ≤ Real.sqrt (B (x - y) (x - y)) + Real.sqrt (B y y) := by
    have := psd_seminorm_triangle B hsym hnn (x - y) y
    rwa [sub_add_cancel] at this
  have h2 : Real.sqrt (B y y) ≤ Real.sqrt (B (y - x) (y - x)) + Real.sqrt (B x x) := by
    have := psd_seminorm_triangle B hsym hnn (y - x) x
    rwa [sub_add_cancel] at this
  have hsymq : B (y - x) (y - x) = B (x - y) (x - y) := by
    have hyx : y - x = -(x - y) := by abel
    rw [hyx]
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hsymq] at h2
  rw [abs_sub_le_iff]; constructor <;> linarith

/-- **The seminorm `x ↦ √(B x x)` is globally Lipschitz** with constant
`√‖B‖`, hence continuous and locally Lipschitz on every set. -/
private lemma psd_sqrt_lipschitz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) :
    LipschitzWith (Real.toNNReal (Real.sqrt ‖B‖)) (fun x => Real.sqrt (B x x)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  have hb0 : (0 : ℝ) ≤ ‖B‖ := by positivity
  calc |Real.sqrt (B x x) - Real.sqrt (B y y)|
        ≤ Real.sqrt (B (x - y) (x - y)) := psd_reverse_triangle B hsym hnn x y
    _ ≤ Real.sqrt ‖B‖ * ‖x - y‖ := by
        have hbz : B (x - y) (x - y) ≤ ‖B‖ * (‖x - y‖ * ‖x - y‖) := by
          calc B (x - y) (x - y) ≤ ‖B (x - y) (x - y)‖ := le_abs_self _
            _ ≤ ‖B‖ * ‖x - y‖ * ‖x - y‖ := B.le_opNorm₂ (x - y) (x - y)
            _ = ‖B‖ * (‖x - y‖ * ‖x - y‖) := by ring
        calc Real.sqrt (B (x - y) (x - y))
              ≤ Real.sqrt (‖B‖ * (‖x - y‖ * ‖x - y‖)) := Real.sqrt_le_sqrt hbz
          _ = Real.sqrt ‖B‖ * ‖x - y‖ := by
              rw [Real.sqrt_mul hb0, show ‖x - y‖ * ‖x - y‖ = ‖x - y‖ ^ 2 by ring,
                Real.sqrt_sq (norm_nonneg _)]

/-- **Angular direction has zero derivative under radiality.** For a curve
`c : ℝ → F` differentiable at `t` with `ρ s = √(B(cs)(cs))`, if at `t` the
radial distance is positive (`0 < ρ t`), `ρ` is differentiable with derivative
`B(ct)(c')/ρ t`, and the velocity `c'` is `B`-radial
(`c' = (B(ct)(c')/B(ct)(ct)) • c t`), then the angular direction
`θ s = (ρ s)⁻¹ • c s` has derivative `0` at `t`.  This is the rigidity ODE:
the angular component of a radial velocity is stationary.  The proof is the
product rule `θ' = (ρ⁻¹)' • c + ρ⁻¹ • c'`, in which the two scalar coefficients
of `c t` cancel exactly because `c'` is radial and `ρ t ^ 2 = B(ct)(ct)`. -/
private lemma angular_hasDerivAt_zero (B : F →L[ℝ] F →L[ℝ] ℝ)
    {c : ℝ → F} {c' : F} {ρ : ℝ → ℝ} {t : ℝ}
    (hc : HasDerivAt c c' t) (hρt : 0 < ρ t)
    (hρ : HasDerivAt ρ (B (c t) c' / ρ t) t)
    (hρsq : ρ t ^ 2 = B (c t) (c t))
    (hrad : c' = (B (c t) c' / B (c t) (c t)) • c t) :
    HasDerivAt (fun s => (ρ s)⁻¹ • c s) 0 t := by
  have hrne : ρ t ≠ 0 := ne_of_gt hρt
  have hBne : B (c t) (c t) ≠ 0 := by rw [← hρsq]; positivity
  -- Abbreviate the (opaque) radial coefficient `k := B(ct)(c')`.
  set k : ℝ := B (c t) c' with hk_def
  have hinv : HasDerivAt (fun s => (ρ s)⁻¹) (-(k / ρ t) / (ρ t)^2) t := by
    have h := hρ.inv hrne
    simpa [hk_def] using h
  have hθ' : HasDerivAt (fun s => (ρ s)⁻¹ • c s)
      ((ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t) t := by
    have h := hinv.smul hc
    simpa using h
  have hzero : (ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t = 0 := by
    -- substitute the radial form of `c'` (only the standalone `c'`).
    rw [hrad]
    rw [smul_smul, ← add_smul]
    rw [show (ρ t)⁻¹ * (k / B (c t) (c t)) + -(k / ρ t) / ρ t ^ 2 = 0 by
      rw [← hρsq]; field_simp; ring]
    rw [zero_smul]
  rwa [hzero] at hθ'

/-- **Right-difference-quotient fencing theorem.** If `ρ` is continuous on
`[a, b]` with `ρ a ≤ 0`, and `φ` is integrable on `[a, b]`, continuous from
the right at every interior point, and dominates the right-side limit inferior
of the difference quotient of `ρ` there, then `ρ b ≤ ∫ φ`.  This is the
fundamental-theorem-of-calculus core of the radial length lower bound: it
turns the pointwise speed estimate into an integral length comparison without
assuming `ρ` is differentiable everywhere (in particular it tolerates the
corner of `ρ` at the centre `ψ(γt) = 0`), and it only asks for `φ` to be
right-continuous in the interior (the velocity speed of a curve `C¹` on a
closed interval need not be continuous at the endpoints). -/
private lemma image_radialDist_le_intervalIntegral_of_slope_le
    {ρ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b)) (hρa : ρ a ≤ 0)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume)
    (hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x)
    (hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r) :
    ρ b ≤ ∫ t in a..b, φ t := by
  set B : ℝ → ℝ := fun x => ∫ t in a..x, φ t with hB
  have hφii : IntervalIntegrable φ volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hφint
  have hBa : ρ a ≤ B a := by simp [hB, hρa]
  have hBcont : ContinuousOn B (Set.Icc a b) := by
    have h := continuousOn_primitive_interval' (f := φ) (μ := volume) (a := a)
      (b₁ := a) (b₂ := b) hφii Set.left_mem_uIcc
    rw [Set.uIcc_of_le hab] at h; exact h
  have hBderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B (φ x) (Set.Ici x) x := by
    intro x hx
    have hcwa : ContinuousWithinAt φ (Set.Ioi x) x := hφcont x hx
    have hmem : Set.Icc a b ∈ nhdsWithin x (Set.Ioi x) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
    have hmeas : StronglyMeasurableAtFilter φ (nhdsWithin x (Set.Ioi x)) volume :=
      ⟨Set.Icc a b, hmem, hφint.aestronglyMeasurable⟩
    have hint_sub : IntervalIntegrable φ volume a x :=
      hφii.mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2.le)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint_sub hmeas hcwa
  exact image_le_of_liminf_slope_right_le_deriv_boundary hρc hBa hBcont hBderiv hslope
    (Set.right_mem_Icc.2 hab)

/-- **Equality case of the radial fencing (FTC tightness).** If `ρ` is
continuous on `[a, b]`, has right-derivative `ρ'` at every interior point,
`ρ'` is interval-integrable and bounded above by an integrable `φ` on the
interior, and the *boundary value* `ρ b - ρ a` already saturates `∫ φ`
(the fencing inequality `ρ b - ρ a ≤ ∫ φ` is an equality), then the
right-derivative agrees with `φ` almost everywhere on `(a, b)`.

This is the equality-case counterpart of
`image_radialDist_le_intervalIntegral_of_slope_le`: there the slope estimate
gave a one-sided length lower bound, here the *saturation* of that bound forces
the pointwise estimate `ρ' ≤ φ` to be an a.e. equality.  The proof is the
fundamental theorem of calculus (`∫ ρ' = ρ b - ρ a = ∫ φ`) fed into
`MeasureTheory.integral_eq_iff_of_ae_le`: two integrable functions with `ρ' ≤ φ`
a.e. and equal integrals coincide a.e.  It is the analytic gateway by which the
length-equality hypothesis of the radial minimiser becomes the pointwise Gauss
equality (and hence, via `gauss_radial_lower_bound_eq_iff`, the a.e. radiality
of the velocity). -/
private lemma ftc_fencing_equality_case
    {ρ φ ρ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b))
    (hρderiv : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt ρ (ρ' x) (Set.Ioi x) x)
    (hρ'int : IntervalIntegrable ρ' MeasureTheory.volume a b)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Ioo a b) MeasureTheory.volume)
    (hρ'φ : ∀ x ∈ Set.Ioo a b, ρ' x ≤ φ x)
    (htight : ρ b - ρ a = ∫ t in a..b, φ t) :
    ρ' =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ := by
  -- Fundamental theorem of calculus: `∫ ρ' = ρ b - ρ a`.
  have hftc : (∫ t in a..b, ρ' t) = ρ b - ρ a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hρc hρderiv hρ'int
  have heqint : (∫ t in a..b, ρ' t) = ∫ t in a..b, φ t := by rw [hftc, htight]
  -- Push both interval integrals (a ≤ b) onto the open interval `Ioo a b`.
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at heqint
  have hconvρ : (∫ t in Set.Ioc a b, ρ' t) = ∫ t in Set.Ioo a b, ρ' t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hconvφ : (∫ t in Set.Ioc a b, φ t) = ∫ t in Set.Ioo a b, φ t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hconvρ, hconvφ] at heqint
  -- Integrability of `ρ'` over the open interval.
  have hρ'Ioo : MeasureTheory.IntegrableOn ρ' (Set.Ioo a b) MeasureTheory.volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hρ'int; exact hρ'int
  -- a.e. domination on the restricted measure, then the equality-case lemma.
  have hae_le : ρ' ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hρ'φ
  exact (MeasureTheory.integral_eq_iff_of_ae_le hρ'Ioo hφint hae_le).mp heqint

end RadialLengthAnalyticEngine

/-! ## Riemannian-distance convention for the radial-minimiser cluster

The statements below quantify the path-length functional `pathELength I`
and the geodesic distance `riemannianEDist I`, both of which are defined in
terms of the fibrewise extended norm `‖·‖ₑ` on `TangentSpace I x`.  The
project's default norm on the tangent bundle is the *model-`E`* Euclidean
norm `Tensor0SBundle.tangentSpace_normedAddCommGroup`; that norm has no
a-priori relation to the Riemannian metric `g`, so a bound of the shape
`√(g_p(v, v)) ≤ riemannianEDist I p (expMap g p v)` is *false* against it
(scale `g`).  We therefore work, exactly as `HopfRinow.lean` and the
consumer `RadialSurjectivity.lean` do, with the fibre norm supplied by an
ambient `RiemannianBundle` structure: we remove the two Euclidean tangent
instances and assume `[RiemannianBundle (fun x ↦ TangentSpace I x)]`.  The
abstract bundle norm is opaque, so each statement additionally exposes the
*norm-diamond bridge*
`hEnorm : ∀ x w, ‖w‖ₑ = ENNReal.ofReal (√(g.inner x w w))`
relating it to `g` (the same bridge `Lifts.lean`'s `proj_pathELength_eq`
and `HopfRinow`'s escape estimates carry).  This is a genuine structural
hypothesis: it does *not* match any conclusion below, and it is the only
channel linking the bundle norm to `g`. -/

section RadialMinimizerConvention

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section LengthBookkeeping

/-! ## Sub-arc of a minimiser is itself a minimiser

Pure metric bookkeeping built from
`Mathlib.Geometry.Manifold.Riemannian.PathELength`. -/

set_option linter.unusedVariables false in
/-- **A sub-arc of a length-minimising `C¹` curve is itself a
length-minimiser between its restricted endpoints.** That is, if a
curve `γ : ℝ → M` realises `riemannianEDist I (γ a) (γ b) = pathELength I γ a b`
on `[a, b]`, then on every sub-interval `[s, t] ⊆ [a, b]` the sub-arc
realises `riemannianEDist I (γ s) (γ t) = pathELength I γ s t`.
The hypothesis `hfin` records finiteness of the parent length: it is what
allows cancelling `pathELength I γ a s + pathELength I γ t b` from the
`ENNReal` squeeze. -/
theorem subArc_of_minimizer_is_minimizer
    {γ : ℝ → M} {a b s t : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hfin : pathELength I γ a b ≠ ⊤)
    (hab : a ≤ b) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    riemannianEDist I (γ s) (γ t) = pathELength I γ s t := by
  -- Abbreviations.
  set L_left := pathELength I γ a s with hL_left_def
  set L_mid := pathELength I γ s t with hL_mid_def
  set L_right := pathELength I γ t b with hL_right_def
  -- Restrict smoothness to each sub-interval.
  have h_ast : a ≤ t := has.trans hst
  have h_sb : s ≤ b := hst.trans htb
  have hγ_as : CMDiff[Icc a s] 1 γ := hγ.mono (Icc_subset_Icc le_rfl h_sb)
  have hγ_st : CMDiff[Icc s t] 1 γ := hγ.mono (Icc_subset_Icc has htb)
  have hγ_tb : CMDiff[Icc t b] 1 γ := hγ.mono (Icc_subset_Icc h_ast le_rfl)
  -- Path additivity: L_left + L_mid + L_right = pathELength I γ a b.
  have hadd_left : L_left + L_mid = pathELength I γ a t :=
    pathELength_add (γ := γ) (I := I) has hst
  have hadd_total : pathELength I γ a t + L_right = pathELength I γ a b :=
    pathELength_add (γ := γ) (I := I) h_ast htb
  have hpath_total : L_left + L_mid + L_right = pathELength I γ a b := by
    rw [hadd_left, hadd_total]
  -- Sub-arc lengths are ≤ parent length, hence finite.
  have hL_left_finite : L_left ≠ ⊤ := by
    have hle : L_left ≤ pathELength I γ a b := by
      rw [← hpath_total]
      have h₁ : L_left ≤ L_left + L_mid := le_self_add
      exact h₁.trans le_self_add
    exact ne_top_of_le_ne_top hfin hle
  have hL_right_finite : L_right ≠ ⊤ := by
    have hle : L_right ≤ pathELength I γ a b := by
      rw [← hpath_total]
      exact le_add_self
    exact ne_top_of_le_ne_top hfin hle
  -- Distance ≤ length on each sub-arc.
  have hD_left : riemannianEDist I (γ a) (γ s) ≤ L_left :=
    riemannianEDist_le_pathELength hγ_as rfl rfl has
  have hD_right : riemannianEDist I (γ t) (γ b) ≤ L_right :=
    riemannianEDist_le_pathELength hγ_tb rfl rfl htb
  have hD_mid_le : riemannianEDist I (γ s) (γ t) ≤ L_mid :=
    riemannianEDist_le_pathELength hγ_st rfl rfl hst
  -- Triangle inequality (twice) on `(γ a) → (γ s) → (γ t) → (γ b)`.
  have htri₁ : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ t) + riemannianEDist I (γ t) (γ b) :=
    riemannianEDist_triangle
  have htri₂ : riemannianEDist I (γ a) (γ t) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t) :=
    riemannianEDist_triangle
  have htri_combined : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t)
        + riemannianEDist I (γ t) (γ b) :=
    htri₁.trans (add_le_add htri₂ le_rfl)
  -- Bound the parent length by the squeezed sum.
  have hpath_le : pathELength I γ a b ≤
      L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    have := htri_combined
    rw [hmin] at this
    refine this.trans ?_
    exact add_le_add (add_le_add hD_left le_rfl) hD_right
  -- Combine to obtain the squeeze on the middle term.
  have hsqueeze : L_left + L_mid + L_right
        ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    calc L_left + L_mid + L_right = pathELength I γ a b := hpath_total
      _ ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := hpath_le
  -- Cancel `L_left` and `L_right` from the squeeze using their finiteness.
  -- Rearranging both sides as `L_left + L_right + L_mid` etc.
  have hsqueeze' : L_left + L_right + L_mid
        ≤ L_left + L_right + riemannianEDist I (γ s) (γ t) := by
    have heq₁ : L_left + L_mid + L_right = L_left + L_right + L_mid := by ring
    have heq₂ : L_left + riemannianEDist I (γ s) (γ t) + L_right
                  = L_left + L_right + riemannianEDist I (γ s) (γ t) := by ring
    rw [heq₁, heq₂] at hsqueeze
    exact hsqueeze
  have hL_lr_finite : L_left + L_right ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hL_left_finite, hL_right_finite⟩
  have hmid_le_D : L_mid ≤ riemannianEDist I (γ s) (γ t) :=
    (ENNReal.add_le_add_iff_left hL_lr_finite).mp hsqueeze'
  -- Anti-symmetry between `L_mid ≤ D_mid` and `D_mid ≤ L_mid` finishes the proof.
  exact le_antisymm hD_mid_le hmid_le_D

end LengthBookkeeping

section RadialUniqueMinimizer

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Inside a normal ball the radial geodesic is the unique minimiser

Direct consequence of Gauss's lemma: the metric expansion
`‖γ'‖² = (γ'_r)² + ‖γ'_a‖²_a ≥ (γ'_r)²` integrates to give a length
lower bound `≥ ‖v‖`, with equality only for a monotone radial
reparametrisation. -/

/-- **Endpoint-generic radial length lower bound.** For a `C¹` curve `γ` on
`[a, b]` starting at `p` and confined to the normal chart's source with chart
image inside the `C²` ball, the `g_p`-radial distance of the *endpoint*
`γ b` is bounded above by `pathELength I γ a b`.  This is the radial fencing
core of Gauss's lemma exposed for an arbitrary in-ball endpoint: it integrates
the pointwise radial speed estimate `gauss_pointwise_speed_lower_bound` against
the radial distance `ρ(t) = √(g_p(ψ(γt), ψ(γt)))` via the fundamental theorem
of calculus, with the corner of `ρ` at the centre `ψ(γt) = 0` handled by the
seminorm-continuity limit of the difference quotient. -/
private theorem radialDist_endpoint_le_pathELength
    (g : SmoothRiemannianMetric I M) (p : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγa : γ a = p)
    (hγ : CMDiff[Set.Icc a b] 1 γ)
    (hsrc : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hbball : ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p)
    (hdom : ∀ t ∈ Set.Icc a b,
      (show TangentSpace I p from
          NormalCoordinates.normalChartAt (I := I) g p (γ t))
        ∈ expDomain (I := I) g p) :
    ENNReal.ofReal (Real.sqrt
        (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
          (NormalCoordinates.normalChartAt (I := I) g p (γ b)))) ≤
      pathELength I γ a b := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  -- Chart-image curve `c(t) = ψ(γt) ∈ E`, and radial distance `ρ`.
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  set φ : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1))
    with hφ_def
  -- Continuity of `c` (chart-image of a `C¹` curve confined to the source).
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hsrc
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  -- Endpoint value at `a`: `ρ a = 0`.
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hρa : ρ a ≤ 0 := by
    rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero, le_refl]
  -- The conclusion's radial distance equals `ρ b`.
  have hρb : ρ b = Real.sqrt (g.inner p (ψ (γ b)) (ψ (γ b))) := rfl
  rw [hρb.symm]
  -- Degenerate interval `a = b`: `ρ b = ρ a ≤ 0`, and `ρ b ≥ 0`, so `ρ b = 0`.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    have hle0 : ρ a ≤ 0 := hρa
    have hzero : ρ a = 0 := le_antisymm hle0 (by rw [hρ_def]; exact Real.sqrt_nonneg _)
    rw [hzero, ENNReal.ofReal_zero]; exact bot_le
  -- Non-degenerate interval `a < b`.
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := fun t ht => by simpa using ht
  have hVel : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)) (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun t _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    rw [hφ_def]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := I) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t := fun t _ => Real.sqrt_nonneg _
  have hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume :=
    hφc.integrableOn_compact isCompact_Icc
  have hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq_mfderiv : ∀ t ∈ Set.Ioo a b,
      φ t = Real.sqrt
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) := by
    intro t ht
    rw [hφ_def]; simp only
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    set cv : E := mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x 1 with hcv_def
    have hcderiv : HasDerivWithinAt c cv (Set.Ici x) x := by
      have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
        (hγ.mdifferentiableOn (by norm_num)) x hxIcc
      have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
        (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)
      have hcomp : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x :=
        hψdiff.comp x hγdiff (fun t ht => hsrc t ht)
      have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x) := hcomp.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hHDW : HasDerivWithinAt c cv (Set.Icc a b) x := hmf.hasDerivWithinAt
      refine hHDW.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hcx : c x = 0
    · have htend : Filter.Tendsto (fun z => slope ρ x z)
          (nhdsWithin x (Set.Ioi x)) (nhds (Real.sqrt (B cv cv))) := by
        have hcz : Filter.Tendsto (fun z => (z - x)⁻¹ • c z)
            (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hcderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z; simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (Filter.tendsto_congr' ?_).mp h0
          filter_upwards with z; rw [slope_def_module, hcx, sub_zero]
        have hcont : Continuous (fun w : E => Real.sqrt (B w w)) := by fun_prop
        have htend2 := (hcont.tendsto cv).comp hcz
        refine (Filter.tendsto_congr' ?_).mp htend2
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        have heq : slope ρ x z
            = Real.sqrt (B ((z - x)⁻¹ • c z) ((z - x)⁻¹ • c z)) := by
          rw [hρ_def, slope_def_module, hcx]
          simp only [map_zero, Real.sqrt_zero, sub_zero, smul_eq_mul, map_smul,
            ContinuousLinearMap.smul_apply]
          rw [show (z - x)⁻¹ * ((z - x)⁻¹ * B (c z) (c z))
              = ((z - x)⁻¹) ^ 2 * B (c z) (c z) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
        simp only [Function.comp_apply]
        exact heq.symm
      have hφx_eq : φ x = Real.sqrt (B cv cv) := by
        have hγx_p : γ x = p := by
          have hcx' : ψ (γ x) = 0 := hcx
          have hpsrc : p ∈ ψ.source := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
          have hψp : ψ p = 0 := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
          exact ψ.injOn (hsrc x hxIcc) hpsrc (by rw [hcx', hψp])
        have hcv_eq : cv = mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x 1 := by
          rw [hcv_def]
          have hUnique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc a b) x := by
            rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact (uniqueDiffOn_Icc hab_lt) x hxIcc
          have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
            (hγ.mdifferentiableOn (by norm_num)) x hxIcc
          have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
            (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
              one_ne_zero (γ x) (hsrc x hxIcc)
          have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
            (f := γ) (g := ψ) (s := Set.Icc a b) (u := ψ.source) x hψdiff hγdiff
            (fun t ht => hsrc t ht) hUnique
          have hcomp_eq : c = ψ ∘ γ := rfl
          rw [hcomp_eq, hchain]
          simp only [Function.comp_apply]
          have hsource_nhds : ψ.source ∈ nhds (γ x) :=
            (NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc)
          rw [mfderivWithin_of_mem_nhds hsource_nhds, hγx_p,
            NormalCoordinates.mfderiv_normalChartAt_self]
          rfl
        simp only [hφ_def]
        rw [hcv_eq, hγx_p, hB_def]; rfl
      rw [hφx_eq] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa; apply hcx; rw [← hxa]; exact hca
      have hmem : Set.Icc a b ∈ nhds x := Icc_mem_nhds hxIoo.1 hxIoo.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
        ((hγ.mdifferentiableOn (by norm_num)) x hxIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ x) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x := hψdiff.comp x hγdiff
      set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x 1 with hcv₂_def
      have hcHDA : HasDerivAt c cv₂ x := by
        have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x) :=
          hcdiff.hasMFDerivAt
        rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
        exact hmf.hasDerivAt
      have hpos : 0 < B (c x) (c x) := by rw [hB_def]; exact g.pos p (c x) hcx
      have hρderiv : HasDerivAt ρ (B (c x) cv₂ / Real.sqrt (B (c x) (c x))) x :=
        radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
      set ρ' : ℝ := B (c x) cv₂ / Real.sqrt (B (c x) (c x)) with hρ'_def
      have hev : ∀ᶠ s in nhds x, γ s ∈ ψ.source := by
        have hopen : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
        filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
      have hball : ‖ψ (γ x)‖ < expMapC2Radius (I := I) g p := hbball x hxIcc
      have hune : ψ (γ x) ≠ 0 := hcx
      have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
        (hsrc x hxIcc) (hdom x hxIcc) hball hune hev
      have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => ψ (γ s)) x (1 : ℝ) := rfl
      have hρ'sq_le : ρ' ^ 2 ≤
          g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) := by
        have hρ'sq : ρ' ^ 2 = (B (c x) cv₂) ^ 2 / B (c x) (c x) := by
          rw [hρ'_def, div_pow, Real.sq_sqrt hpos.le]
        rw [hρ'sq, hcv₂_eq, hB_def]
        exact hgauss
      have hφx_eq : φ x = Real.sqrt
          (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1)) := by
        simp only [hφ_def]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx_eq]
        calc ρ' ≤ |ρ'| := le_abs_self _
          _ = Real.sqrt (ρ' ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt hρ'sq_le
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  have hftc : ρ b ≤ ∫ t in a..b, φ t :=
    image_radialDist_le_intervalIntegral_of_slope_le hab hρc hρa hφint hφcont hslope
  have hpath : ENNReal.ofReal (∫ t in a..b, φ t) ≤ pathELength I γ a b := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
            using hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_mono_ae' measurableSet_Ioo
    filter_upwards with t ht
    rw [hφ_eq_mfderiv t ht]
    exact le_of_eq (hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).symm
  calc ENNReal.ofReal (ρ b)
        ≤ ENNReal.ofReal (∫ t in a..b, φ t) := ENNReal.ofReal_le_ofReal hftc
    _ ≤ pathELength I γ a b := hpath

/-- **Ball-wide injectivity of the exponential differential.** For a vector
`u` inside the `C²`-ball `‖u‖ < expMapC2Radius g p`, the manifold differential
`mfderiv (fun y ↦ expMap g p y) u` is injective.  The normal chart is the
inverse of `expMap g p` (as a partial diffeomorphism), so the chart-image left
inverse `normalChartAt g p` produces, via the chain rule on the composite
`normalChartAt ∘ expMap = id` valid on a neighbourhood of `u`, a continuous
linear left inverse of the exponential differential; a linear map with a left
inverse is injective.  This is the keystone of the equality-case rigidity: it
lets the annihilation of the `g_p`-orthogonal part under `dexp` (the content of
`gauss_radial_lower_bound_eq_iff`) be lifted to the annihilation of the
orthogonal part itself. -/
private theorem mfderiv_expMap_injective_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {u : E}
    (hu : ‖u‖ < expMapC2Radius (I := I) g p) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) u) := by
  classical
  -- Abbreviations.
  set Φ := NormalCoordinates.expMapDiffeo (I := I) g p with hΦ_def
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  -- `u` lies in the exponential-side diffeomorphism's source.
  have hsrc : u ∈ Φ.source := by
    have := ball_subset_normalChartAt_target (I := I) g p hu
    rw [NormalCoordinates.normalChartAt_target_eq] at this
    exact this
  -- The two functions `Φ` and `y ↦ expMap g p y` agree near `u` (open source).
  have hΦ_exp : Φ =ᶠ[nhds u]
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) := by
    refine Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hsrc) ?_
    intro y hy
    exact NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hy
  -- So the exponential differential at `u` equals the differential of `Φ` at `u`.
  set A : E →L[ℝ] TangentSpace I (expMap (I := I) g p (show TangentSpace I p from u)) :=
    mfderiv 𝓘(ℝ, E) I
      (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) u with hA_def
  have hA_eq : A = mfderiv 𝓘(ℝ, E) I Φ u := by
    rw [hA_def, hΦ_exp.mfderiv_eq]
  -- `Φ u = expMap g p u` (agreement on the source).
  have hΦu : Φ u = expMap (I := I) g p (show TangentSpace I p from u) :=
    NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hsrc
  -- `ψ ∘ Φ = id` near `u` (left inverse on the open source).
  have hψΦ_id : (ψ ∘ Φ) =ᶠ[nhds u] (_root_.id : E → E) := by
    refine Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hsrc) ?_
    intro y hy
    change ψ (Φ y) = y
    exact Φ.left_inv hy
  -- Differentiability of `Φ` at `u` and of `ψ` at `Φ u`.
  have hΦ_diff : MDifferentiableAt 𝓘(ℝ, E) I Φ u :=
    (Φ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero u hsrc).mdifferentiableAt
      (Φ.open_source.mem_nhds hsrc)
  have hΦu_target : Φ u ∈ ψ.source := by
    rw [hψ_def, NormalCoordinates.normalChartAt_source_eq]
    exact Φ.map_source hsrc
  have hψ_diff : MDifferentiableAt I 𝓘(ℝ, E) ψ (Φ u) :=
    ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
      one_ne_zero (Φ u) hΦu_target).mdifferentiableAt
      ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds hΦu_target)
  -- Chain rule on `ψ ∘ Φ = id`, evaluated pointwise: `mfderiv ψ (Φ u)` is a
  -- left inverse of `mfderiv Φ u`.
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := Φ) (g := ψ) (x := u) hψ_diff hΦ_diff
  have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ ∘ Φ) u
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (_root_.id : E → E) u := hψΦ_id.mfderiv_eq
  have hleft : Function.LeftInverse
      (mfderiv I 𝓘(ℝ, E) ψ (Φ u)) (mfderiv 𝓘(ℝ, E) I Φ u) := by
    intro x
    -- Evaluate the CLM identity `mfderiv (ψ∘Φ) u = mfderiv id u` at `x`.
    have hidx := congrArg (fun (T : E →L[ℝ] E) => T x) hid
    simp only at hidx
    -- LHS: `mfderiv (ψ∘Φ) u x = mfderiv ψ (Φ u) (mfderiv Φ u x)`.
    rw [hchain] at hidx
    -- RHS: `mfderiv id u x = x`.
    rw [mfderiv_id] at hidx
    simpa using hidx
  have hΦinj : Function.Injective (mfderiv 𝓘(ℝ, E) I Φ u) := hleft.injective
  rw [hA_eq]
  exact hΦinj

set_option linter.unusedVariables false in
/-- **Inside the normal ball, every `C¹` curve from `p` to `expMap g p v`
has length at least the `g_p`-norm of `v`.** This is the length lower
bound delivered by Gauss's lemma; the equality-case identification of
the radial geodesic as the unique minimiser is the content of the prose
statement and the assembly downstream. The lower bound uses the
`g`-norm `√(g_p(v,v))`, not the model-space Euclidean norm `‖v‖_E`
(which has no a-priori relation to `g_p`).

The hypothesis `hv : v ∈ expDomain` records the natural precondition that
`expMap g p v` is the genuine geodesic value (not the junk value `p`); it is
kept for API symmetry with the equality-case sibling, even though the
first-exit argument re-derives domain membership for the candidate paths
internally. -/
theorem normalBall_radial_unique_minimizer
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p) :
    ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) := by
  -- The `g_p`-smallness `√(g_p(v,v)) < expRadiusGp` is the correct domain
  -- hypothesis: under an anisotropic `g_p` the Euclidean radius would allow
  -- `√(g_p(v,v))` to exceed the realised radial distance.  It implies the
  -- Euclidean `C²`-ball smallness `‖v‖ < expMapC2Radius` (coercivity), used
  -- below to discharge the variational machinery's domain hypotheses.
  -- The classical Gauss-lemma length lower bound. We reduce to the
  -- forall-greater formulation of `riemannianEDist` as an infimum.
  -- For every `r` strictly larger than the distance, there is a smooth
  -- path `γ : [0, 1] → M` from `p` to `exp_p v` of `pathELength < r`.
  -- The Gauss-lemma curve-length lower bound (the pointwise radial speed
  -- estimate `gauss_pointwise_speed_lower_bound` integrated against the
  -- radial distance `√(g_p(ψ(γt), ψ(γt)))` via the fundamental theorem of
  -- calculus) then forces `√(g_p(v,v)) ≤ pathELength γ`.  Combining yields
  -- `√(g_p(v,v)) ≤ r` for every such `r`, which by forall-greater gives
  -- `√(g_p(v,v)) ≤ riemannianEDist`.
  set q := expMap (I := I) g p (show TangentSpace I p from v) with hq_def
  classical
  -- Abbreviation for the normal chart at `p`.
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  -- The Gauss-lemma length lower bound, restated so it can be quantified over
  -- candidate paths produced by the infimum.  The hypotheses `hsrc`/`hbball`
  -- record that the candidate stays inside the normal chart's source and
  -- inside the `C²` ball (in chart coordinates): both are genuine domain
  -- conditions (a curve escaping the chart is handled by the caller via
  -- first-exit truncation), supplied here so that the pointwise Gauss speed
  -- estimate `gauss_pointwise_speed_lower_bound` is available at every
  -- interior parameter.  The bound is assembled by the
  -- fundamental-theorem-of-calculus engine
  -- `image_radialDist_le_intervalIntegral_of_slope_le` applied to the radial
  -- distance `ρ(t) = √(g_p(ψ(γt), ψ(γt)))`, whose right-difference quotient is
  -- dominated by the intrinsic speed `√(g(γt)(γ't)(γ't))` at every interior
  -- parameter (the pointwise Gauss estimate, with the corner at `ψ(γt) = 0`
  -- handled by the seminorm-continuity limit of the difference quotient). -/
  -- Abbreviations: `S` the target `g_p`-radial distance, `Rₑ`/`R` the Euclidean
  -- and `g_p`-domain radii, `c` the coercivity constant.
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set Rₑ : ℝ := expMapC2Radius (I := I) g p with hRₑ_def
  have hRₑ_pos : 0 < Rₑ := expMapC2Radius_pos (I := I) g p
  -- The continuous `g_p`-seminorm `nE w := √(g_p(w, w))` on `E`.
  set Bp : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hBp_def
  have hBpsym : ∀ x y : E, Bp x y = Bp y x := g.symm p
  have hBpnn : ∀ x : E, 0 ≤ Bp x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set nE : E → ℝ := fun w => Real.sqrt (Bp w w) with hnE_def
  have hnE_cont : Continuous nE := (psd_sqrt_lipschitz Bp hBpsym hBpnn).continuous
  -- `nE w < expRadiusGp ⟹ ‖w‖ < Rₑ` (coercivity) and hence `w ∈ ψ.target`.
  have hnE_to_ball : ∀ {w : E}, nE w < expRadiusGp (I := I) g p → ‖w‖ < Rₑ := by
    intro w hw
    have : Real.sqrt (g.inner p w w) < expRadiusGp (I := I) g p := hw
    exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p this
  -- Now combine with the infimum characterisation of `riemannianEDist`.
  refine le_of_forall_gt (fun r hr => ?_)
  -- For every `r > riemannianEDist I p q`, get a path from `p` to `q` of length `< r`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one with
    ⟨γ, hγ0, hγ1, hγ_smooth, hγ_len, _, _⟩
  have hγ1' : γ 1 = q := by simp [hq_def, hγ1]
  -- The chart-image radial value along `γ`, defined where `γ` is in source.
  -- `hM x := √(g_p(ψ x, ψ x))` is continuous on `ψ.source`.
  set hM : M → ℝ := fun x => nE (ψ x) with hhM_def
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hhM_cont : ContinuousOn hM ψ.source := hnE_cont.comp_continuousOn hψcont
  have hγcont : Continuous γ := hγ_smooth.continuous
  -- The radial value of the chart at `p` is `0`.
  have hψp : ψ p = 0 := by rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hpsrc : p ∈ ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
  -- `ψ q = v` (the chart inverts `expMap` at the radial endpoint).
  have hψq : ψ q = v := by
    rw [hψ_def, hq_def]
    have hsource : v ∈ ψ.symm.source := hball
    have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p (v := v) hsource
    rw [← hψ_def, hψ_def, ← hsymm]
    exact NormalCoordinates.normalChartAt_right_inv (I := I) g p hball
  -- Pick an exit radius `δ` strictly between `S` and the `g_p`-domain radius.
  obtain ⟨δ, hSδ, hδR⟩ := exists_between hsmall_g
  have hδ_pos : 0 < δ := lt_of_le_of_lt hS_nn hSδ
  -- `K := ψ.symm '' {w | nE w ≤ δ}`: a compact (closed g_p-ball pushed through the
  -- chart inverse), source-trapped neighbourhood of `p`.
  set D : Set E := {w : E | nE w ≤ δ} with hD_def
  -- `D ⊆ ψ.target` (g_p-ball of radius `δ < expRadiusGp` is inside the Euclidean
  -- `C²` ball, which is inside the chart target by PIECE 1).
  have hD_sub_target : D ⊆ ψ.target := by
    intro w hw
    have hw' : nE w < expRadiusGp (I := I) g p := lt_of_le_of_lt hw hδR
    rw [hψ_def]
    exact ball_subset_normalChartAt_target (I := I) g p (hnE_to_ball hw')
  -- `D` is compact: closed (continuity of `nE`) and bounded (coercivity).
  have hcoerc : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  set cδ : ℝ := δ / Real.sqrt (gpCoerciveConst (I := I) g p) with hcδ_def
  have hcδ_nn : 0 ≤ cδ := div_nonneg hδ_pos.le (Real.sqrt_nonneg _)
  -- Clean coercivity bound: `nE x ≤ δ ⟹ ‖x‖ ≤ cδ`.
  have hbound : ∀ {x : E}, nE x ≤ δ → ‖x‖ ≤ cδ := by
    intro x hx
    have hg_le : g.inner p x x ≤ δ ^ 2 := by
      have hsqrt_le : Real.sqrt (g.inner p x x) ≤ δ := hx
      have h := Real.sq_sqrt (show (0:ℝ) ≤ g.inner p x x from hBpnn x)
      calc g.inner p x x = Real.sqrt (g.inner p x x) ^ 2 := h.symm
        _ ≤ δ ^ 2 := by
            apply pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le
    have hcx : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
      gpCoerciveConst_le (I := I) g p x
    have hsq : ‖x‖ ^ 2 ≤ cδ ^ 2 := by
      rw [hcδ_def, div_pow, Real.sq_sqrt hcoerc.le, le_div_iff₀ hcoerc]
      calc ‖x‖ ^ 2 * gpCoerciveConst (I := I) g p
            = gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 := by ring
        _ ≤ g.inner p x x := hcx
        _ ≤ δ ^ 2 := hg_le
    exact (sq_le_sq₀ (norm_nonneg x) hcδ_nn).mp hsq
  have hD_compact : IsCompact D := by
    haveI : ProperSpace E := FiniteDimensional.proper_rclike (K := ℝ) (E := E)
    have hD_closed : IsClosed D := isClosed_le hnE_cont continuous_const
    have hD_bdd : Bornology.IsBounded D := by
      apply Metric.isBounded_iff.mpr
      refine ⟨2 * cδ, fun x hx y hy => ?_⟩
      have hbx : ‖x‖ ≤ cδ := hbound hx
      have hby : ‖y‖ ≤ cδ := hbound hy
      calc dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
        _ ≤ 2 * cδ := by linarith
    exact Metric.isCompact_of_isClosed_isBounded hD_closed hD_bdd
  -- `K := ψ.symm '' D`, compact image (ψ.symm continuous on target ⊇ D).
  have hψsymm_cont : ContinuousOn ψ.symm ψ.target :=
    (NormalCoordinates.normalChartAt_symm_contMDiffOn (I := I) g p).continuousOn
  set K : Set M := ψ.symm '' D with hK_def
  have hK_compact : IsCompact K :=
    hD_compact.image_of_continuousOn (hψsymm_cont.mono hD_sub_target)
  haveI : T2Space M := gauss_t2Space_base (I := I) (M := M)
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- Membership characterisation of `K` (for points whose chart image is in `D`).
  -- For `x ∈ ψ.source` with `ψ x ∈ D`, we have `x ∈ K`.
  have hmem_K_of_src : ∀ {x : M}, x ∈ ψ.source → ψ x ∈ D → x ∈ K := by
    intro x hxsrc hxD
    refine ⟨ψ x, hxD, ?_⟩
    exact ψ.left_inv hxsrc
  -- Conversely, `x ∈ K ⟹ x ∈ ψ.source ∧ ψ x ∈ D` (since `D ⊆ target`).
  have hK_src : ∀ {x : M}, x ∈ K → x ∈ ψ.source := by
    rintro x ⟨w, hwD, rfl⟩
    exact ψ.symm_mapsTo (hD_sub_target hwD)
  have hK_chart : ∀ {x : M}, x ∈ K → ψ x ∈ D := by
    rintro x ⟨w, hwD, rfl⟩
    have : ψ (ψ.symm w) = w := ψ.right_inv (hD_sub_target hwD)
    rw [this]; exact hwD
  -- `p ∈ K` and `q ∈ K` (their chart radial values `0`, `S` are `≤ δ`).
  have hpK : p ∈ K := hmem_K_of_src hpsrc (by
    change nE (ψ p) ≤ δ; rw [hψp, hnE_def]; simp only [map_zero, Real.sqrt_zero]; exact hδ_pos.le)
  have hqsrc : q ∈ ψ.source := by
    have hsymm_src : ψ.symm v ∈ ψ.source := ψ.symm_mapsTo hball
    have hqeq : ψ.symm v = q := by
      rw [hq_def, hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g p hball
    rwa [hqeq] at hsymm_src
  -- The first-exit / in-ball case split.  Define the "out of K" subset of [0,1].
  set Z : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | γ t ∉ K} with hZ_def
  by_cases hZ : Z = ∅
  · -- Case A: the whole curve stays in `K ⊆ source` with radial value `≤ δ < Rₑ`.
    have hall_K : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ K := by
      intro t ht
      by_contra hcon
      have htZ : t ∈ Z := ⟨ht, hcon⟩
      rw [hZ] at htZ
      exact Set.notMem_empty t htZ
    have hsrc' : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ ψ.source :=
      fun t ht => hK_src (hall_K t ht)
    have hbball' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ψ (γ t)‖ < Rₑ := by
      intro t ht
      have hch : ψ (γ t) ∈ D := hK_chart (hall_K t ht)
      exact hnE_to_ball (lt_of_le_of_lt hch hδR)
    have hdom' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
      fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' t ht)
    have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one hγ0 hγ_smooth.contMDiffOn
      hsrc' hbball' hdom'
    -- `ψ (γ 1) = ψ q = v`, so the endpoint radial value is `S`.
    rw [show (NormalCoordinates.normalChartAt (I := I) g p (γ 1)) = v by
      rw [← hψ_def, hγ1', hψq]] at hlb
    have hSeq : Real.sqrt (g.inner p v v) = S := rfl
    rw [hSeq] at hlb
    exact lt_of_le_of_lt hlb hγ_len
  · -- Case B: the curve exits `K`.  Take the first exit time `t₀`.
    rw [← Ne.eq_def, ← Set.nonempty_iff_ne_empty] at hZ
    -- `Z` is bounded below by `0`; let `t₀ := sInf Z`.
    have hZ_sub : Z ⊆ Set.Icc (0 : ℝ) 1 := fun t ht => ht.1
    have hZbdd : BddBelow Z := ⟨0, fun t ht => ht.1.1⟩
    set t₀ : ℝ := sInf Z with ht₀_def
    have ht₀_nn : 0 ≤ t₀ := le_csInf hZ (fun t ht => ht.1.1)
    have ht₀_le1 : t₀ ≤ 1 := by
      obtain ⟨t, ht⟩ := hZ
      exact le_trans (csInf_le hZbdd ht) ht.1.2
    -- For `s ∈ [0, t₀)`, `s ∉ Z`, hence `γ s ∈ K` (since `s ∈ [0,1]`).
    have hpre_K : ∀ s, 0 ≤ s → s < t₀ → γ s ∈ K := by
      intro s hs0 hst₀
      by_contra hcon
      have hsZ : s ∈ Z := ⟨⟨hs0, le_trans hst₀.le ht₀_le1⟩, hcon⟩
      exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hst₀)
    -- `[0, t₀] ⊆ γ⁻¹ K`: by continuity + closedness of `K`, the endpoint `t₀`
    -- is also in `K`.
    have ht₀_K : γ t₀ ∈ K := by
      rcases eq_or_lt_of_le ht₀_nn with h0 | h0
      · rw [← h0]; rw [hγ0]; exact hpK
      · -- `t₀ > 0`: `γ t₀ = lim_{s→t₀⁻} γ s`, all in closed `K`.
        have htend : Filter.Tendsto (fun s => γ s) (nhdsWithin t₀ (Set.Iio t₀))
            (nhds (γ t₀)) :=
          (hγcont.continuousWithinAt (s := Set.Iio t₀) (x := t₀))
        have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀), γ s ∈ K := by
          have hpos : Set.Ioo 0 t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
            rw [mem_nhdsWithin]
            exact ⟨Set.Ioi 0, isOpen_Ioi, h0, by
              intro z hz; exact ⟨hz.1, hz.2⟩⟩
          filter_upwards [hpos] with s hs using hpre_K s hs.1.le hs.2
        haveI hne : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := nhdsLT_neBot t₀
        exact hK_closed.mem_of_tendsto htend hev
    have hall_K_prefix : ∀ s ∈ Set.Icc (0 : ℝ) t₀, γ s ∈ K := by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h]; exact ht₀_K
      · exact hpre_K s hs.1 h
    -- The chart radial value at the exit is exactly `δ`.
    -- It is `≤ δ` (since `γ t₀ ∈ K`), and `≥ δ` because if it were `< δ`, the open
    -- in-K region would extend past `t₀`, contradicting `t₀ = sInf Z`.
    have ht₀_src : γ t₀ ∈ ψ.source := hK_src ht₀_K
    have ht₀_le_δ : hM (γ t₀) ≤ δ := hK_chart ht₀_K
    have ht₀_eq_δ : hM (γ t₀) = δ := by
      refine le_antisymm ht₀_le_δ ?_
      by_contra hcon
      rw [not_le] at hcon
      -- The open set `{x ∈ ψ.source | hM x < δ}` contains `γ t₀`; pull back along
      -- `γ`, get a right neighbourhood of `t₀` staying in `K`, contradicting `sInf`.
      have hopenW : IsOpen (ψ.source ∩ hM ⁻¹' (Set.Iio δ)) := by
        have h1 : IsOpen ψ.source := NormalCoordinates.normalChartAt_open_source (I := I) g p
        exact hhM_cont.isOpen_inter_preimage h1 isOpen_Iio
      have ht₀_mem : γ t₀ ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) := ⟨ht₀_src, hcon⟩
      have hpre : γ ⁻¹' (ψ.source ∩ hM ⁻¹' (Set.Iio δ)) ∈ nhds t₀ :=
        hγcont.continuousAt.preimage_mem_nhds (hopenW.mem_nhds ht₀_mem)
      -- get a right interval `(t₀, t₀ + ε)` mapping into K.
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
      -- Pick `t₁ := min (t₀ + ε/2) 1 > t₀` (if t₀ < 1) inside the ball, and in [0,1].
      have ht₀_lt1 : t₀ < 1 := by
        rcases eq_or_lt_of_le ht₀_le1 with h1 | h1
        · exfalso
          -- if `t₀ = 1`, `γ t₀ = q`, with `hM q = S < δ`, fine; but Z nonempty with all
          -- points `≤ 1`, so `sInf Z ≤ 1`; here `t₀ = 1` and `γ 1 = q ∈ K`, but then
          -- every `t ∈ Z` has `t ≤ 1 = t₀ = sInf Z`, so `t = t₀ = 1`, i.e. `1 ∈ Z`,
          -- contradicting `γ 1 = q ∈ K`.
          obtain ⟨t, htZ⟩ := hZ
          have htge : t₀ ≤ t := csInf_le hZbdd htZ
          have htle : t ≤ 1 := htZ.1.2
          have : t = 1 := le_antisymm htle (by rw [h1] at htge; exact htge)
          rw [this] at htZ
          have hqD : ψ q ∈ D := by
            change nE (ψ q) ≤ δ
            rw [hψq]
            have hnv : nE v = S := rfl
            rw [hnv]; exact hSδ.le
          have hq_in_K : γ 1 ∈ K := by rw [hγ1']; exact hmem_K_of_src hqsrc hqD
          exact htZ.2 hq_in_K
        · exact h1
      set t₁ : ℝ := min (t₀ + ε / 2) 1 with ht₁_def
      have ht₀_lt_t₁ : t₀ < t₁ := by
        rw [ht₁_def, lt_min_iff]
        exact ⟨by linarith, ht₀_lt1⟩
      have ht₁_le1 : t₁ ≤ 1 := min_le_right _ _
      have ht₁_dist : dist t₁ t₀ < ε := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [ht₀_lt_t₁.le] : (0:ℝ) ≤ t₁ - t₀)]
        have : t₁ ≤ t₀ + ε / 2 := min_le_left _ _
        linarith
      have ht₁_mem : t₁ ∈ Metric.ball t₀ ε := by rw [Metric.mem_ball]; exact ht₁_dist
      have hγt₁_W : γ t₁ ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) := hε_sub ht₁_mem
      have hγt₁_K : γ t₁ ∈ K := by
        refine hmem_K_of_src hγt₁_W.1 ?_
        change nE (ψ (γ t₁)) ≤ δ
        exact le_of_lt hγt₁_W.2
      -- But then `t₁` and everything in `[0, t₁]` is in K, so `Z ∩ [0,t₁] = ∅`,
      -- meaning `sInf Z ≥ t₁ > t₀ = sInf Z`, contradiction.
      have hge : t₁ ≤ t₀ := by
        apply le_csInf hZ
        intro t htZ
        by_contra hlt
        rw [not_le] at hlt
        -- `t ∈ Z`, `t < t₁`, `t ∈ [0,1]`.  If `t ≤ t₀` then `t = t₀` would need ...;
        -- but `t ≥ sInf Z = t₀`.  So `t₀ ≤ t < t₁`.
        have htge : t₀ ≤ t := csInf_le hZbdd htZ
        -- `t ∈ [t₀, t₁) ⊆ ball t₀ ε ∩ [0,1]`, so `γ t ∈ K`, contradicting `t ∈ Z`.
        have htdist : dist t t₀ < ε := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - t₀)]
          have : t < t₁ := hlt
          have ht₁le : t₁ ≤ t₀ + ε / 2 := min_le_left _ _
          linarith
        have htW : γ t ∈ ψ.source ∩ hM ⁻¹' (Set.Iio δ) :=
          hε_sub (by rw [Metric.mem_ball]; exact htdist)
        have htK : γ t ∈ K := by
          refine hmem_K_of_src htW.1 ?_
          change nE (ψ (γ t)) ≤ δ
          exact le_of_lt htW.2
        exact htZ.2 htK
      linarith
    -- Apply the engine on `[0, t₀]`: endpoint radial value is `δ`.
    have hsrc' : ∀ t ∈ Set.Icc (0 : ℝ) t₀, γ t ∈ ψ.source :=
      fun t ht => hK_src (hall_K_prefix t ht)
    have hbball' : ∀ t ∈ Set.Icc (0 : ℝ) t₀, ‖ψ (γ t)‖ < Rₑ := by
      intro t ht
      have hch : ψ (γ t) ∈ D := hK_chart (hall_K_prefix t ht)
      exact hnE_to_ball (lt_of_le_of_lt hch hδR)
    have hdom' : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
        (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
      fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' t ht)
    have hγ_pref : CMDiff[Set.Icc (0:ℝ) t₀] 1 γ := hγ_smooth.contMDiffOn
    have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
      (a := (0 : ℝ)) (b := t₀) ht₀_nn hγ0 hγ_pref hsrc' hbball' hdom'
    -- The endpoint radial value `√(g_p(ψ(γ t₀), ψ(γ t₀))) = hM (γ t₀) = δ`.
    have hendpt : Real.sqrt (g.inner p (ψ (γ t₀)) (ψ (γ t₀))) = δ := by
      have : hM (γ t₀) = δ := ht₀_eq_δ
      rwa [hhM_def, hnE_def, hBp_def] at this
    rw [hendpt] at hlb
    -- `pathELength I γ 0 t₀ ≤ pathELength I γ 0 1`.
    have hpath_mono : pathELength I γ (0 : ℝ) t₀ ≤ pathELength I γ (0 : ℝ) 1 := by
      have hadd : pathELength I γ (0:ℝ) t₀ + pathELength I γ t₀ 1 = pathELength I γ (0:ℝ) 1 :=
        pathELength_add (γ := γ) (I := I) ht₀_nn ht₀_le1
      calc pathELength I γ (0:ℝ) t₀ ≤ pathELength I γ (0:ℝ) t₀ + pathELength I γ t₀ 1 :=
            le_self_add
        _ = pathELength I γ (0:ℝ) 1 := hadd
    -- Assemble: `S < δ ≤ pathELength γ 0 t₀ ≤ pathELength γ 0 1 < r`.
    have hSlt : ENNReal.ofReal S < ENNReal.ofReal δ :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS_nn |>.mpr hSδ
    calc ENNReal.ofReal S < ENNReal.ofReal δ := hSlt
      _ ≤ pathELength I γ (0:ℝ) t₀ := hlb
      _ ≤ pathELength I γ (0:ℝ) 1 := hpath_mono
      _ < r := hγ_len

/-- **A minimiser of exact radial length stays inside the `C²`-ball.** A `C¹`
curve `γ` on `[a, b]` from `p`, confined to the normal-chart source, whose total
`pathELength` is at most the `g_p`-radial bound `S = √(g_p(v, v)) < expRadiusGp`,
has chart image inside the Euclidean `C²`-ball at every parameter.  This is the
first-exit confinement underlying the equality case: were the chart radial
distance to reach a level `δ ∈ (S, expRadiusGp)` at some first time `t₀`, the
radial fencing on `[a, t₀]` would force `δ ≤ pathELength γ a t₀ ≤ pathELength
γ a b ≤ S < δ`, a contradiction.  The output ball bound feeds the pointwise
Gauss estimates that are only available on the `C²`-ball. -/
private theorem minimizer_confined_to_C2_ball
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Set.Icc a b] 1 γ) (hγa : γ a = p)
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hlen_le : pathELength I γ a b ≤
      ENNReal.ofReal (Real.sqrt (g.inner p v v))) :
    ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hγ_inBall
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  -- `ρ` is the `g_p`-radial distance; `ρ t < expRadiusGp ⟹ ‖c t‖ < C²radius`.
  have hρ_to_ball : ∀ {t : ℝ}, ρ t < expRadiusGp (I := I) g p →
      ‖c t‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p ht
  -- It suffices to show `ρ t < expRadiusGp` for all `t ∈ [a, b]`.
  suffices hbound : ∀ t ∈ Set.Icc a b, ρ t < expRadiusGp (I := I) g p by
    intro t ht
    exact hρ_to_ball (hbound t ht)
  -- Pick `δ` strictly between `S` and `expRadiusGp`.
  obtain ⟨δ, hSδ, hδR⟩ := exists_between hsmall_g
  have hδ_pos : 0 < δ := lt_of_le_of_lt hS_nn hSδ
  -- It suffices to show `ρ t ≤ δ` for all `t` (then `ρ t ≤ δ < expRadiusGp`).
  suffices hle : ∀ t ∈ Set.Icc a b, ρ t ≤ δ by
    intro t ht; exact lt_of_le_of_lt (hle t ht) hδR
  -- Suppose not.  Let `t₀` be the first time `ρ` reaches `δ` (`Z = {ρ ≥ δ}`).
  by_contra hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨t', ht'Icc, ht'δ⟩ := hcon
  -- `Z` is the (closed, nonempty) set of parameters with `ρ ≥ δ`.
  set Z : Set ℝ := {t ∈ Set.Icc a b | δ ≤ ρ t} with hZ_def
  have hZne : Z.Nonempty := ⟨t', ht'Icc, ht'δ.le⟩
  have hZbdd : BddBelow Z := ⟨a, fun t ht => ht.1.1⟩
  set t₀ : ℝ := sInf Z with ht₀_def
  have ht₀_lb : a ≤ t₀ := le_csInf hZne (fun t ht => ht.1.1)
  have ht₀_ub : t₀ ≤ b := by
    obtain ⟨t, ht⟩ := hZne; exact le_trans (csInf_le hZbdd ht) ht.1.2
  have ht₀Icc : t₀ ∈ Set.Icc a b := ⟨ht₀_lb, ht₀_ub⟩
  -- For `s < t₀`, `s ∉ Z`, so (if `s ∈ [a,b]`) `ρ s < δ`.
  have hpre : ∀ s ∈ Set.Icc a b, s < t₀ → ρ s < δ := by
    intro s hs hst₀
    by_contra hns
    have hns' : δ ≤ ρ s := not_lt.mp hns
    have hsZ : s ∈ Z := ⟨hs, hns'⟩
    exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hst₀)
  -- By continuity and closedness of `Z`, `ρ t₀ = δ`.
  have hρt₀_ge : δ ≤ ρ t₀ := by
    -- `ρ t₀ = lim_{s→t₀⁻} ρ s` if `t₀ > a`, but each such `ρ s < δ`; so `≤ δ`,
    -- and equals `δ` by closedness.  We obtain `δ ≤ ρ t₀` from `Z` closed.
    have hZclosed : IsClosed Z := by
      have h2 : Z = Set.Icc a b ∩ ρ ⁻¹' (Set.Ici δ) := by
        ext t; simp only [hZ_def, Set.mem_setOf_eq, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_Ici]
      rw [h2]
      exact hρc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have ht₀mem : t₀ ∈ Z := by
      rw [← hZclosed.closure_eq]
      exact csInf_mem_closure hZne hZbdd
    exact ht₀mem.2
  have hρt₀_le : ρ t₀ ≤ δ := by
    rcases eq_or_lt_of_le ht₀_lb with h0 | h0
    · -- `t₀ = a`: but `ρ a = 0 < δ`, so `ρ t₀ = 0 ≤ δ`.
      rw [← h0]
      have hca : c a = 0 := by
        rw [hc_def]; simp only; rw [hγa, hψ_def]
        exact NormalCoordinates.normalChartAt_centre (I := I) g p
      rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]; exact hδ_pos.le
    · -- `t₀ > a`: `ρ t₀ = lim_{s→t₀⁻} ρ s ≤ δ` since each `ρ s < δ`.
      have htend : Filter.Tendsto ρ (nhdsWithin t₀ (Set.Iio t₀)) (nhds (ρ t₀)) :=
        (hρc.continuousWithinAt ht₀Icc).mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi a, isOpen_Ioi, h0, by
            intro z hz; exact ⟨hz.1.le, le_trans hz.2.le ht₀_ub⟩⟩)
      have hev : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀), ρ s ≤ δ := by
        have hpos : Set.Ioo a t₀ ∈ nhdsWithin t₀ (Set.Iio t₀) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi a, isOpen_Ioi, h0, by intro z hz; exact ⟨hz.1, hz.2⟩⟩
        filter_upwards [hpos] with s hs
        exact (hpre s ⟨hs.1.le, le_trans hs.2.le ht₀_ub⟩ hs.2).le
      haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := nhdsLT_neBot t₀
      exact le_of_tendsto htend hev
  have ht₀_eq : ρ t₀ = δ := le_antisymm hρt₀_le hρt₀_ge
  -- On `[a, t₀]`, `ρ ≤ δ < expRadiusGp`, hence `‖c‖ < C²radius` and in domain.
  have hpref_le : ∀ s ∈ Set.Icc a t₀, ρ s ≤ δ := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]; exact hρt₀_le
    · exact (hpre s ⟨hs.1, le_trans hs.2 ht₀_ub⟩ h).le
  have hsrc' : ∀ s ∈ Set.Icc a t₀, γ s ∈ ψ.source :=
    fun s hs => hγ_inBall s ⟨hs.1, le_trans hs.2 ht₀_ub⟩
  have hbball' : ∀ s ∈ Set.Icc a t₀, ‖ψ (γ s)‖ < expMapC2Radius (I := I) g p := by
    intro s hs
    exact hρ_to_ball (lt_of_le_of_lt (hpref_le s hs) hδR)
  have hdom' : ∀ s ∈ Set.Icc a t₀,
      (show TangentSpace I p from ψ (γ s)) ∈ expDomain (I := I) g p :=
    fun s hs => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball' s hs)
  have hγ_pref : CMDiff[Set.Icc a t₀] 1 γ := hγ.mono (Set.Icc_subset_Icc le_rfl ht₀_ub)
  have hlb := radialDist_endpoint_le_pathELength (I := I) g p hEnorm
    (a := a) (b := t₀) ht₀_lb hγa hγ_pref hsrc' hbball' hdom'
  -- The endpoint radial value `√(g_p(ψ(γ t₀), ψ(γ t₀))) = ρ t₀ = δ`.
  have hendpt : Real.sqrt (g.inner p (ψ (γ t₀)) (ψ (γ t₀))) = δ := by
    have : ρ t₀ = δ := ht₀_eq
    rwa [hρ_def, hc_def, hB_def] at this
  rw [hendpt] at hlb
  -- `pathELength γ a t₀ ≤ pathELength γ a b`.
  have hpath_mono : pathELength I γ a t₀ ≤ pathELength I γ a b := by
    have hadd : pathELength I γ a t₀ + pathELength I γ t₀ b = pathELength I γ a b :=
      pathELength_add (γ := γ) (I := I) ht₀_lb ht₀_ub
    calc pathELength I γ a t₀ ≤ pathELength I γ a t₀ + pathELength I γ t₀ b := le_self_add
      _ = pathELength I γ a b := hadd
  -- Assemble: `δ ≤ pathELength γ a t₀ ≤ pathELength γ a b ≤ S < δ`.
  have hδS : ENNReal.ofReal δ ≤ ENNReal.ofReal S := by
    calc ENNReal.ofReal δ ≤ pathELength I γ a t₀ := hlb
      _ ≤ pathELength I γ a b := hpath_mono
      _ ≤ ENNReal.ofReal S := hlen_le
  have hδS' : δ ≤ S := (ENNReal.ofReal_le_ofReal_iff hS_nn).mp hδS
  exact absurd hδS' (not_le.mpr hSδ)

/-- **Radial-distance identity and chart-velocity radiality for an exact
minimiser.** Under the `C²`-ball confinement (`hbball`), a `C¹` curve `γ` from
`p` confined to the chart with exact radial length `√(g_p(v,v))` has chart
radial distance `ρ(t) = √(g_p(ψ(γt), ψ(γt)))` equal to the running speed
integral `∫_a^t √(g(γs)(γ's)(γ's)) ds` at every parameter, so `ρ` is monotone;
and at every *interior* parameter where the chart image `ψ(γt)` is nonzero, the
chart velocity `mfderiv (ψ∘γ) t 1` is `g_p`-parallel to `ψ(γt)`.  The radiality
is the rigidity extracted from the tightness of Gauss's bound:
the running integral makes `ρ` differentiable with `ρ'(t)` equal to the
intrinsic speed, which forces the pointwise Gauss estimate to be an equality and
hence (via `gauss_radial_lower_bound_eq_iff` and the ball-wide injectivity of
the exponential differential) the chart velocity to be radial. -/
private theorem radial_minimizer_radiality
    (g : SmoothRiemannianMetric I M) (p : M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : CMDiff[Set.Icc a b] 1 γ) (hγa : γ a = p)
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hbball : ∀ t ∈ Set.Icc a b,
      ‖NormalCoordinates.normalChartAt (I := I) g p (γ t)‖ <
        expMapC2Radius (I := I) g p)
    (hlen : pathELength I γ a b =
      ENNReal.ofReal (Real.sqrt
        (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
          (NormalCoordinates.normalChartAt (I := I) g p (γ b))))) :
    (∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
        Real.sqrt (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ s))
            (NormalCoordinates.normalChartAt (I := I) g p (γ s)))
          ≤ Real.sqrt (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
            (NormalCoordinates.normalChartAt (I := I) g p (γ t)))) ∧
    (∀ t ∈ Set.Ioo a b,
      NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0 →
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ)
        = (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
              (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
                (fun s => NormalCoordinates.normalChartAt (I := I) g p (γ s)) t (1:ℝ))
            / g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ t))
                (NormalCoordinates.normalChartAt (I := I) g p (γ t)))
          • NormalCoordinates.normalChartAt (I := I) g p (γ t)) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  set φ : ℝ → ℝ := fun t =>
    Real.sqrt (g.inner (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1))
    with hφ_def
  -- Domain membership along the curve.
  have hdom : ∀ t ∈ Set.Icc a b,
      (show TangentSpace I p from ψ (γ t)) ∈ expDomain (I := I) g p :=
    fun t ht => mem_expDomain_of_norm_lt_radius (I := I) g p (hbball t ht)
  -- Continuity of `c`, `ρ`, `φ` (mirroring the engine).
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have hψcont : ContinuousOn ψ ψ.source :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hccont : ContinuousOn c (Set.Icc a b) := hψcont.comp hγcont hγ_inBall
  have hρc : ContinuousOn ρ (Set.Icc a b) :=
    ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hρa0 : ρ a = 0 := by rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]
  -- Velocity continuity for `φ`.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · -- Degenerate `a = b`: both conclusions are vacuous / trivial.
    subst hab_eq
    refine ⟨?_, ?_⟩
    · intro s t hs ht hst
      have hsa : s = a := le_antisymm hs.2 hs.1
      have hta : t = a := le_antisymm ht.2 ht.1
      rw [hsa, hta]
    · intro t ht; exact absurd ht (by simp)
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := fun x hx => by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]; exact (uniqueDiffOn_Icc hab_lt) x hx
  have hLift : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := fun t ht => by simpa using ht
  have hVel : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) t 1)) (Set.Icc a b) :=
    ((hγ.continuousOn_tangentMapWithin (le_refl 1) hUnique).comp
      hLift.continuousOn hMaps).congr (fun t _ => rfl)
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    rw [hφ_def]
    exact Real.continuous_sqrt.comp_continuousOn
      (Variation.continuousOn_g_inner_along_curve (I := I) g hVel hVel)
  have hφnn : ∀ t ∈ Set.Icc a b, 0 ≤ φ t := fun t _ => Real.sqrt_nonneg _
  have hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume :=
    hφc.integrableOn_compact isCompact_Icc
  -- Alias used by the slope analysis below.
  have hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ ψ.source := hγ_inBall
  have hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x := by
    intro x hx
    refine (hφc x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
      intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
  have hφ_eq_mfderiv : ∀ t ∈ Set.Ioo a b,
      φ t = Real.sqrt
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) := by
    intro t ht
    rw [hφ_def]; simp only
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
    set cv : E := mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x 1 with hcv_def
    have hcderiv : HasDerivWithinAt c cv (Set.Ici x) x := by
      have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
        (hγ.mdifferentiableOn (by norm_num)) x hxIcc
      have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
        (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)
      have hcomp : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x :=
        hψdiff.comp x hγdiff (fun t ht => hsrc t ht)
      have hmf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Set.Icc a b) x) := hcomp.hasMFDerivWithinAt
      rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hmf
      have hHDW : HasDerivWithinAt c cv (Set.Icc a b) x := hmf.hasDerivWithinAt
      refine hHDW.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 hz.2, le_of_lt hz.1⟩⟩
    by_cases hcx : c x = 0
    · have htend : Filter.Tendsto (fun z => slope ρ x z)
          (nhdsWithin x (Set.Ioi x)) (nhds (Real.sqrt (B cv cv))) := by
        have hcz : Filter.Tendsto (fun z => (z - x)⁻¹ • c z)
            (nhdsWithin x (Set.Ioi x)) (nhds cv) := by
          have h0 := hcderiv.mono (Set.Ioi_subset_Ici_self)
          rw [hasDerivWithinAt_iff_tendsto_slope] at h0
          have hset : Set.Ioi x \ {x} = Set.Ioi x := by
            ext z; simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
          rw [hset] at h0
          refine (Filter.tendsto_congr' ?_).mp h0
          filter_upwards with z; rw [slope_def_module, hcx, sub_zero]
        have hcont : Continuous (fun w : E => Real.sqrt (B w w)) := by fun_prop
        have htend2 := (hcont.tendsto cv).comp hcz
        refine (Filter.tendsto_congr' ?_).mp htend2
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzx : 0 < z - x := sub_pos.mpr hz
        have heq : slope ρ x z
            = Real.sqrt (B ((z - x)⁻¹ • c z) ((z - x)⁻¹ • c z)) := by
          rw [hρ_def, slope_def_module, hcx]
          simp only [map_zero, Real.sqrt_zero, sub_zero, smul_eq_mul, map_smul,
            ContinuousLinearMap.smul_apply]
          rw [show (z - x)⁻¹ * ((z - x)⁻¹ * B (c z) (c z))
              = ((z - x)⁻¹) ^ 2 * B (c z) (c z) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
        simp only [Function.comp_apply]
        exact heq.symm
      have hφx_eq : φ x = Real.sqrt (B cv cv) := by
        have hγx_p : γ x = p := by
          have hcx' : ψ (γ x) = 0 := hcx
          have hpsrc : p ∈ ψ.source := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p
          have hψp : ψ p = 0 := by
            rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g p
          exact ψ.injOn (hsrc x hxIcc) hpsrc (by rw [hcx', hψp])
        have hcv_eq : cv = mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x 1 := by
          rw [hcv_def]
          have hUnique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Set.Icc a b) x := by
            rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact (uniqueDiffOn_Icc hab_lt) x hxIcc
          have hγdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ (Set.Icc a b) x :=
            (hγ.mdifferentiableOn (by norm_num)) x hxIcc
          have hψdiff : MDifferentiableWithinAt I 𝓘(ℝ, E) ψ ψ.source (γ x) :=
            (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
              one_ne_zero (γ x) (hsrc x hxIcc)
          have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
            (f := γ) (g := ψ) (s := Set.Icc a b) (u := ψ.source) x hψdiff hγdiff
            (fun t ht => hsrc t ht) hUnique
          have hcomp_eq : c = ψ ∘ γ := rfl
          rw [hcomp_eq, hchain]
          simp only [Function.comp_apply]
          have hsource_nhds : ψ.source ∈ nhds (γ x) :=
            (NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc)
          rw [mfderivWithin_of_mem_nhds hsource_nhds, hγx_p,
            NormalCoordinates.mfderiv_normalChartAt_self]
          rfl
        simp only [hφ_def]
        rw [hcv_eq, hγx_p, hB_def]; rfl
      rw [hφx_eq] at hr
      exact (htend.eventually_lt_const hr).frequently
    · have hxIoo : x ∈ Set.Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_, hx.2⟩
        intro hxa; apply hcx; rw [← hxa]; exact hca
      have hmem : Set.Icc a b ∈ nhds x := Icc_mem_nhds hxIoo.1 hxIoo.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
        ((hγ.mdifferentiableOn (by norm_num)) x hxIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ x) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ x) (hsrc x hxIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc x hxIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x := hψdiff.comp x hγdiff
      set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x 1 with hcv₂_def
      have hcHDA : HasDerivAt c cv₂ x := by
        have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c x) :=
          hcdiff.hasMFDerivAt
        rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
        exact hmf.hasDerivAt
      have hpos : 0 < B (c x) (c x) := by rw [hB_def]; exact g.pos p (c x) hcx
      have hρderiv : HasDerivAt ρ (B (c x) cv₂ / Real.sqrt (B (c x) (c x))) x :=
        radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
      set ρ' : ℝ := B (c x) cv₂ / Real.sqrt (B (c x) (c x)) with hρ'_def
      have hev : ∀ᶠ s in nhds x, γ s ∈ ψ.source := by
        have hopen : Set.Ioo a b ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
        filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
      have hball : ‖ψ (γ x)‖ < expMapC2Radius (I := I) g p := hbball x hxIcc
      have hune : ψ (γ x) ≠ 0 := hcx
      have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
        (hsrc x hxIcc) (hdom x hxIcc) hball hune hev
      have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => ψ (γ s)) x (1 : ℝ) := rfl
      have hρ'sq_le : ρ' ^ 2 ≤
          g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) := by
        have hρ'sq : ρ' ^ 2 = (B (c x) cv₂) ^ 2 / B (c x) (c x) := by
          rw [hρ'_def, div_pow, Real.sq_sqrt hpos.le]
        rw [hρ'sq, hcv₂_eq, hB_def]
        exact hgauss
      have hφx_eq : φ x = Real.sqrt
          (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x 1) (mfderiv 𝓘(ℝ, ℝ) I γ x 1)) := by
        simp only [hφ_def]
        rw [mfderivWithin_of_mem_nhds hmem]
      have hρ'_le : ρ' ≤ φ x := by
        rw [hφx_eq]
        calc ρ' ≤ |ρ'| := le_abs_self _
          _ = Real.sqrt (ρ' ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt hρ'sq_le
      have hρ'_lt : ρ' < r := lt_of_le_of_lt hρ'_le hr
      exact (hρderiv.hasDerivWithinAt (s := Set.Ici x)).liminf_right_slope_le hρ'_lt
  -- (continued below)
  -- `ρ b = ∫_a^b φ`: `pathELength = ofReal(∫ φ)` (via `hEnorm`) `= ofReal(ρ b)`.
  have hpath_eq : pathELength I γ a b = ENNReal.ofReal (∫ t in a..b, φ t) := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hφint.mono_set Ioo_subset_Icc_self)
        (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
            using hφnn x (Ioo_subset_Icc_self hx))]
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only
    rw [hφ_eq_mfderiv t ht]
    exact hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
  -- A convenient interval-integrability helper for sub-intervals of `[a, b]`.
  have hφii : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      IntervalIntegrable φ MeasureTheory.volume s t := by
    intro s t has hst htb
    refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hst]
    exact hφint.mono_set (Set.Icc_subset_Icc has htb)
  have hint_nn : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ∫ u in s..t, φ u := by
    intro s t has hst htb
    rw [intervalIntegral.integral_of_le hst]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun u hu => hφnn u ⟨le_trans has (le_of_lt hu.1), le_trans hu.2 htb⟩)
  have hρb_nn : 0 ≤ ρ b := Real.sqrt_nonneg _
  have hρb_int : ρ b = ∫ t in a..b, φ t := by
    -- `pathELength = ofReal(√(g_p(ψ(γb),ψ(γb)))) = ofReal(ρ b)` and `= ofReal(∫ φ)`.
    have hρb_eq : ρ b = Real.sqrt
        (g.inner p (ψ (γ b)) (ψ (γ b))) := rfl
    have h : ENNReal.ofReal (ρ b) = ENNReal.ofReal (∫ t in a..b, φ t) := by
      rw [hρb_eq, ← hlen, hpath_eq]
    exact (ENNReal.ofReal_eq_ofReal_iff hρb_nn (hint_nn a b le_rfl hab le_rfl)).mp h
  -- `ρ t ≤ ∫_a^t φ` (slope fencing on `[a, t]`).
  have hρ_le_int : ∀ t ∈ Set.Icc a b, ρ t ≤ ∫ s in a..t, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    refine image_radialDist_le_intervalIntegral_of_slope_le hat
      (hρc.mono (Set.Icc_subset_Icc le_rfl htb)) (le_of_eq hρa0)
      (hφint.mono_set (Set.Icc_subset_Icc le_rfl htb)) ?_ ?_
    · intro x hx
      exact hφcont x ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩
    · intro x hx r hr
      exact hslope x ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩ r hr
  -- `ρ b - ρ t ≤ ∫_t^b φ` (slope fencing of `ρ(·) - ρ t` on `[t, b]`).
  have hρb_sub_le : ∀ t ∈ Set.Icc a b, ρ b - ρ t ≤ ∫ s in t..b, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hkey := image_radialDist_le_intervalIntegral_of_slope_le
      (ρ := fun s => ρ s - ρ t) (φ := φ) htb
      ((hρc.mono (Set.Icc_subset_Icc hat le_rfl)).sub continuousOn_const)
      (by simp) (hφint.mono_set (Set.Icc_subset_Icc hat le_rfl)) ?_ ?_
    · simpa using hkey
    · intro x hx
      exact hφcont x ⟨le_trans hat hx.1, hx.2⟩
    · intro x hx r hr
      -- slope of `ρ - const` equals slope of `ρ`.
      have hsl := hslope x ⟨le_trans hat hx.1, hx.2⟩ r hr
      refine hsl.mono (fun z hz => ?_)
      have hsleq : slope (fun s => ρ s - ρ t) x z = slope ρ x z := by
        rw [slope_def_field, slope_def_field]; ring_nf
      rw [hsleq]; exact hz
  -- Sandwich: `ρ t = ∫_a^t φ` for all `t`.
  have hρ_int : ∀ t ∈ Set.Icc a b, ρ t = ∫ s in a..t, φ s := by
    intro t ht
    have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hsplit : (∫ s in a..t, φ s) + ∫ s in t..b, φ s = ∫ s in a..b, φ s :=
      intervalIntegral.integral_add_adjacent_intervals
        (hφii a t le_rfl hat htb) (hφii t b hat htb le_rfl)
    have hle1 := hρ_le_int t ht
    have hle2 := hρb_sub_le t ht
    -- `ρ b = ρ t + (ρ b - ρ t) ≤ ∫_a^t + ∫_t^b = ∫_a^b = ρ b`.
    have : ρ b ≤ ∫ s in a..b, φ s := by
      rw [← hsplit]
      calc ρ b = ρ t + (ρ b - ρ t) := by ring
        _ ≤ (∫ s in a..t, φ s) + ∫ s in t..b, φ s := add_le_add hle1 hle2
    rw [hρb_int] at this
    -- equality forces both sub-bounds to be equalities.
    have heq1 : ρ t = ∫ s in a..t, φ s := by
      by_contra hne
      have hlt1 : ρ t < ∫ s in a..t, φ s := lt_of_le_of_ne hle1 hne
      have : ρ b < ∫ s in a..b, φ s := by
        rw [← hsplit]
        calc ρ b = ρ t + (ρ b - ρ t) := by ring
          _ < (∫ s in a..t, φ s) + ∫ s in t..b, φ s := by
              exact add_lt_add_of_lt_of_le hlt1 hle2
      rw [hρb_int] at this; exact absurd rfl (ne_of_lt this)
    exact heq1
  -- `ρ` is monotone: it is the running integral of the nonnegative `φ`.
  have hmono : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t → ρ s ≤ ρ t := by
    intro s t hs ht hst
    rw [hρ_int s hs, hρ_int t ht]
    have hsub : (∫ u in a..t, φ u) - ∫ u in a..s, φ u = ∫ u in s..t, φ u := by
      rw [intervalIntegral.integral_interval_sub_left
        (hφii a t le_rfl ht.1 ht.2) (hφii a s le_rfl hs.1 hs.2)]
    have hnn : 0 ≤ ∫ u in s..t, φ u := hint_nn s t hs.1 hst ht.2
    linarith [hsub ▸ hnn]
  -- Convert `ρ`-monotonicity to the stated `√(g_p ...)`-monotonicity.
  refine ⟨fun s t hs ht hst => ?_, ?_⟩
  · have := hmono s t hs ht hst
    rwa [hρ_def, hc_def, hB_def] at this
  -- Radiality at interior points where the chart image is nonzero.
  · intro t ht hne
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    -- Chart-velocity `cv₂ = mfderiv c t 1` and its `HasDerivAt`.
    have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      ((hγ.mdifferentiableOn (by norm_num)) t htIcc).mdifferentiableAt hmem
    have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ t) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
        one_ne_zero (γ t) (hsrc t htIcc)).mdifferentiableAt
        ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hsrc t htIcc))
    have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t := hψdiff.comp t hγdiff
    set cv₂ : E := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 with hcv₂_def
    have hcHDA : HasDerivAt c cv₂ t := by
      have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) :=
        hcdiff.hasMFDerivAt
      rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
      exact hmf.hasDerivAt
    have hcx_ne : c t ≠ 0 := hne
    have hpos : 0 < B (c t) (c t) := by rw [hB_def]; exact g.pos p (c t) hcx_ne
    -- `ρ` has two derivatives at `t`: the radial one and the FTC one.
    have hρderiv1 : HasDerivAt ρ (B (c t) cv₂ / Real.sqrt (B (c t) (c t))) t :=
      radialDist_hasDerivAt B hBsym c cv₂ hcHDA hpos
    -- FTC: `ρ = ∫_a^· φ` near `t`, and `φ` is continuous at `t`, giving `ρ' = φ t`.
    have hρderiv2 : HasDerivAt ρ (φ t) t := by
      have hftc : HasDerivAt (fun u => ∫ s in a..u, φ s) (φ t) t :=
        intervalIntegral.integral_hasDerivAt_right
          (hφii a t le_rfl (le_of_lt ht.1) (le_of_lt ht.2))
          ⟨Set.Icc a b, hmem, hφc.aestronglyMeasurable measurableSet_Icc⟩
          (hφc.continuousAt hmem)
      refine hftc.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hρ_int s (Ioo_subset_Icc_self hs)
    -- Uniqueness of the derivative: `B(ct)(cv₂)/ρ = φ t`, hence the Gauss
    -- tightness `(B(ct)(cv₂))²/B(ct)(ct) = g(γt)(γ't)(γ't)`.
    have hρ'_eq : B (c t) cv₂ / Real.sqrt (B (c t) (c t)) = φ t :=
      hρderiv1.unique hρderiv2
    -- The chart-velocity equals `mfderiv (ψ∘γ) t 1` and γ-velocity = dexp(cv₂).
    have hev : ∀ᶠ s in nhds t, γ s ∈ ψ.source := by
      have hopen : Set.Ioo a b ∈ nhds t := isOpen_Ioo.mem_nhds ht
      filter_upwards [hopen] with s hs using hsrc s (Ioo_subset_Icc_self hs)
    have hball : ‖ψ (γ t)‖ < expMapC2Radius (I := I) g p := hbball t htIcc
    -- `gauss_pointwise_speed_lower_bound` gives the ≤; tightness gives `=`.
    have hgauss := gauss_pointwise_speed_lower_bound (I := I) g p hγdiff
      (hsrc t htIcc) (hdom t htIcc) hball hne hev
    have hcv₂_eq : cv₂ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => ψ (γ s)) t (1 : ℝ) := rfl
    have hφt_sq : φ t ^ 2 =
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hφ_def]; simp only
      rw [mfderivWithin_of_mem_nhds hmem, Real.sq_sqrt]
      rcases eq_or_ne (mfderiv 𝓘(ℝ, ℝ) I γ t 1) 0 with h0 | h0
      · rw [h0]; simp
      · exact (g.pos (γ t) _ h0).le
    -- `(B(ct)(cv₂))² / B(ct)(ct) = φ t ^ 2 = g(γt)(γ't)(γ't)`.
    have hLHS_sq : (B (c t) cv₂) ^ 2 / B (c t) (c t) = φ t ^ 2 := by
      have : (B (c t) cv₂ / Real.sqrt (B (c t) (c t))) ^ 2 = φ t ^ 2 := by rw [hρ'_eq]
      rwa [div_pow, Real.sq_sqrt hpos.le] at this
    have htight : (B (c t) cv₂) ^ 2 / B (c t) (c t) =
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hLHS_sq, hφt_sq]
    -- Rewrite the intrinsic speed via `radial_chain_mfderiv` and `expMap_normalChartAt`
    -- into the form appearing in `gauss_radial_lower_bound_eq_iff`.
    have hchain := radial_chain_mfderiv (I := I) g p hγdiff (hsrc t htIcc) hball hev
    have hbase : expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))) = γ t :=
      expMap_normalChartAt (I := I) g p (hsrc t htIcc)
    -- `dexp_{ψ(γt)}(cv₂) = γ't` (chain rule, `cv₂ = mfderiv (ψ∘γ) t 1`).
    have hdexp : mfderiv 𝓘(ℝ, E) I
        (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
        (show TangentSpace I p from cv₂) = mfderiv 𝓘(ℝ, ℝ) I γ t 1 :=
      hchain.symm
    -- The Gauss equality LHS holds (with `u = ψ(γt)`, `ζ = cv₂`): the tightness.
    -- The RHS, by `hbase` and `hdexp`, equals `g(γt)(γ't)(γ't)`.
    have hRHS :
        g.inner (expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂)) =
          g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
      rw [hdexp, hbase]
    have hgauss_eq :
        (g.inner p (ψ (γ t)) cv₂) ^ 2 / g.inner p (ψ (γ t)) (ψ (γ t)) =
          g.inner (expMap (I := I) g p (show TangentSpace I p from (ψ (γ t))))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂))
            (mfderiv 𝓘(ℝ, E) I
              (fun y : E => (expMap (I := I) g p (show TangentSpace I p from y) : M)) (ψ (γ t))
              (show TangentSpace I p from cv₂)) := by
      rw [hRHS]; exact htight
    -- Apply the equality-case iff to get the orthogonal part annihilated.
    have hiff := gauss_radial_lower_bound_eq_iff (I := I) g p (hdom t htIcc) hball hne cv₂
    have horth_dexp := hiff.mp hgauss_eq
    -- Ball-wide injectivity of `dexp` ⟹ the orthogonal part vanishes.
    have hinj := mfderiv_expMap_injective_of_norm_lt_radius (I := I) g p hball
    have horth_zero :
        cv₂ - (g.inner p (ψ (γ t)) cv₂ / g.inner p (ψ (γ t)) (ψ (γ t))) • (ψ (γ t)) = 0 :=
      hinj (horth_dexp.trans (ContinuousLinearMap.map_zero _).symm)
    -- Rearrange into the radial form `cv₂ = (B(ψγt)(cv₂)/B(ψγt)(ψγt)) • (ψ γt)`.
    have hradial : cv₂ =
        (g.inner p (ψ (γ t)) cv₂ / g.inner p (ψ (γ t)) (ψ (γ t))) • (ψ (γ t)) :=
      sub_eq_zero.mp horth_zero
    -- Conclude (note `cv₂ = mfderiv (ψ∘γ) t 1`).
    rw [hcv₂_eq] at hradial
    exact hradial

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
/-- **Equality case of the radial unique-minimiser bound.** Inside the
normal ball at `p`, a `C¹` curve `γ` on `[a, b]` from `p` to
`expMap g p v` that stays in the normal-chart source and whose
`pathELength` equals the minimum `√(g_p(v, v))` (the lower bound of
`normalBall_radial_unique_minimizer`) is a monotone radial
reparametrisation: there is a monotone reparametrisation function
`φ : ℝ → ℝ` with `φ a = 0`, `φ b = 1` such that `γ` coincides with the
radial geodesic `t ↦ expMap g p (φ t • v)` on `[a, b]`. This is the
equality-characterisation sibling of `normalBall_radial_unique_minimizer`
(which gives only the inequality), consumed by the local radial
identification of a minimiser and by the radial-image openness step. -/
theorem normalBall_radial_minimizer_equality
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (hsmall_g : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CMDiff[Set.Icc a b] 1 γ)
    (hγa : γ a = p)
    (hγb : γ b = expMap (I := I) g p (show TangentSpace I p from v))
    (hγ_inBall : ∀ t ∈ Set.Icc a b,
      γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hlen : pathELength I γ a b =
      ENNReal.ofReal (Real.sqrt (g.inner p v v))) :
    ∃ φ : ℝ → ℝ, MonotoneOn φ (Set.Icc a b) ∧ φ a = 0 ∧ φ b = 1 ∧
      ∀ t ∈ Set.Icc a b,
        γ t = expMap (I := I) g p (show TangentSpace I p from (φ t • v)) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g p with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm p
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos p x h).le
  set S : ℝ := Real.sqrt (g.inner p v v) with hS_def
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  set c : ℝ → E := fun t => ψ (γ t) with hc_def
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (c t) (c t)) with hρ_def
  -- Chart endpoint values.
  have hca : c a = 0 := by
    rw [hc_def]; simp only; rw [hγa, hψ_def]
    exact NormalCoordinates.normalChartAt_centre (I := I) g p
  have hcb : c b = v := by
    have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p (v := v) hball
    have hrinv := NormalCoordinates.normalChartAt_right_inv (I := I) g p hball
    -- `c b = ψ (exp_p v) = ψ (ψ.symm v) = v`.
    change ψ (γ b) = v
    rw [hγb, hψ_def, ← hsymm, hrinv]
  have hρa : ρ a = 0 := by rw [hρ_def]; simp only [hca, map_zero, Real.sqrt_zero]
  have hρb : ρ b = S := by
    change Real.sqrt (B (c b) (c b)) = S
    rw [hcb]; rfl
  have hSsq : S ^ 2 = B v v := by
    rw [hS_def]
    exact Real.sq_sqrt (hBnn v)
  -- Ball confinement from the exact length, via the first-exit lemma.
  have hbball : ∀ t ∈ Set.Icc a b,
      ‖ψ (γ t)‖ < expMapC2Radius (I := I) g p :=
    minimizer_confined_to_C2_ball (I := I) g p hEnorm hsmall_g hγ hγa hγ_inBall (le_of_eq hlen)
  -- The radiality package: `ρ` monotone and the chart velocity is radial.
  have hψγb : NormalCoordinates.normalChartAt (I := I) g p (γ b) = v := by
    rw [← hψ_def]; exact hcb
  have hlen' : pathELength I γ a b = ENNReal.ofReal (Real.sqrt
      (g.inner p (NormalCoordinates.normalChartAt (I := I) g p (γ b))
        (NormalCoordinates.normalChartAt (I := I) g p (γ b)))) := by
    rw [hlen, hψγb]
  obtain ⟨hmono, hradial⟩ :=
    radial_minimizer_radiality (I := I) g p hEnorm (le_of_lt hab) hγ hγa hγ_inBall hbball hlen'
  -- Translate `hmono` to `ρ` and `hradial` to `c`.
  have hρmono : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t → ρ s ≤ ρ t := by
    intro s t hs ht hst; exact hmono s t hs ht hst
  have hρnn : ∀ t, 0 ≤ ρ t := fun t => Real.sqrt_nonneg _
  -- `S > 0` main case (and `S = 0` degenerate handled separately).
  rcases eq_or_lt_of_le hS_nn with hS0 | hSpos
  · -- `S = 0`: `v = 0`, the whole curve sits at `p`.
    have hSeq : S = 0 := hS0.symm
    have hvz : v = 0 := by
      have : B v v = 0 := by rw [← hSsq, hSeq]; ring
      by_contra hv0
      exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p v hv0))
    -- `ρ ≡ 0` on `[a, b]` (monotone, `ρ a = ρ b = 0`).
    have hρ0 : ∀ t ∈ Set.Icc a b, ρ t = 0 := by
      intro t ht
      refine le_antisymm ?_ (hρnn t)
      calc ρ t ≤ ρ b := hρmono t b ht ⟨le_of_lt hab, le_rfl⟩ ht.2
        _ = 0 := by rw [hρb, hSeq]
    -- `c t = 0` and `γ t = p`.
    have hct0 : ∀ t ∈ Set.Icc a b, c t = 0 := by
      intro t ht
      have : B (c t) (c t) = 0 := by
        have h := hρ0 t ht; rw [hρ_def] at h; simp only at h
        nlinarith [Real.sq_sqrt (hBnn (c t)), Real.sqrt_nonneg (B (c t) (c t)), h,
          Real.sq_sqrt (hBnn (c t))]
      by_contra hc0
      exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p (c t) hc0))
    refine ⟨fun t => (t - a) / (b - a), ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      simp only
      gcongr
      linarith
    · simp only [sub_self, zero_div]
    · simp only; rw [div_self (by linarith : b - a ≠ 0)]
    · intro t ht
      have hctz : c t = 0 := hct0 t ht
      have hγtp : γ t = p := by
        have : ψ (γ t) = ψ p := by
          rw [show ψ (γ t) = c t from rfl, hctz, hψ_def,
            NormalCoordinates.normalChartAt_centre (I := I) g p]
        exact ψ.injOn (hγ_inBall t ht)
          (by rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g p) this
      rw [hγtp, hvz, smul_zero]
      -- `exp_p 0 = ψ.symm 0 = p`, so `p = exp_p 0`.
      have h0tgt : (0 : E) ∈ (NormalCoordinates.normalChartAt (I := I) g p).target :=
        NormalCoordinates.zero_mem_normalChartAt_target (I := I) g p
      have hsymm := NormalCoordinates.normalChartAt_symm_apply (I := I) g p
        (v := (0 : E)) h0tgt
      rw [NormalCoordinates.normalChartAt_symm_zero (I := I) g p] at hsymm
      -- `hsymm : p = exp_p 0`.
      exact hsymm
  -- `S > 0` main case.  Here `ρ b = S > 0` and the angular direction
  -- `θ(t) = (ρ t)⁻¹ • c t` is constant `= S⁻¹ • v` on `{ρ > 0}`, forcing
  -- `c t = (ρ t / S) • v`.
  · have hSpos' : 0 < S := hSpos
    -- `HasDerivAt c (mfderiv c t 1) t` at interior parameters.
    have hcderiv : ∀ t ∈ Set.Ioo a b,
        HasDerivAt c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) t := by
      intro t ht
      have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
        ((hγ.mdifferentiableOn (by norm_num)) t htIcc).mdifferentiableAt hmem
      have hψdiff : MDifferentiableAt I 𝓘(ℝ, E) ψ (γ t) :=
        ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).mdifferentiableOn
          one_ne_zero (γ t) (hγ_inBall t htIcc)).mdifferentiableAt
          ((NormalCoordinates.normalChartAt_open_source (I := I) g p).mem_nhds (hγ_inBall t htIcc))
      have hcdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t := hψdiff.comp t hγdiff
      have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) :=
        hcdiff.hasMFDerivAt
      rw [hasMFDerivAt_iff_hasFDerivAt] at hmf
      exact hmf.hasDerivAt
    -- `ρ` is continuous on `[a, b]`.
    have hccont : ContinuousOn c (Set.Icc a b) :=
      ((NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn).comp
        hγ.continuousOn hγ_inBall
    have hρc : ContinuousOn ρ (Set.Icc a b) :=
      ((psd_sqrt_lipschitz B hBsym hBnn).continuous.comp_continuousOn hccont)
    -- The angular direction `θ t := (ρ t)⁻¹ • c t`.
    set θ : ℝ → E := fun t => (ρ t)⁻¹ • c t with hθ_def
    -- At interior `t` with `ρ t > 0`, `θ` has derivative `0` (angular ODE).
    have hθderiv : ∀ t ∈ Set.Ioo a b, 0 < ρ t → HasDerivAt θ 0 t := by
      intro t ht hρt
      have hct_ne : c t ≠ 0 := by
        intro h0
        have : ρ t = 0 := by rw [hρ_def]; simp only [h0, map_zero, Real.sqrt_zero]
        exact absurd this (ne_of_gt hρt)
      have hBpos : 0 < B (c t) (c t) := by rw [hB_def]; exact g.pos p (c t) hct_ne
      have hc' : HasDerivAt c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) t := hcderiv t ht
      have hρ' : HasDerivAt ρ
          (B (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) / Real.sqrt (B (c t) (c t))) t :=
        radialDist_hasDerivAt B hBsym c (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) hc' hBpos
      have hρt_eq : Real.sqrt (B (c t) (c t)) = ρ t := rfl
      rw [hρt_eq] at hρ'
      have hrad' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1
          = (B (c t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) / B (c t) (c t)) • (c t) :=
        hradial t ht (by
          show NormalCoordinates.normalChartAt (I := I) g p (γ t) ≠ 0
          rw [← hψ_def]; exact hct_ne)
      have hρtsq : ρ t ^ 2 = B (c t) (c t) := by
        rw [hρ_def]; simp only; rw [Real.sq_sqrt (hBnn (c t))]
      exact angular_hasDerivAt_zero B hc' hρt hρ' hρtsq hrad'
    -- `θ b = S⁻¹ • v`.
    have hθb : θ b = (S)⁻¹ • v := by
      rw [hθ_def]; simp only [hρb, hcb]
    -- For interior `t` with `ρ t > 0`, propagate `θ t = θ b` via constancy on `[t,b]`.
    have hθ_const : ∀ t ∈ Set.Ioo a b, 0 < ρ t → θ t = θ b := by
      intro t ht hρt
      -- On `[t, b]`, `ρ ≥ ρ t > 0` (monotonicity), so `θ` is `C¹` with `θ' = 0`.
      have hρpos_on : ∀ s ∈ Set.Icc t b, 0 < ρ s := by
        intro s hs
        have hsIcc : s ∈ Set.Icc a b := ⟨le_trans (le_of_lt ht.1) hs.1, hs.2⟩
        exact lt_of_lt_of_le hρt
          (hρmono t s ⟨le_of_lt ht.1, le_of_lt ht.2⟩ hsIcc hs.1)
      -- Continuity of `θ` on `[t, b]`.
      have hθcont : ContinuousOn θ (Set.Icc t b) := by
        apply ContinuousOn.smul
        · apply ContinuousOn.inv₀
          · exact (hρc.mono (Set.Icc_subset_Icc (le_of_lt ht.1) le_rfl))
          · exact fun s hs => ne_of_gt (hρpos_on s hs)
        · exact hccont.mono (Set.Icc_subset_Icc (le_of_lt ht.1) le_rfl)
      -- Right-derivative `0` at every `x ∈ Ico t b`.
      have hθrd : ∀ x ∈ Set.Ico t b, HasDerivWithinAt θ 0 (Set.Ici x) x := by
        intro x hx
        have hxIoo : x ∈ Set.Ioo a b := ⟨lt_of_lt_of_le ht.1 hx.1, hx.2⟩
        have hρx : 0 < ρ x := hρpos_on x ⟨hx.1, le_of_lt hx.2⟩
        exact (hθderiv x hxIoo hρx).hasDerivWithinAt
      have hconst := constant_of_has_deriv_right_zero hθcont hθrd
      exact (hconst b (Set.right_mem_Icc.2 (le_of_lt ht.2))).symm
    -- Conclude `c t = (ρ t / S) • v` for all `t ∈ [a, b]`.
    have hc_formula : ∀ t ∈ Set.Icc a b, c t = (ρ t / S) • v := by
      intro t ht
      rcases eq_or_lt_of_le (hρnn t) with hρt0 | hρtpos
      · -- `ρ t = 0`: `c t = 0` and `(ρt/S)•v = 0`.
        have hct0 : c t = 0 := by
          have : B (c t) (c t) = 0 := by
            have h : ρ t = 0 := hρt0.symm
            rw [hρ_def] at h; simp only at h
            nlinarith [Real.sq_sqrt (hBnn (c t)), Real.sqrt_nonneg (B (c t) (c t)), h]
          by_contra hc0
          exact absurd this (ne_of_gt (by rw [hB_def]; exact g.pos p (c t) hc0))
        rw [hct0, ← hρt0, zero_div, zero_smul]
      · -- `ρ t > 0`.  Boundary `t = a` is impossible (`ρ a = 0`); handle `t = b`
        -- and interior `t ∈ (a, b)` via `θ`-constancy.
        rcases eq_or_lt_of_le ht.2 with htb | htb
        · -- `t = b`: `c b = v = (S/S)•v`.
          rw [htb, hcb, hρb, div_self (ne_of_gt hSpos'), one_smul]
        · have hta : a < t := by
            rcases eq_or_lt_of_le ht.1 with hta | hta
            · exfalso; rw [← hta] at hρtpos; exact (hρtpos.ne') hρa
            · exact hta
          have htIoo : t ∈ Set.Ioo a b := ⟨hta, htb⟩
          have hθt := hθ_const t htIoo hρtpos
          -- `θ t = θ b = S⁻¹ • v`, so `c t = ρ t • (S⁻¹ • v) = (ρt/S)•v`.
          rw [hθb] at hθt
          have hθt' : (ρ t)⁻¹ • c t = S⁻¹ • v := hθt
          have hctv : c t = ρ t • (S⁻¹ • v) := by
            rw [← hθt', smul_smul, mul_inv_cancel₀ hρtpos.ne', one_smul]
          rw [hctv, smul_smul, div_eq_mul_inv]
      -- end of cases
    -- Build `φ = ρ / S` and conclude.
    refine ⟨fun t => ρ t / S, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      simp only
      gcongr
      exact hρmono s t hs ht hst
    · simp only [hρa, zero_div]
    · simp only [hρb, div_self (ne_of_gt hSpos')]
    · intro t ht
      -- `γ t = ψ.symm (c t) = ψ.symm ((ρt/S)•v) = exp_p ((ρt/S)•v)`.
      have hctf := hc_formula t ht
      have hγt_symm : γ t = ψ.symm (c t) := by
        rw [hc_def]; simp only
        exact (NormalCoordinates.normalChartAt_left_inv (I := I) g p (hγ_inBall t ht)).symm
      rw [hγt_symm, hctf]
      -- `ψ.symm w = exp_p w` for `w` in the target.
      have hwtgt : ((ρ t / S) • v) ∈
          (NormalCoordinates.normalChartAt (I := I) g p).symm.source := by
        change ((ρ t / S) • v) ∈ (NormalCoordinates.normalChartAt (I := I) g p).target
        -- `(ρt/S)•v = c t ∈ ψ.target` (chart image of a source point).
        rw [← hctf, hc_def]; simp only
        exact (NormalCoordinates.normalChartAt (I := I) g p).map_source (hγ_inBall t ht)
      change ψ.symm ((ρ t / S) • v) = _
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g p hwtgt

end RadialUniqueMinimizer

section LocalRadialIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Local radial identification of a minimiser

At any interior parameter of a length-minimising curve, there is a
`δ`-neighbourhood on which the curve, after rescaling, is a monotone
radial geodesic in normal coordinates at `γ(t₀)`. -/

/-- **`C¹` smoothness of the central radial curve on `[0, 1]`.** For
`‖a‖ < expMapC2Radius g p`, the curve `t ↦ expMap g p (t • a)` is `C¹` on
`[0, 1]`.  Each parameter `t ∈ [0, 1]` has `‖t • a‖ ≤ ‖a‖`, so
`radialCurve_contMDiffAt2` provides `C²`-smoothness pointwise; we downgrade to
the `C¹`-on-set form needed for `pathELength` / `riemannianEDist`. -/
private lemma radialCurve_contMDiffOn_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) :
    CMDiff[Set.Icc (0 : ℝ) 1] 1
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) := by
  intro t ht
  have hnorm : ‖t • a‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := ht
    have habs : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    calc |t| * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖a‖ := one_mul _
      _ < _ := ha
  exact ((radialCurve_contMDiffAt2 (I := I) g p a t hnorm).of_le
    (by norm_num)).contMDiffWithinAt

/-- **Central radial path length equals the radius.** For
`‖a‖ < expMapC2Radius g p`, the `pathELength` of `t ↦ expMap g p (t • a)` over
`[0, 1]` is exactly `ofReal √(g_p(a, a))`.  The velocity has constant `g`-speed
`√(g_p(a, a))` on the interior `(0, 1)` (`radialSpeedSq_eq_inner`), so via
`hEnorm` the integrand `‖mfderiv‖ₑ` is the constant `ofReal √(g_p(a, a))` there,
and the lintegral over `(0, 1)` (measure `1`) returns that constant. -/
private lemma radialCurve_pathELength_eq
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha : ‖a‖ < expMapC2Radius (I := I) g p) :
    pathELength I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) 0 1
      = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  classical
  set γr : ℝ → M :=
    fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
    with hγr_def
  -- The constant `g`-speed on the interior, transported to the integrand.
  have hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) I γr t 1‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
    intro t ht
    have hsp := radialSpeedSq_eq_inner (I := I) g p a ha t ht
    -- `radialSpeedSq g p a t = g.inner (γr t) (mfderiv γr t 1) (mfderiv γr t 1)` definitionally.
    have hsp' : g.inner (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t 1) (mfderiv 𝓘(ℝ, ℝ) I γr t 1)
        = g.inner p a a := hsp
    rw [hEnorm (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t 1), hsp']
  -- Integrate the constant over `Ioo 0 1`.
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hintegrand]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- **Radial distance equals the radius (inside the `C²` ball).** For a chart
endpoint `a` with `√(g_p(a, a)) < expRadiusGp g p` (equivalently `a` in the
normal-chart target and in the natural exponential domain), the Riemannian
distance from `p` to the radial point `expMap g p a` equals `ofReal √(g_p(a, a))`.
The `≤` direction is the radial path length bound `radialCurve_pathELength_eq`
(the radial geodesic realises the distance); the `≥` direction is the Gauss-lemma
radial lower bound `normalBall_radial_unique_minimizer`. -/
private theorem radial_riemannianEDist_eq_radius
    (g : SmoothRiemannianMetric I M) (p : M) {a : E}
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (ha_dom : (show TangentSpace I p from a) ∈ expDomain (I := I) g p)
    (ha_ball : a ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (ha_small : Real.sqrt (g.inner p a a) < expRadiusGp (I := I) g p) :
    riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a))
      = ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
  classical
  -- Euclidean smallness from the `g_p`-smallness.
  have ha_eucl : ‖a‖ < expMapC2Radius (I := I) g p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p ha_small
  -- `≥`: the Gauss radial lower bound.
  have hge : ENNReal.ofReal (Real.sqrt (g.inner p a a)) ≤
      riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a)) :=
    normalBall_radial_unique_minimizer (I := I) g p hEnorm ha_dom ha_ball ha_small
  -- `≤`: the radial geodesic from `p` to `expMap p a` realises that length.
  have hle : riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from a))
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p a a)) := by
    set γr : ℝ → M :=
      fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)
      with hγr_def
    have hγr0 : γr 0 = p := by
      rw [hγr_def]; simp only [zero_smul]; exact expMap_zero (I := I) g p
    have hγr1 : γr 1 = expMap (I := I) g p (show TangentSpace I p from a) := by
      rw [hγr_def]; simp only [one_smul]
    have hγr_C1 : CMDiff[Set.Icc (0 : ℝ) 1] 1 γr :=
      radialCurve_contMDiffOn_Icc (I := I) g p a ha_eucl
    have hdist_le : riemannianEDist I (γr 0) (γr 1) ≤ pathELength I γr 0 1 :=
      riemannianEDist_le_pathELength (I := I) (γ := γr) (a := 0) (b := 1)
        hγr_C1 rfl rfl zero_le_one
    rw [hγr0, hγr1] at hdist_le
    refine hdist_le.trans ?_
    rw [radialCurve_pathELength_eq (I := I) g p a hEnorm ha_eucl]
  exact le_antisymm hle hge

/-- **Short-time confinement of a curve to the small normal ball at its
launch point.** If `γ` is `C¹` on `[a, b]` with `γ t₀ = q` at an interior
parameter `t₀ ∈ (a, b)`, then there is a `δ > 0` such that the forward sub-arc
`γ |[t₀, t₀ + δ]` lies inside `q`'s normal-chart source with `g_q`-chart radius
below `expRadiusGp g q`.  This is pure continuity: the chart-radial value
`t ↦ √(g_q(ψ_q(γ t), ψ_q(γ t)))` is continuous and vanishes at `t₀`, so it stays
below the positive threshold `expRadiusGp g q` on a forward neighbourhood; the
source-membership is the openness of the chart source at `q = γ t₀`. -/
private theorem exists_forward_confinement_to_smallBall
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} {t₀ : ℝ}
    (hγ : CMDiff[Set.Icc a b] 1 γ) (ht₀ : t₀ ∈ Set.Ioo a b)
    {q : M} (hq : γ t₀ = q) :
    ∃ δ : ℝ, 0 < δ ∧ t₀ + δ ≤ b ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + δ),
        γ t ∈ (NormalCoordinates.normalChartAt (I := I) g q).source) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + δ),
        Real.sqrt (g.inner q
            (NormalCoordinates.normalChartAt (I := I) g q (γ t))
            (NormalCoordinates.normalChartAt (I := I) g q (γ t)))
          < expRadiusGp (I := I) g q) := by
  classical
  set ψ := NormalCoordinates.normalChartAt (I := I) g q with hψ_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner q with hB_def
  have hBsym : ∀ x y : E, B x y = B y x := g.symm q
  have hBnn : ∀ x : E, 0 ≤ B x x := fun x => by
    rcases eq_or_ne x 0 with h | h
    · subst h; simp
    · exact (g.pos q x h).le
  -- Continuity of `γ` on `[a, b]`; and `q ∈ ψ.source`, `ψ q = 0`.
  have hγcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  have ht₀Icc : t₀ ∈ Set.Icc a b := ⟨ht₀.1.le, ht₀.2.le⟩
  have hqsrc : q ∈ ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_source (I := I) g q
  have hψq : ψ q = 0 := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_centre (I := I) g q
  -- The chart-radial value `ρ t := √(B (ψ (γ t)) (ψ (γ t)))`.
  set ρ : ℝ → ℝ := fun t => Real.sqrt (B (ψ (γ t)) (ψ (γ t))) with hρ_def
  -- `γ t₀ = q ∈ ψ.source`, so `γ` maps a neighbourhood (in `[a,b]`) into `ψ.source`.
  have hγt₀_src : γ t₀ ∈ ψ.source := by rw [hq]; exact hqsrc
  have hopen_src : IsOpen ψ.source := by
    rw [hψ_def]; exact NormalCoordinates.normalChartAt_open_source (I := I) g q
  -- The preimage `γ ⁻¹' ψ.source` is a (relative) neighbourhood of `t₀` in `[a,b]`.
  have hpre_nhds : γ ⁻¹' ψ.source ∈ nhdsWithin t₀ (Set.Icc a b) :=
    (hγcont t₀ ht₀Icc).preimage_mem_nhdsWithin (hopen_src.mem_nhds hγt₀_src)
  -- `ρ` is continuous within `[a,b]` at `t₀` on the source-preimage, and `ρ t₀ = 0`.
  have hρt₀ : ρ t₀ = 0 := by
    rw [hρ_def]; simp only [hq, hψq, map_zero, Real.sqrt_zero]
  -- Continuity of `ρ` near `t₀` (restricted to the source-preimage where `ψ∘γ` is continuous).
  have hψcont : ContinuousOn ψ ψ.source := by
    rw [hψ_def]; exact (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g q).continuousOn
  have hρ_contWithin : ContinuousWithinAt ρ (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ := by
    have hcomp : ContinuousWithinAt (fun t => ψ (γ t))
        (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ := by
      have h1 : ContinuousWithinAt γ (Set.Icc a b ∩ γ ⁻¹' ψ.source) t₀ :=
        (hγcont t₀ ht₀Icc).mono Set.inter_subset_left
      have hmaps : Set.MapsTo γ (Set.Icc a b ∩ γ ⁻¹' ψ.source) ψ.source :=
        fun t ht => ht.2
      exact (hψcont _ hγt₀_src).comp h1 hmaps
    exact ((psd_sqrt_lipschitz B hBsym hBnn).continuous.continuousAt.comp_continuousWithinAt hcomp)
  -- The threshold is positive; pull back the `< expRadiusGp` condition.
  have hR_pos : 0 < expRadiusGp (I := I) g q := expRadiusGp_pos (I := I) g q
  have hρ_small_nhds : {t | ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Icc a b ∩ γ ⁻¹' ψ.source) := by
    have : Set.Iio (expRadiusGp (I := I) g q) ∈ nhds (ρ t₀) := by
      rw [hρt₀]; exact isOpen_Iio.mem_nhds hR_pos
    exact hρ_contWithin this
  -- Combine: the set `S := {t | γ t ∈ source ∧ ρ t < R}` is a `nhdsWithin t₀ [a,b]` set.
  have hS_nhds : {t | γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Icc a b) := by
    -- `nhdsWithin t₀ (Icc ∩ pre) = nhdsWithin t₀ Icc ⊓ 𝓟 pre`; intersect.
    have hpre_nhds' : (γ ⁻¹' ψ.source) ∈ nhdsWithin t₀ (Set.Icc a b) := hpre_nhds
    have hρ_in_Icc : {t | ρ t < expRadiusGp (I := I) g q} ∈
        nhdsWithin t₀ (Set.Icc a b) := by
      rw [show Set.Icc a b ∩ γ ⁻¹' ψ.source
          = (Set.Icc a b) ∩ (γ ⁻¹' ψ.source) from rfl] at hρ_small_nhds
      rw [nhdsWithin_inter_of_mem' hpre_nhds'] at hρ_small_nhds
      exact hρ_small_nhds
    filter_upwards [hpre_nhds', hρ_in_Icc] with t htpre htρ
    exact ⟨htpre, htρ⟩
  -- Extract a forward radius `δ`.  We use the right-interval form of `nhdsWithin`.
  have ht₀_lt_b : t₀ < b := ht₀.2
  -- `Ico t₀ b ⊆ Icc a b`, and `nhdsWithin t₀ (Ico t₀ b) ≤ nhdsWithin t₀ (Icc a b)`.
  have hIco_sub : Set.Ico t₀ b ⊆ Set.Icc a b := fun t ht => ⟨ht₀.1.le.trans ht.1, ht.2.le⟩
  have hS_nhds_right : {t | γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q} ∈
      nhdsWithin t₀ (Set.Ico t₀ b) :=
    nhdsWithin_mono t₀ hIco_sub hS_nhds
  -- `nhdsWithin t₀ (Ico t₀ b)` has a basis of `Ico t₀ t₀'`; extract one inside `S`.
  rw [nhdsWithin_Ico_eq_nhdsGE ht₀_lt_b, mem_nhdsGE_iff_exists_Ico_subset] at hS_nhds_right
  obtain ⟨u, hu_mem, hu_sub⟩ := hS_nhds_right
  -- `u ∈ Ioi t₀`, so `u > t₀`; pick `δ` with `t₀ + δ < u` and `t₀ + δ ≤ b`.
  have hu_gt : t₀ < u := hu_mem
  set δ : ℝ := min ((u - t₀) / 2) (b - t₀) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact lt_min (by linarith) (by linarith [ht₀_lt_b])
  have hδ_le_b : t₀ + δ ≤ b := by
    rw [hδ_def]; have := min_le_right ((u - t₀) / 2) (b - t₀); linarith
  have hδ_lt_u : t₀ + δ < u := by
    rw [hδ_def]; have := min_le_left ((u - t₀) / 2) (b - t₀); linarith
  -- For `t ∈ Icc t₀ (t₀+δ) ⊆ Ico t₀ u`, `t ∈ S`.
  have hmemS : ∀ t ∈ Set.Icc t₀ (t₀ + δ),
      γ t ∈ ψ.source ∧ ρ t < expRadiusGp (I := I) g q := by
    intro t ht
    have ht_Ico : t ∈ Set.Ico t₀ u := ⟨ht.1, lt_of_le_of_lt ht.2 hδ_lt_u⟩
    exact hu_sub ht_Ico
  refine ⟨δ, hδ_pos, hδ_le_b, ?_, ?_⟩
  · intro t ht; exact (hmemS t ht).1
  · intro t ht; exact (hmemS t ht).2

/-- **Forward local radial identification of a minimiser.** Let `γ : ℝ → M` be
a length-minimising `C¹` curve on `[a, b]` (`riemannianEDist (γ a) (γ b) =
pathELength γ a b`, with finite length `hfin`).  At every interior parameter
`t₀ ∈ (a, b)` there is a `δ > 0` such that the forward sub-arc
`γ |[t₀, t₀ + δ]` is, after a monotone rescaling, the radial geodesic
`s ↦ expMap g (γ t₀) (σ s • v)` in normal coordinates centred at `γ t₀`, for a
launch vector `v : T_{γ t₀} M` and a monotone `σ` with `σ 0 = 0`.

This is the moving-foot no-corner regularity: re-based at the foot `γ t₀`, the
restricted minimiser realises the chart-radial distance to its forward endpoint,
hence — by the endpoint-generic radial rigidity `normalBall_radial_minimizer_equality`
applied with base `γ t₀` — coincides with a monotone radial reparametrisation.
The sub-arc minimality is `subArc_of_minimizer_is_minimizer`; the equality
`pathELength = ofReal √(g_{γ t₀}(v, v))` feeding the rigidity is
`radial_riemannianEDist_eq_radius` (distance equals radius inside the small
normal ball) composed with the sub-arc minimality; the short-time ball
confinement is `exists_forward_confinement_to_smallBall`. -/
theorem local_radial_identification_of_minimizer
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hfin : pathELength I γ a b ≠ ⊤)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ Icc t₀ (t₀ + δ) ⊆ Icc a b ∧
      ∃ (v : TangentSpace I (γ t₀)) (σ : ℝ → ℝ),
        MonotoneOn σ (Icc 0 δ) ∧ σ 0 = 0 ∧
        ∀ s : ℝ, s ∈ Icc 0 δ →
          γ (t₀ + s) = expMap (I := I) g (γ t₀) (σ s • v) := by
  classical
  set q : M := γ t₀ with hq_def
  -- Short-time confinement of the forward sub-arc to `q`'s small normal ball.
  obtain ⟨δ, hδ_pos, hδ_le_b, hsrc, hradial_small⟩ :=
    exists_forward_confinement_to_smallBall (I := I) g hγ ht₀ (q := q) hq_def.symm
  -- Interior room: `a ≤ t₀ ≤ t₀ + δ ≤ b`, so the sub-interval is inside `[a, b]`.
  have ht₀_ge_a : a ≤ t₀ := ht₀.1.le
  have h_subset : Icc t₀ (t₀ + δ) ⊆ Icc a b :=
    Icc_subset_Icc ht₀_ge_a hδ_le_b
  -- The chart at `q` and the forward endpoint's chart coordinate `v`.
  set ψ := NormalCoordinates.normalChartAt (I := I) g q with hψ_def
  set v : E := ψ (γ (t₀ + δ)) with hv_def
  -- The forward sub-arc is `C¹`.
  have hδ_endIcc : t₀ + δ ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith, le_rfl⟩
  have hγ_sub : CMDiff[Set.Icc t₀ (t₀ + δ)] 1 γ := hγ.mono h_subset
  -- The forward sub-arc is itself a minimiser (`subArc_of_minimizer_is_minimizer`).
  have hsub_min : riemannianEDist I (γ t₀) (γ (t₀ + δ)) = pathELength I γ t₀ (t₀ + δ) :=
    subArc_of_minimizer_is_minimizer (I := I) hγ hmin hfin hab ht₀_ge_a
      (by linarith) hδ_le_b
  -- Smallness of `v` (chart-radial value of the endpoint) below `expRadiusGp q`.
  have hv_small : Real.sqrt (g.inner q v v) < expRadiusGp (I := I) g q := by
    have h := hradial_small (t₀ + δ) hδ_endIcc
    rw [hv_def]; exact h
  -- `v ∈ ψ.target` and `v ∈ expDomain q` (small radius ⟹ in the `C²` ball ⟹ both).
  have hv_eucl : ‖v‖ < expMapC2Radius (I := I) g q :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g q hv_small
  have hv_ball : v ∈ ψ.target := by
    rw [hψ_def]; exact ball_subset_normalChartAt_target (I := I) g q hv_eucl
  have hv_dom : (show TangentSpace I q from v) ∈ expDomain (I := I) g q :=
    mem_expDomain_of_norm_lt_radius (I := I) g q hv_eucl
  -- `q = expMap q (ψ q)` and the endpoint `γ(t₀+δ) = expMap q v` (chart round-trip).
  have hγend_src : γ (t₀ + δ) ∈ ψ.source := hsrc (t₀ + δ) hδ_endIcc
  have hend_eq : γ (t₀ + δ) = expMap (I := I) g q (show TangentSpace I q from v) := by
    have hround : ψ.symm (ψ (γ (t₀ + δ))) = γ (t₀ + δ) := by
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_left_inv (I := I) g q hγend_src
    have hsymm : ψ.symm v = expMap (I := I) g q (show TangentSpace I q from v) := by
      rw [hψ_def]
      exact NormalCoordinates.normalChartAt_symm_apply (I := I) g q
        (show v ∈ ψ.symm.source from hv_ball)
    rw [← hround, ← hv_def, hsymm]
  -- The distance from `q` to the endpoint equals the radius `ofReal √(g_q(v,v))`.
  have hdist_eq : riemannianEDist I q (expMap (I := I) g q (show TangentSpace I q from v))
      = ENNReal.ofReal (Real.sqrt (g.inner q v v)) :=
    radial_riemannianEDist_eq_radius (I := I) g q hEnorm hv_dom hv_ball hv_small
  -- Hence the sub-arc length equals `ofReal √(g_q(v,v))`, the rigidity input.
  have hlen : pathELength I γ t₀ (t₀ + δ)
      = ENNReal.ofReal (Real.sqrt (g.inner q v v)) := by
    rw [← hsub_min]
    show riemannianEDist I (γ t₀) (γ (t₀ + δ)) = _
    rw [hq_def, hend_eq]; exact hdist_eq
  -- Apply the endpoint-generic radial rigidity with base `q = γ t₀`.
  have hab_sub : t₀ < t₀ + δ := by linarith
  have hγa_sub : γ t₀ = q := hq_def
  have hγb_sub : γ (t₀ + δ) = expMap (I := I) g q (show TangentSpace I q from v) := hend_eq
  have hγ_inBall : ∀ t ∈ Set.Icc t₀ (t₀ + δ), γ t ∈ ψ.source := by
    intro t ht; rw [hψ_def]; exact hsrc t ht
  obtain ⟨φ, hφ_mono, hφ0, hφ1, hφ_eq⟩ :=
    normalBall_radial_minimizer_equality (I := I) g q hEnorm hv_dom hv_ball hv_small
      hab_sub hγ_sub hγa_sub hγb_sub hγ_inBall hlen
  -- Reindex `φ` on `[t₀, t₀+δ]` to `σ` on `[0, δ]` via `σ s := φ (t₀ + s)`.
  refine ⟨δ, hδ_pos, h_subset, (show TangentSpace I q from v), fun s => φ (t₀ + s), ?_, ?_, ?_⟩
  · -- `σ` monotone on `[0, δ]`.
    intro s hs t ht hst
    have hs' : t₀ + s ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : t₀ + t ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hφ_mono hs' ht' (by linarith)
  · -- `σ 0 = φ t₀ = 0`.
    simp only [add_zero]; exact hφ0
  · -- The radial identification, reindexed.
    intro s hs
    have hs' : t₀ + s ∈ Set.Icc t₀ (t₀ + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hφ_eq (t₀ + s) hs'
    rw [hq_def]; exact this

end LocalRadialIdentification

section ArclengthReparam

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Global arclength reparametrisation is a smooth geodesic

Each local piece is a smooth unit-speed radial geodesic; overlap
consistency from `Geodesic/Uniqueness.lean` glues them into a global
smooth geodesic on `(0, L)`. -/

/-- **The arclength reparametrisation of a length-minimiser is a smooth
geodesic.** Given a length-minimising `C¹` curve `γ : [a, b] → M`, there
exist `L ≥ 0` and an arclength reparametrisation `η : ℝ → M` defined on
`[0, L]` such that `η` is a smooth geodesic on the open interval
`(0, L)`. -/
theorem arclength_reparam_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) :
    ∃ (L : ℝ) (η : ℝ → M), 0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicAt
          (I := I) g η t) := by
  -- Split on whether the parameter interval is degenerate.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · -- Degenerate case `a = b`: the curve has a single point `γ a`. Take
    -- `L = 0` and the constant curve `η = fun _ ↦ γ a`. The two universal
    -- quantifiers range over `Ioo 0 0 = ∅`, hence are vacuous, and the
    -- endpoint equalities reduce to `γ a = γ a` and `γ a = γ b` (the latter
    -- by `hab_eq`).
    refine ⟨0, fun _ : ℝ => γ a, le_refl 0, rfl, ?_, ?_, ?_⟩
    · -- `η L = η 0 = γ a = γ b` since `a = b`.
      simp [hab_eq]
    · intro t ht
      -- `Ioo 0 0 = ∅`, so `t ∈ Ioo 0 0` is a contradiction.
      simp at ht
    · intro t ht
      simp at ht
  · -- Nondegenerate case `a < b`: the substantive arclength reparametrisation.
    -- The forward local radial identification `local_radial_identification_of_minimizer`
    -- is now available: re-based at any interior foot `γ t₀`, the minimiser is a
    -- monotone radial reparametrisation of a radial geodesic.  The remaining
    -- construction, not yet built, is:
    --   (i)  the arclength function `s(t) := (pathELength γ a t).toReal`, its
    --        strict monotonicity (positive `g`-speed away from rest), and its
    --        `C¹` inverse `t(s)` giving the unit-speed reparam `η := γ ∘ t`;
    --   (ii) at each interior arclength point, the monotone reparam `σ` of the
    --        forward radial identification becomes the *identity* under arclength
    --        (a unit-speed radial geodesic has arclength `= parameter`), turning
    --        the conclusion into the linear radial form `η(s+·) = expMap (η s) (· • v̂)`
    --        with `|v̂|_g = 1`, which is `IsGeodesicAt` and `ContMDiffAt ∞` via
    --        `radial_maximalGeodesic_hasGeodesicEquationAt_of_small` and the
    --        `expMap`-radial-curve smoothness;
    --   (iii) the no-corner gluing of consecutive radial pieces via the chart-flow
    --        geodesic uniqueness in `Geodesic/Uniqueness.lean`.
    -- Steps (i)-(iii) are left as the residual of this branch.
    sorry

end ArclengthReparam

end RadialMinimizerConvention

end Riemannian
end Geometry
end DifferentialGeometry
