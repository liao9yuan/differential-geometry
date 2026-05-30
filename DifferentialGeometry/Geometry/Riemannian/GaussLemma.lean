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
`expMapC2Radius g p` below. -/

/-- The radius of a ball around the origin on which `expMap g p` is `C²`,
extracted from `expMap_contMDiffAt2_of_norm_lt`.  On `‖w‖ < expMapC2Radius g p`
the map `u ↦ expMap g p u` is `ContMDiffAt 𝓘(ℝ, E) I 2`.  This is the
genuine domain on which the second-order variational argument behind
Gauss's lemma is available. -/
def expMapC2Radius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  Classical.choose (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)

/-- The `C²` radius is strictly positive. -/
lemma expMapC2Radius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expMapC2Radius (I := I) g p :=
  (Classical.choose_spec
    (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)).1

/-- On the ball of radius `expMapC2Radius g p`, `expMap g p` is `C²`. -/
lemma expMap_contMDiffAt2_of_norm_lt_radius
    (g : SmoothRiemannianMetric I M) (p : M) {w : E}
    (hw : ‖w‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 2
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) w :=
  (Classical.choose_spec
    (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)).2 w hw

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
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
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
  have hIcc_sub_J : Set.Icc (0 : ℝ) 1 ⊆ J := by
    rw [hJ_eq]; intro x hx; obtain ⟨hx0, hx1⟩ := hx; exact ⟨by linarith, by linarith⟩
  have ht_J : t ∈ J := hIcc_sub_J ht
  have h0_J : (0 : ℝ) ∈ J := hIcc_sub_J ⟨le_rfl, zero_le_one⟩
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
      exact ⟨by nlinarith [ht'_pos.le, hT_pos.le], by nlinarith [ht'_lt_T.le, ht'_pos.le]⟩
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
  -- STATUS (verified during dispatch):
  --   * STEP 1 (radial geodesic property) is now CLOSED:
  --     `radial_maximalGeodesic_hasGeodesicEquationAt_of_small` (above, this file)
  --     proves, for every small `v` (`‖v‖ < (T/2)·ρ₀`) and every `t ∈ [0, 1]`,
  --     `HasGeodesicEquationAt g (fun s => maximalGeodesic g p v s) t`.  It routes
  --     the whole radial arc through the single uniform chart-pushed flow orbit of
  --     `exists_uniform_existence_interval`: the rescaled manifold lift
  --     `chartFlowOrbitLiftRescaled` is, on `Ioo (-2) 2 ⊇ [0, 1]`, a SINGLE
  --     `IsGeodesicOnWithInitial` witness whose projection equals
  --     `maximalGeodesic g p v`; the unconditional
  --     `IsGeodesicOnWithInitial.isGeodesicAt → IsGeodesicAt.hasGeodesicEquationAt`
  --     chain (foot-in-source from `chartFlowOrbitLiftRescaled_proj_mem_chartAt_source`)
  --     then gives the geodesic equation at every interior `t`, transferred to
  --     `maximalGeodesic` by `HasGeodesicEquationAt.congr_of_eventuallyEq_at`.
  --     This replaces the former blocker (a): no normal-chart / `expMapDiffeo`
  --     identification and no import cycle is needed.
  --   * STEP 2 (the variational assembly itself) is the remaining residual.  The
  --     `C²`-relaxed chart-level engines are public:
  --     `commute_ds_dt_fixed_chart_C2`, `hasDerivAt_innerW`, `nabla_t_nabla_s_eq`,
  --     `nabla_s_nabla_t_eq` (FixedChartIdentities.lean), and the velocity bridge
  --     `chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt`
  --     (MFDerivAlongCurve.lean).  But the INTRINSIC metric-compatibility product
  --     rule that converts a `t`-derivative of `g.inner (γ t) (V t) (W t)` into
  --     `⟨∇_t V, W⟩ + ⟨V, ∇_t W⟩` at `C²` regularity —
  --     `metric_compat_hasDerivAt_inner_of_chartCurveDeriv` (SecondVariation.lean) —
  --     is `private`, hence not importable here; and the conversion
  --     `HasGeodesicEquationAt → covDerivAlong velocity = 0` exists only in the
  --     `C^∞`-hypothesis form `covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt`
  --     (CovariantDerivativeAlong.lean), whereas the radial variation is only `C²`.
  --     Closing STEP 2 therefore requires: (i) de-privatising
  --     `metric_compat_hasDerivAt_inner_of_chartCurveDeriv` (a minimal,
  --     dependency-free visibility change); (ii) a `C²`-form
  --     `HasGeodesicEquationAt → covDerivAlong velocity = 0` (the backward direction
  --     of the existing iff uses only the unpacked geodesic identity, so it relaxes
  --     to `C²`, but it must be re-stated with `DifferentiableAt`-level hypotheses on
  --     `chartCurve (γ t) γ`); and (iii) the integration argument itself (FTC over
  --     `[0, 1]`, continuity / interval-integrability of the `C²`-only integrand,
  --     and the `½ ∂_s g.inner_p (v + s•w, v + s•w)|₀ = g.inner_p (v, w)` endpoint
  --     computation).  This is substantial new `C²`-relaxed infrastructure rather
  --     than a thin assembly, and is left as the residual.
  sorry

end GaussLemma

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

/-- **Inside the normal ball, every `C¹` curve from `p` to `expMap g p v`
has length at least the `g_p`-norm of `v`.** This is the length lower
bound delivered by Gauss's lemma; the equality-case identification of
the radial geodesic as the unique minimiser is the content of the prose
statement and the assembly downstream. The lower bound uses the
`g`-norm `√(g_p(v,v))`, not the model-space Euclidean norm `‖v‖_E`
(which has no a-priori relation to `g_p`). -/
theorem normalBall_radial_unique_minimizer
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) := by
  -- The classical Gauss-lemma length lower bound. We reduce to the
  -- forall-greater formulation of `riemannianEDist` as an infimum.
  -- For every `r` strictly larger than the distance, there is a smooth
  -- path `γ : [0, 1] → M` from `p` to `exp_p v` of `pathELength < r`.
  -- The Gauss-lemma curve-length lower bound (the orthogonal-decomposition
  -- argument inside a normal ball: pull back `γ` through normal
  -- coordinates, decompose the velocity into a radial and orthogonal
  -- part, and integrate) then forces `√(g_p(v,v)) ≤ pathELength γ`.
  -- Combining yields `√(g_p(v,v)) ≤ r` for every such `r`, which by
  -- forall-greater gives `√(g_p(v,v)) ≤ riemannianEDist`.
  --
  -- The curve-length lower bound (Gauss-lemma consequence inside a
  -- normal ball) is the substantive geometric content; isolating it as
  -- a named auxiliary fact captures the precise statement to be filled
  -- once `gauss_lemma_pullback` (still `sorry` above) is available.
  set q := expMap (I := I) g p (show TangentSpace I p from v) with hq_def
  -- The curve-length lower bound inside a normal ball, restated so it
  -- can be quantified over candidate paths produced by the infimum.
  have curveLengthLowerBound :
      ∀ {γ : ℝ → M} {a b : ℝ},
        a ≤ b → γ a = p → γ b = q → CMDiff[Set.Icc a b] 1 γ →
        (∀ t ∈ Set.Icc a b,
          γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) →
        ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
          pathELength I γ a b := by
    -- This is the Gauss-lemma length lower bound: orthogonal
    -- decomposition of `γ'` against the radial direction (via
    -- `gauss_lemma_pullback`) plus a `∫|r(t)| ≥ |∫r(t)|`-style
    -- integral inequality.
    --
    -- NOTE: `gauss_lemma_pullback` now carries the genuine domain hypothesis
    -- `‖v‖ < expMapC2Radius g p` (the `C²` ball on which the variational
    -- argument is available).  When filling this lower bound, invoke it on the
    -- radial directions `s • v` arising from the orthogonal decomposition, each
    -- of which satisfies `‖s • v‖ ≤ ‖v‖`; so the caller must first establish
    -- `‖v‖ < expMapC2Radius g p` (a new hypothesis to thread onto this theorem,
    -- as `hball : v ∈ normalChartAt.target` only places `v` in the opaque
    -- `expMapDiffeo`-source, which has no proven relation to the `C²` radius).
    sorry
  -- Now combine with the infimum characterisation of `riemannianEDist`.
  refine le_of_forall_gt (fun r hr => ?_)
  -- For every `r > riemannianEDist I p q`, get a path from `p` to `q`
  -- of length `< r`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one with
    ⟨γ, hγ0, hγ1, hγ_smooth, hγ_len, _, _⟩
  -- The lower bound holds for this path provided it stays inside the
  -- normal-ball source. Combining this lower bound (via
  -- `curveLengthLowerBound`, isolated above) with `hγ_len < r` yields
  -- `√(g_p(v,v)) < r`, hence the desired forall-greater conclusion.
  -- The "stays inside the normal ball" hypothesis is genuine: a path
  -- exiting the normal ball can have arbitrarily small length while
  -- the endpoints are still inside, by the Gauss-lemma argument it is
  -- handled by truncating at the first exit (so the radial bound
  -- applies on the truncated piece). We state and consume this
  -- in-ball hypothesis as a self-contained intermediate step.
  have hγ_inBall :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source := by
    -- Truncation argument: if `γ` leaves the normal ball, replace it
    -- by its initial in-ball segment plus an angle-correction; the
    -- length only decreases. This is the standard Gauss-lemma
    -- handling of paths that "escape" the normal chart's source.
    sorry
  have hγ1' : γ 1 = q := by simp [hq_def, hγ1]
  have hlb : ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      pathELength I γ (0 : ℝ) 1 :=
    curveLengthLowerBound zero_le_one hγ0 hγ1'
      hγ_smooth.contMDiffOn hγ_inBall
  exact lt_of_le_of_lt hlb hγ_len

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
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
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
  sorry

end RadialUniqueMinimizer

section LocalRadialIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Local radial identification of a minimiser

At any interior parameter of a length-minimising curve, there is a
`δ`-neighbourhood on which the curve, after rescaling, is a monotone
radial geodesic in normal coordinates at `γ(t₀)`. -/

/-- **Local radial identification.** Let `γ : ℝ → M` be a
length-minimising `C¹` curve on `[a, b]`. At every interior parameter
`t₀ ∈ (a, b)` there is a `δ > 0` such that the sub-arc
`γ |[t₀ - δ, t₀ + δ]` is (after monotone rescaling) the radial geodesic
`s ↦ expMap g (γ t₀) (s • v)` in normal coordinates at `γ t₀`, for some
tangent vector `v : TangentSpace I (γ t₀)`. -/
theorem local_radial_identification_of_minimizer
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b ∧
      ∃ v : TangentSpace I (γ t₀), ∀ s : ℝ, s ∈ Icc (-δ) δ →
        γ (t₀ + s) = expMap (I := I) g (γ t₀) (s • v) := by
  -- Extract interior-room data from `ht₀ : t₀ ∈ Ioo a b`.
  obtain ⟨ha_lt, hb_lt⟩ := ht₀
  have hδ_left_pos : 0 < t₀ - a := sub_pos.mpr ha_lt
  have hδ_right_pos : 0 < b - t₀ := sub_pos.mpr hb_lt
  -- Choose `δ := min (t₀ - a) (b - t₀) / 2`. Halving gives room on both
  -- sides while keeping `δ > 0`.
  set δ := min (t₀ - a) (b - t₀) / 2 with hδ_def
  have hmin_pos : 0 < min (t₀ - a) (b - t₀) := lt_min hδ_left_pos hδ_right_pos
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact half_pos hmin_pos
  -- The interval bound `Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b`.
  have hδ_le_left : δ ≤ t₀ - a := by
    rw [hδ_def]
    have h₁ : min (t₀ - a) (b - t₀) ≤ t₀ - a := min_le_left _ _
    have h₂ : min (t₀ - a) (b - t₀) / 2 ≤ min (t₀ - a) (b - t₀) := by
      exact half_le_self hmin_pos.le
    exact h₂.trans h₁
  have hδ_le_right : δ ≤ b - t₀ := by
    rw [hδ_def]
    have h₁ : min (t₀ - a) (b - t₀) ≤ b - t₀ := min_le_right _ _
    have h₂ : min (t₀ - a) (b - t₀) / 2 ≤ min (t₀ - a) (b - t₀) := by
      exact half_le_self hmin_pos.le
    exact h₂.trans h₁
  have h_lower : a ≤ t₀ - δ := by linarith
  have h_upper : t₀ + δ ≤ b := by linarith
  have h_subset : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b :=
    Icc_subset_Icc h_lower h_upper
  -- The witness `v : TangentSpace I (γ t₀)` and the radial identification
  -- `γ(t₀ + s) = expMap g (γ t₀) (s • v)` for `s ∈ [-δ, δ]` is the
  -- equality case of the Gauss-lemma minimiser identification. The
  -- proof composes `subArc_of_minimizer_is_minimizer` (with `hfin`
  -- derived from `hmin` plus `riemannianEDist ≤ pathELength`) followed
  -- by the equality case of `normalBall_radial_unique_minimizer`
  -- (currently a length lower bound; the equality case sits as a
  -- pending substep upstream). We isolate the existence of the witness
  -- as an intermediate claim consumed below.
  have hwitness :
      ∃ v : TangentSpace I (γ t₀), ∀ s : ℝ, s ∈ Icc (-δ) δ →
        γ (t₀ + s) = expMap (I := I) g (γ t₀) (s • v) := by
    -- The sub-arc on `[t₀ - δ, t₀ + δ]` is itself a minimiser (via
    -- `subArc_of_minimizer_is_minimizer`); inside the normal chart at
    -- `γ t₀` the equality case of `normalBall_radial_unique_minimizer`
    -- forces the sub-arc to coincide with a radial geodesic. The
    -- explicit construction of `v` from this equality case is the
    -- remaining substep, pending the upstream equality-case fill.
    sorry
  -- Package the choice of `δ`, the room subset, and the witness.
  exact ⟨δ, hδ_pos, h_subset, hwitness⟩

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
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
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
  · -- Nondegenerate case `a < b`: this is the substantive arclength
    -- reparametrisation, requiring `local_radial_identification_of_minimizer`
    -- (still a `sorry` in this file) plus a global gluing argument via
    -- geodesic uniqueness. The construction is: pull the arclength parameter
    -- `s : [a, b] → [0, L]` through the local radial-geodesic identification
    -- on each `δ`-neighbourhood, then glue using the chart-flow uniqueness
    -- in `Geodesic/Uniqueness.lean`. We leave this branch as a `sorry` until
    -- the local-radial identification lemma is filled and the global
    -- gluing infrastructure is built.
    sorry

end ArclengthReparam

end Riemannian
end Geometry
end DifferentialGeometry
