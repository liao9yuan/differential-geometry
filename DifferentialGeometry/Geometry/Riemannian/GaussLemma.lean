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
geodesic on `[0, 1]`, and the radius of the geodesic rescaling identity. -/
def expMapC2Radius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  min (Classical.choose (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p))
    (min
      (Classical.choose
        (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p))
      (Classical.choose
        (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)))

/-- The combined radius is strictly positive. -/
lemma expMapC2Radius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < expMapC2Radius (I := I) g p := by
  rw [expMapC2Radius, lt_min_iff, lt_min_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact (Classical.choose_spec
      (Exponential.expMap_contMDiffAt2_of_norm_lt (I := I) g p)).1
  · exact (Classical.choose_spec
      (radial_maximalGeodesic_hasGeodesicEquationAt_of_small (I := I) g p)).1
  · exact (Classical.choose_spec
      (Exponential.maximalGeodesic_rescale_at_one_of_small (I := I) g p)).1

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
    (lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))) t ht

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
