import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Unconditional
import DifferentialGeometry.Geometry.Riemannian.Exponential.FinalClosure

set_option linter.unusedSectionVars false

/-!
# Off-zero `ContMDiffAt 1` regularity of `expMap`

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file records the
off-zero (`v ≠ 0`) analogue of the at-zero smoothness lemma
`expMap_contMDiffAt_zero_unconditional`.

Away from the zero vector the regularity of the exponential map is
unconditional: the `HasChartFlowGeodesicMatchData` hypothesis required at
the zero vector is not needed once `v ≠ 0`, because the geodesic flow is
jointly smooth in `(t, v)` along any orbit with non-zero initial velocity.

## Main result

* `off_zero_exp_regularity` — for `v ≠ 0`, the exponential map
  `fun w : E => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v`.

## Single-chart building blocks (M1 / M2)

The off-zero argument is the analogue of the at-zero argument with the
fixed home chart `extChartAt I p` replaced by a chain of charts along the
geodesic arc `[0, 1] ∋ s ↦ maximalGeodesic g p v s`. Two of its
ingredients are single-chart and are recorded here, fully proven:

* **M1 (single-chart slice C¹).** The chart-flow candidate
  `chartFlowCandidate Φ p t'` produced by the unified packaging is
  `ContMDiffAt 𝓘(ℝ, E) I 1` *at every* `v₁` in the spatial ball of the
  unified data, not only at `v₁ = 0`. This is `private`
  `chartFlowCandidate_contMDiffAt_of_mem_ball` below; it generalises the
  zero-point lemma `chartFlowCandidate_contMDiffAt_zero_at_origin` to an
  arbitrary interior point of the ball, by evaluating the `ContDiffOn 1`
  flow at that point rather than at the centre.

* **M2 (single-curve identification by uniqueness).** Along a single
  home chart, `(chartFlowOrbitLiftRescaled Φ p t' v 1).proj =
  expMap g p (t' • v)` — the rescaled-lift projection identity at `s = 1`
  (`chartFlowOrbitLiftRescaled_proj_at_one`, proven in `RescaledLift.lean`
  via preconnected propagation against the chosen maximal-geodesic curve).
  Combined with M1 this yields the *small-vector* off-zero statement
  `expMap_contMDiffAt_of_norm_lt` below: `w ↦ expMap g p w` is
  `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w` with `‖w‖ < t' * ρ` (a
  punctured ball whose closure stays inside the home chart's reach).

These two are the single-chart skeleton of the off-zero argument. The
remaining content — reaching an arbitrary fixed `v ≠ 0` whose geodesic
leaves the home chart — is genuinely cross-chart and is supplied by the
re-basing and chart-cover gluing recorded as separate obligations
(`Geodesic.bm_c_gc_cross_vf_projection_uniqueness` and the chained-flow
joint regularity); see the proof of `off_zero_exp_regularity`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## M1: single-chart slice `C¹` at a general ball point

The chart-coordinate slice of a jointly-`C¹` flow `Φ` is `ContDiffAt 1`
at any point `v₁` lying strictly inside the spatial ball, by evaluating
the `ContDiffOn 1` regularity at `((x₀, v₁), t')` (an interior point of
the domain product) and composing with the smooth affine embedding
`v ↦ ((x₀, v), t')`. -/

section SliceAtBallPoint

/-- **Slice `C¹` at a general ball point.** For a chart-flow `Φ`,
`ContDiffOn ℝ 1` on `ball ((x₀, 0), ρ) ×ˢ Ioo (-T) T`, and `v₁` with
`‖v₁‖ < ρ`, `t' ∈ Ioo (-T) T`, the velocity slice
`v ↦ (Φ((x₀, v), t')).1` is `ContDiffAt ℝ 1` at `v₁`. -/
private lemma contDiffAt_chartFlow_slice_fst_of_mem_ball
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ := by
  classical
  -- The affine embedding `v ↦ ((x₀, v), t')` is `C^1`.
  have hpair_cd : ContDiff ℝ 1 (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ 1 (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ 1 (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ 1 (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ 1 (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  -- `Φ` is `ContDiffAt ℝ 1` at the interior point `((x₀, v₁), t')`.
  have hmem : (((x₀, v₁) : E × E), t') ∈
      (Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T := by
    refine ⟨?_, ht'⟩
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    -- `max (dist x₀ x₀) (‖v₁‖) = ‖v₁‖ < ρ`.
    have : max (0 : ℝ) ‖v₁‖ = ‖v₁‖ := max_eq_right (norm_nonneg v₁)
    rw [this]; exact hv₁
  have hopen : IsOpen
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hΦ_cda : ContDiffAt ℝ 1 Φ (((x₀, v₁) : E × E), t') :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  -- Compose with the affine embedding and project to the first coordinate.
  have hslice : ContDiffAt ℝ 1 (fun v : E => Φ (((x₀, v) : E × E), t')) v₁ :=
    hΦ_cda.comp v₁ hpair_cd.contDiffAt
  have hfst : ContDiff ℝ 1 (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp v₁ hslice

end SliceAtBallPoint

/-! ## M1 (continued): the manifold-valued candidate is `C¹` at a ball point

We lift the chart-coordinate slice `C¹` to the manifold-valued candidate
`chartFlowCandidate Φ p t'`, under the hypothesis (supplied uniformly by
the unified packaging) that the slice's value at `v₁` lands in the
chart-target interior. -/

section CandidateAtBallPoint

variable [I.Boundaryless] [CompleteSpace E]

/-- **Candidate `ContMDiffAt 1` at a general ball point.** If the
chart-flow `Φ` is `ContDiffOn ℝ 1` on the velocity ball product, `v₁`
lies in the open ball of radius `ρ`, `t' ∈ Ioo (-T) T`, and the slice's
value at `v₁` lands in the chart target, then the manifold-valued
candidate `chartFlowCandidate Φ p t'` is `ContMDiffAt 𝓘(ℝ, E) I 1` at
`v₁`.

This is M1: the single-chart slice smoothness generalised from the centre
`v₁ = 0` of the at-zero argument to an arbitrary interior point. -/
private lemma chartFlowCandidate_contMDiffAt_of_mem_ball
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T t' : ℝ} {v₁ : E}
    (hv₁ : ‖v₁‖ < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T))
    (hval : (Φ (((extChartAt I p p, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') v₁ := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  -- The slice's first coordinate is `C^1` at `v₁`.
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) v₁ :=
    contDiffAt_chartFlow_slice_fst_of_mem_ball (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁ ht' hcd
  -- The slice value at `v₁` lies in the chart target.
  have hval_target : (Φ (((x₀, v₁) : E × E), t')).1 ∈ (extChartAt I p).target :=
    interior_subset hval
  -- The candidate is `(extChartAt I p).symm ∘ (slice's first coordinate)`.
  -- The inner slice is `ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 1` (a map `E → E` from a
  -- `ContDiffAt`), landing (eventually, by continuity) in the chart target,
  -- on which `(extChartAt I p).symm` is `ContMDiffOn 𝓘(ℝ,E) I 1`. Compose.
  set s : E → E := fun v => (Φ (((x₀, v) : E × E), t')).1 with hs_def
  have hs_cmda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 s v₁ :=
    hslice.contMDiffAt
  -- `(extChartAt I p).symm` is `ContMDiffWithinAt` on the target at the
  -- slice value, and the target is a neighbourhood of that value (interior).
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I p).symm (extChartAt I p).target (s v₁) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) p hval_target
  -- Upgrade to `ContMDiffAt` since the target is a neighbourhood of `s v₁`.
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 (s v₁) :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hval⟩
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I p).symm (s v₁) :=
    hsymm_within.contMDiffAt htarget_nhds
  -- Compose: the candidate equals `(extChartAt I p).symm ∘ s`.
  have hcand_eq : chartFlowCandidate (I := I) Φ p t' =
      (extChartAt I p).symm ∘ s := by
    funext v
    simp only [chartFlowCandidate_apply, Function.comp_apply, hs_def, hx₀_def]
  rw [hcand_eq]
  exact hsymm_at.comp v₁ hs_cmda

end CandidateAtBallPoint

/-! ## M1 + M2: the small-vector off-zero `C¹` statement

Combining the candidate's `C¹` smoothness at an arbitrary ball point
(M1) with the rescaled-lift projection identity at `s = 1` (M2), the
exponential map is `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w` whose norm is
small enough that the geodesic `[0, 1] ∋ s ↦ γ_w(s)` stays inside the
home chart's reach. -/

section SmallVector

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Small-vector off-zero `C¹`.** There is a radius `δ > 0` such that
`w ↦ expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w` with
`‖w‖ < δ`. This includes nonzero `w`: it is the off-zero analogue of the
at-zero headline, restricted to the single home chart `extChartAt I p`.

The proof reuses the unified chart-flow packaging
(`exists_unified_chartFlow_data`), M1
(`chartFlowCandidate_contMDiffAt_of_mem_ball`) for the candidate's `C¹`
smoothness on the whole spatial ball, and M2
(`chartFlowOrbitLiftRescaled_proj_at_one`) for the identification
`expMap g p (t' • v) = chartFlowCandidate Φ p t' v`, then transfers
through the smooth rescaling `w ↦ (1 / t') • w`. -/
theorem expMap_contMDiffAt_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ →
      ContMDiffAt 𝓘(ℝ, E) I 1
        (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        w := by
  classical
  obtain ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le_T,
    hΦ_cd, hΦ_init0, hΦ_init_v, hΦ_target, hΦ_phase, hΦ_const_zero, _hF_int⟩ :=
    exists_unified_chartFlow_data (I := I) g p
  set t' : ℝ := T_match / 2 with ht'_def
  have ht'_pos : 0 < t' := by rw [ht'_def]; exact half_pos hT_match_pos
  have ht'_lt_T_match : t' < T_match := by
    rw [ht'_def]; exact half_lt_self hT_match_pos
  have ht'_lt_T : t' < T := lt_of_lt_of_le ht'_lt_T_match hT_match_le_T
  have ht'_in_Ioo : t' ∈ Set.Ioo (-T) T := ⟨by linarith, ht'_lt_T⟩
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  -- Match identification: `expMap g p (t' • v) = chartFlowCandidate Φ p t' v`
  -- for every `v` in the spatial ball.
  set x₀ : E := extChartAt I p p with hx₀_def
  have hmatch : ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v := by
    intro v hv_ball
    have hΦ_init_v_at : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) :=
      hΦ_init_v v hv_ball
    have hΦ_target_v : ∀ s ∈ Set.Icc (-T) T,
        Φ (((x₀, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      intro s hs; exact hΦ_target v hv_ball s hs
    have hΦ_phase_v : ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
          (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := by
      intro s hs; exact hΦ_phase v hv_ball s hs
    have hproj1 :=
      chartFlowOrbitLiftRescaled_proj_at_one (I := I) (g := g) (p := p) (v := v)
        (T := T) (t' := t') ht'_pos ht'_lt_T (Φ := Φ)
        hΦ_init_v_at hΦ_target_v hΦ_phase_v
    have hΦ_target_t' : Φ (((x₀, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      rw [mul_one]
      exact hΦ_target_v t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'
    have hcand_unfold : chartFlowCandidate (I := I) Φ p t' v =
        (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := rfl
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := by
      rw [hproj_def, mul_one]
    rw [← hproj1, hproj_def', ← hcand_unfold]
  -- The off-zero radius: `δ := t' * ρ`. For `‖w‖ < δ`, `v := (1/t') • w`
  -- has `‖v‖ < ρ`, so M1 + the match give `C¹` at `w = t' • v`.
  refine ⟨t' * ρ, by positivity, ?_⟩
  intro w hw
  set v₁ : E := (1 / t') • w with hv₁_def
  have hv₁_norm : ‖v₁‖ < ρ := by
    rw [hv₁_def, norm_smul]
    have h1t' : ‖(1 / t' : ℝ)‖ = 1 / t' := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1t']
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ ht'_pos]
    calc ‖w‖ < t' * ρ := hw
      _ = ρ * t' := by ring
  have hv₁_ball : v₁ ∈ Metric.ball (0 : E) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₁_norm
  have htv₁_eq_w : t' • v₁ = w := by
    rw [hv₁_def, smul_smul, mul_one_div, div_self ht'_ne, one_smul]
  -- M1: candidate is `C¹` at `v₁`.
  have hval_int : (Φ (((x₀, v₁) : E × E), t')).1 ∈
      interior (extChartAt I p).target := by
    have := hΦ_target v₁ hv₁_ball t' (Set.Ioo_subset_Icc_self ht'_in_Ioo)
    exact this.1
  have hcand_cd : ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') v₁ :=
    chartFlowCandidate_contMDiffAt_of_mem_ball (I := I) (p := p) (Φ := Φ)
      (ρ := ρ) (T := T) (t' := t') (v₁ := v₁) hv₁_norm ht'_in_Ioo hΦ_cd hval_int
  -- Compose with smooth rescaling `u ↦ (1 / t') • u`.
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun u : E => (1 / t') • u) := by
    have h0 : ContDiff ℝ ∞ (fun u : E => (1 / t') • u) :=
      contDiff_const.smul contDiff_id
    have h1 : ContDiff ℝ 1 (fun u : E => (1 / t') • u) :=
      h0.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.contMDiff
  have hsmul_at : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun u : E => (1 / t') • u) w := hsmul_cd.contMDiffAt
  have hsmul_w_eq : (fun u : E => (1 / t') • u) w = v₁ := by
    rw [hv₁_def]
  have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t')
      ((fun u : E => (1 / t') • u) w) := by
    rw [hsmul_w_eq]; exact hcand_cd
  have hcomp : ContMDiffAt 𝓘(ℝ, E) I 1
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) w :=
    hcand_cd'.comp w hsmul_at
  -- `expMap g p u =ᶠ chartFlowCandidate Φ p t' ((1/t') • u)` near `w`.
  have hev :
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M))
        =ᶠ[𝓝 w]
      ((chartFlowCandidate (I := I) Φ p t') ∘ (fun u : E => (1 / t') • u)) := by
    have hsmul_cont : Continuous (fun u : E => (1 / t') • u) :=
      continuous_const.smul continuous_id
    have hpre : (fun u : E => (1 / t') • u) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 w := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun u : E => (1 / t') • u) w) := by
        rw [hsmul_w_eq]; exact Metric.isOpen_ball.mem_nhds hv₁_ball
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with u hu
    have hheq := hmatch ((1 / t') • u) hu
    have htu_eq : t' • ((1 / t') • u) = u := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htu_eq] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from u) : M) = _
    simp only [Function.comp_apply]
    exact hheq
  exact hcomp.congr_of_eventuallyEq hev

end SmallVector

section OffZero

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Off-zero unconditional regularity.** For any smooth Riemannian metric
`g`, base point `p : M`, and non-zero tangent vector `v ≠ 0`, the
exponential map `fun w => expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v`.

This is the off-zero analogue of `expMap_contMDiffAt_zero_unconditional`;
the `HasChartFlowGeodesicMatchData` hypothesis needed at the zero vector is
dropped, since away from `0` the geodesic flow's joint smoothness in
`(t, v)` yields the regularity unconditionally. -/
theorem off_zero_exp_regularity
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M))
      v := by
  -- M1 (`chartFlowCandidate_contMDiffAt_of_mem_ball`) and M2
  -- (`chartFlowOrbitLiftRescaled_proj_at_one`, via the small-vector
  -- assembly `expMap_contMDiffAt_of_norm_lt`) close the single-home-chart
  -- case: `w ↦ expMap g p w` is `ContMDiffAt 𝓘(ℝ, E) I 1` at every `w`
  -- with `‖w‖ < δ` for a chart-dependent `δ > 0`. They do NOT reach a
  -- fixed `v ≠ 0` of arbitrary magnitude, whose geodesic arc
  -- `[0, 1] ∋ s ↦ maximalGeodesic g p v s` generically LEAVES the home
  -- chart `extChartAt I p` (and there is no geodesic-homogeneity rescaling
  -- in `Geodesic/Homogeneity.lean` — only the trivial time-`0` and `1 • v`
  -- cases — that could shrink `v`).
  --
  -- The remaining obligations are genuinely cross-chart:
  --
  --   M3 (cross-VF re-basing): for each `s₀ ∈ [0, 1]` produce, near `s₀`,
  --   a `γ(s₀)`-centred local integral curve of `geodesicVectorFieldChart`
  --   whose projection agrees with the maximal geodesic, jointly `C¹` in
  --   the initial velocity. The projection-uniqueness re-basing exists as
  --   `Geodesic.bm_c_gc_cross_vf_projection_uniqueness`
  --   (`Geodesic/CrossVFReduction.lean`), but it is currently `sorry`-backed
  --   at its foot-in-source residual (`CrossVFReduction.lean:626`), and it
  --   delivers only the per-curve eventual equality, not the
  --   joint-in-velocity `C¹` flow.
  --
  --   M4 (chart-cover gluing): chain the per-chart joint-`C¹` flows
  --   (`Geodesic.SmoothFlow.exists_chartPhase_contDiffOn_isLocalFlow_combined`)
  --   across the finitely many chart junctions covering the compact arc
  --   (Lebesgue-number partition) via the local-flow group property,
  --   uniformly in the initial velocity, and evaluate the chained flow at
  --   `t = 1`. The continuity-only analogue is recorded as
  --   `bm_c_expMap_chainedFlow_joint_continuity`
  --   (`ChainedFlowContinuity.lean:171`, `sorry`-backed); the `C¹`-in-`(v, t)`
  --   strengthening is what is needed here.
  --
  -- Precise missing producer signature (would close this `sorry`): a lemma
  --   `∃ δ > 0, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ,E).prod I) 1
  --      (fun (vt : E × ℝ) => maximalGeodesic g p vt.1 vt.2) (v, 1)`
  -- (joint `C¹` regularity of the chained geodesic flow at `(v, 1)`),
  -- after which `off_zero_exp_regularity` follows by precomposing with the
  -- smooth slice `w ↦ (w, 1)` exactly as in
  -- `bm_c_expMap_continuity_from_jointFlow`.
  sorry

end OffZero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
