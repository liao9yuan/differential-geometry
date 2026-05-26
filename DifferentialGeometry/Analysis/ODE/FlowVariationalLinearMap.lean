import DifferentialGeometry.Analysis.ODE.FlowCkVariational
import Mathlib.Analysis.ODE.Gronwall

/-!
# Joint `C^1` smoothness of the variational linear map (building blocks)

The goal: for a time-dependent vector field `f : ℝ → E → E` jointly `C^2` in
`(t, x)` and a local Picard–Lindelöf flow `Φ`, build a joint-`C^1`
spatial-piece function `Y : E × ℝ → (E →L[ℝ] E)` satisfying
`IsVariationalFlowProjection hΦ T_eff ρ_eff Y 1` for some shrunk
`(T_eff, ρ_eff)`.

The clean construction uses the *augmented flow*: the augmented vector field
`augVF f` on `E × (E →L[ℝ] E)` is jointly `C^1` whenever `f` is jointly
`C^2`, so its Picard–Lindelöf flow `aΦ` is jointly `C^1` on a strictly-interior
open neighbourhood of `((x₀, id), t₀)` by `contDiffOn_flow_of_isLocalFlow`
applied to `aΦ` itself.  The projection `Y(x, t) := (aΦ ⟨(x, id), t⟩).2`
inherits joint `C^1`-smoothness via `contDiffOn_fromAugFlow`, and the
variational identification `Y q = variationalLinearMapAt(...)` holds pointwise.

This file ships **two atomic building-block lemmas** that the orchestrator
combines downstream to close the projection witness:

## Headlines

* `orbit_eq_of_augFlow_isLocalFlow` — orbit-equality identification.  The first
  projection of an augmented PL flow agrees with the original PL flow on a
  neighbourhood of `t₀`, via `ODE_solution_unique_of_eventually`.  This is the
  bridge that lets us identify `variationalLinearMapAt(α := Φ⟨x, ·⟩, t)` with
  `variationalLinearMapAt(α := s ↦ (aΦ ⟨(x, id), s⟩).1, t)` once the two
  orbits agree pointwise.

* `contDiffOn_fromAugFlow_inherits` — the joint smoothness of the projection
  inherits from the joint smoothness of the augmented flow.  Given `aΦ` is
  jointly `C^1` on a neighbourhood of `((x₀, id), t₀)`, the function
  `Y := fromAugFlow aΦ` is jointly `C^1` on the embedded neighbourhood of
  `(x₀, t₀)`.

The remaining unconditional step — running `contDiffOn_flow_of_isLocalFlow` on
the augmented system requires a uniform-in-orbit operator-norm bound `M_aug`
on the augmented linearization — needs either `[FiniteDimensional ℝ E]` (so
closed balls are compact, giving `M_aug` from joint continuity) or a careful
Grönwall-based bound using the augmented PL constants.  Both routes are
independent of this file and shipped downstream.

All theorems are formulated on a generic Banach space `E`; `[InnerProductSpace ℝ E]`
is *not* used.  No manifold or tensor file is imported.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Orbit-equality lemma

Both the original local flow `Φ` and the first projection of the augmented local
flow `aΦ` are solutions of the original ODE `y' = f t y` with initial value `x`
at time `t₀`.  By Picard–Lindelöf uniqueness applied locally near `t₀`, they
agree on a neighbourhood of `t₀`. -/

section OrbitEquality

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

set_option maxHeartbeats 2400000 in
/--
**Orbit-equality lemma.**  If `aΦ` is a local flow of the augmented field
`augVF f` centred at `((x₀, id), t₀)`, `Φ` is a local flow of `f` centred at
`(x₀, t₀)`, and `(t₀, x)` lies in the interior of both flows' time domains,
then the orbit `s ↦ Φ ⟨x, s⟩` agrees with the first projection
`s ↦ (aΦ ⟨(x, id), s⟩).1` on a neighbourhood of `t₀`.

The proof uses `ODE_solution_unique_of_eventually` applied to the original ODE
`v t y := f t y`, with the local Lipschitz constant of `uncurry f` at `(t₀, x)`
supplied by `ContDiffAt.exists_lipschitzOnWith`.
-/
theorem orbit_eq_of_augFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    (ht₀_Φ : t₀ ∈ Ioo tmin tmax) (ht₀_a : t₀ ∈ Ioo tmin_a tmax_a) :
    (fun s => Φ ⟨x, s⟩) =ᶠ[𝓝 t₀]
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) := by
  -- The "ambient" Lipschitz constant for `f` at `(t₀, x)`.
  have hcd_at : ContDiffAt ℝ 1 (uncurry f) (t₀, x) :=
    hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
  obtain ⟨K, sNhd, hsNhd, hl⟩ := hcd_at.exists_lipschitzOnWith
  -- Shrink to a metric ball around `(t₀, x)` inside the Lipschitz neighbourhood.
  obtain ⟨ρ_Lip, hρ_Lip_pos, hρ_Lip_sub⟩ := Metric.mem_nhds_iff.mp hsNhd
  -- The two orbits.
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_init : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_init : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  -- Continuity of `α_Φ` at `t₀`.
  have hIcc_nhds_Φ : Icc tmin tmax ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_Φ) Ioo_subset_Icc_self
  have hIcc_nhds_a : Icc tmin_a tmax_a ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_a) Ioo_subset_Icc_self
  have hα_Φ_cont_on : ContinuousOn α_Φ (Icc tmin tmax) := hΦ.orbit_continuousOn x hx_Φ
  have hα_Φ_cont : ContinuousAt α_Φ t₀ :=
    hα_Φ_cont_on.continuousAt hIcc_nhds_Φ
  -- Continuity of `α_a` at `t₀`.
  have h_orbit_cont_on : ContinuousOn
      (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
      (Icc tmin_a tmax_a) :=
    haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
  have hα_a_cont : ContinuousAt α_a t₀ := by
    have h_pair_cont_at : ContinuousAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) t₀ :=
      h_orbit_cont_on.continuousAt hIcc_nhds_a
    exact continuous_fst.continuousAt.comp h_pair_cont_at
  -- The set `S := ball x (ρ_Lip / 2)`.
  set ρ' : ℝ := ρ_Lip / 2 with hρ'_def
  have hρ'_pos : 0 < ρ' := by positivity
  have hρ'_lt_Lip : ρ' < ρ_Lip := by rw [hρ'_def]; linarith
  set S : Set E := ball x ρ' with hS_def
  have hS_nhds_x : S ∈ 𝓝 x := ball_mem_nhds x hρ'_pos
  -- Eventually near `t₀`: `α_Φ t ∈ S` and `α_a t ∈ S`.
  have hα_Φ_eventually : ∀ᶠ t in 𝓝 t₀, α_Φ t ∈ S := by
    have h := hα_Φ_cont (show S ∈ 𝓝 (α_Φ t₀) by rw [hα_Φ_init]; exact hS_nhds_x)
    exact h
  have hα_a_eventually : ∀ᶠ t in 𝓝 t₀, α_a t ∈ S := by
    have h := hα_a_cont (show S ∈ 𝓝 (α_a t₀) by rw [hα_a_init]; exact hS_nhds_x)
    exact h
  -- Eventually near `t₀`: `f t` is `K`-Lipschitz on `S`.
  have h_v_lip_event : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (f t) S := by
    rw [eventually_iff_exists_mem]
    refine ⟨ball t₀ ρ', ball_mem_nhds t₀ hρ'_pos, ?_⟩
    intro t ht
    rw [mem_ball] at ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y₁ hy₁ y₂ hy₂
    have h_pair₁ : ((t, y₁) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₁
      have hmax_le_ρ' : max (dist t t₀) (dist y₁ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₁)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_pair₂ : ((t, y₂) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₂
      have hmax_le_ρ' : max (dist t t₀) (dist y₂ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₂)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_in_S₁ : ((t, y₁) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₁
    have h_in_S₂ : ((t, y₂) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₂
    have hd : dist (uncurry f (t, y₁)) (uncurry f (t, y₂))
        ≤ K * dist ((t, y₁) : ℝ × E) (t, y₂) :=
      hl.dist_le_mul _ h_in_S₁ _ h_in_S₂
    have hdist_eq : dist ((t, y₁) : ℝ × E) (t, y₂) = dist y₁ y₂ := by
      rw [Prod.dist_eq]; simp [dist_self]
    rw [hdist_eq] at hd
    change dist (uncurry f (t, y₁)) (uncurry f (t, y₂)) ≤ K * dist y₁ y₂
    exact hd
  -- Derivative hypotheses for `α_Φ` and `α_a` near `t₀`.
  have hα_Φ_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_Φ (f t (α_Φ t)) t ∧ α_Φ t ∈ S := by
    have h_int : Ioo tmin tmax ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_Φ
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_Φ_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_dw : HasDerivWithinAt (fun s => Φ ⟨x, s⟩) (f t (Φ ⟨x, t⟩))
        (Icc tmin tmax) t :=
      hΦ.hasDerivWithinAt x hx_Φ t (Ioo_subset_Icc_self ht_int)
    have hIcc_nhds_t : Icc tmin tmax ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    exact h_dw.hasDerivAt hIcc_nhds_t
  have hα_a_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_a (f t (α_a t)) t ∧ α_a t ∈ S := by
    have h_int : Ioo tmin_a tmax_a ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_a
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_a_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_orbit_dw : HasDerivWithinAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        (Icc tmin_a tmax_a) t :=
      haΦ.hasDerivWithinAt _ hx_a t (Ioo_subset_Icc_self ht_int)
    have hIcc_a_nhds_t : Icc tmin_a tmax_a ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    have h_orbit_at : HasDerivAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)) t :=
      h_orbit_dw.hasDerivAt hIcc_a_nhds_t
    -- Project to the first component via `ContinuousLinearMap.fst`.
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))) t :=
      h_fst_fd.comp_hasDerivAt t h_orbit_at
    -- `fst (augVF f t (a, b)) = f t a`.
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        = f t (α_a t) := by
      change (augVF f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)).1
        = f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1
      rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  -- Apply `ODE_solution_unique_of_eventually`.
  have h_init_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_init, hα_a_init]
  exact ODE_solution_unique_of_eventually
    (K := K) (v := fun t y => f t y) (s := fun _ => S)
    h_v_lip_event hα_Φ_deriv_event hα_a_deriv_event h_init_eq

end OrbitEquality

/-! ## Smoothness inheritance for the projection

The function `Y(x, t) := (aΦ ⟨(x, id), t⟩).2` (i.e. `fromAugFlow aΦ`) inherits
joint smoothness from the augmented flow `aΦ`.  This is a direct repackaging of
`contDiffOn_fromAugFlow` and reduces the joint `C^1`-smoothness of `Y` to that
of `aΦ`, which is in turn delivered by `contDiffOn_flow_of_isLocalFlow` applied
to the augmented system. -/

section SmoothnessInheritance

variable {f : ℝ → E → E} {x₀ : E} {t₀ : ℝ}

/-- **Smoothness inheritance for the projection.**  If `aΦ` is jointly `C^1` on
the open neighbourhood `(ball (x₀, id) (ρ_a : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)`,
and the spatial radius `ρ` and time width `T` satisfy `(ρ : ℝ) ≤ (ρ_a : ℝ)` and
`T ≤ T_a`, then the projection `fromAugFlow aΦ` is jointly `C^1` on the
corresponding neighbourhood `ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem contDiffOn_fromAugFlow_inherits
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {ρ_a ρ : ℝ≥0} {T_a T : ℝ}
    (hρ_le : (ρ : ℝ) ≤ (ρ_a : ℝ)) (hT_le : T ≤ T_a)
    (haΦ_C1 : ContDiffOn ℝ 1 aΦ
      ((ball ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E))
          (ρ_a : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a))) :
    ContDiffOn ℝ 1 (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Embedding `(x, t) ↦ ((x, id), t)` maps the small neighbourhood into the large.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  set U : Set (E × ℝ) := ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T) with hU_def
  set U_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    ball p₀ (ρ_a : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_a_def
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U U_a := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hq_x ⊢
      have hd : dist ((q.1, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) p₀
          = dist q.1 x₀ := by
        change max (dist q.1 x₀) (dist (ContinuousLinearMap.id ℝ E)
          (ContinuousLinearMap.id ℝ E)) = dist q.1 x₀
        rw [dist_self, max_eq_left dist_nonneg]
      rw [hd]
      exact lt_of_lt_of_le hq_x hρ_le
    · rcases hq_t with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  exact contDiffOn_fromAugFlow (k := (1 : ℕ∞)) (Ω := U_a) (U := U) haΦ_C1 hmap

end SmoothnessInheritance

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
