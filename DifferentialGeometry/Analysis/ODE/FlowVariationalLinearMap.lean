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

/-! ## Orbit-equality on a closed interval

Strengthening `orbit_eq_of_augFlow_isLocalFlow`: under the same hypotheses, plus a
uniform Lipschitz bound for `f` on a slab `closedBall x₀ r₀ ⊆ E` that contains both
orbits on the closed interval `Icc (t₀ - T) (t₀ + T)`, the two orbit projections agree
on the entire closed interval (not merely on a neighbourhood of `t₀`).  The proof
specialises `ODE_solution_unique_of_mem_Icc` to the original ODE `y' = f t y` with
the uniform Lipschitz constant supplied on the slab. -/

section OrbitEqualityIcc

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

/-- **Orbit-equality on a closed interval.**  If both orbits land in a closed ball
`closedBall x₀ r₀` on which `f t` is uniformly `K`-Lipschitz for `t` in the open
interval `Ioo (t₀ - T) (t₀ + T)`, then `Φ ⟨x, ·⟩` and `(aΦ ⟨(x, id), ·⟩).1` agree on
the entire closed interval `Icc (t₀ - T) (t₀ + T)`.  The hypotheses package the
orbit-stays-in-the-ball condition for each side and the uniform Lipschitz property of
`f` on the slab. -/
theorem orbit_eq_Icc_of_augFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    {T : ℝ} (hT_sub_Φ : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hT_sub_a : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin_a tmax_a)
    (ht₀_Ioo : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
    {r₀ : ℝ} {K : ℝ≥0}
    (h_Φ_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T), Φ ⟨x, t⟩ ∈ closedBall x₀ r₀)
    (h_a_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 ∈ closedBall x₀ r₀)
    (h_lip : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      LipschitzOnWith K (f t) (closedBall x₀ r₀)) :
    EqOn (fun s => Φ ⟨x, s⟩)
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
      (Icc (t₀ - T) (t₀ + T)) := by
  -- Both orbits satisfy the original ODE.
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_init : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_init : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  have hα_Φ_cont : ContinuousOn α_Φ (Icc (t₀ - T) (t₀ + T)) :=
    (hΦ.orbit_continuousOn x hx_Φ).mono hT_sub_Φ
  have hα_a_cont : ContinuousOn α_a (Icc (t₀ - T) (t₀ + T)) := by
    have h_pair_cont : ContinuousOn
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (Icc tmin_a tmax_a) :=
      haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
    have h_fst_cont : ContinuousOn α_a (Icc tmin_a tmax_a) :=
      continuous_fst.continuousOn.comp h_pair_cont (fun _ _ => mem_univ _)
    exact h_fst_cont.mono hT_sub_a
  -- Derivative at every interior point.
  have hα_Φ_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_Φ (f s (α_Φ s)) s := by
    intro s hs
    have h_in_Icc_Φ : s ∈ Icc tmin tmax := hT_sub_Φ (Ioo_subset_Icc_self hs)
    have h_dw : HasDerivWithinAt (fun u => Φ ⟨x, u⟩) (f s (Φ ⟨x, s⟩))
        (Icc tmin tmax) s := hΦ.hasDerivWithinAt x hx_Φ s h_in_Icc_Φ
    -- Promote to HasDerivAt using the fact that s ∈ Ioo (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax.
    -- The latter set is in 𝓝 s because Ioo (t₀ - T) (t₀ + T) is open and contained in it.
    have h_nhds : Icc tmin tmax ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_Φ (Ioo_subset_Icc_self hu))
    exact h_dw.hasDerivAt h_nhds
  have hα_a_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_a (f s (α_a s)) s := by
    intro s hs
    have h_in_Icc_a : s ∈ Icc tmin_a tmax_a := hT_sub_a (Ioo_subset_Icc_self hs)
    have h_orbit_dw : HasDerivWithinAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        (Icc tmin_a tmax_a) s :=
      haΦ.hasDerivWithinAt _ hx_a s h_in_Icc_a
    have h_nhds : Icc tmin_a tmax_a ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_a (Ioo_subset_Icc_self hu))
    have h_orbit_at : HasDerivAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)) s :=
      h_orbit_dw.hasDerivAt h_nhds
    -- Project to first component.
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))) s :=
      h_fst_fd.comp_hasDerivAt s h_orbit_at
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augVF f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        = f s (α_a s) := rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  -- Initial value agreement.
  have h_init_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_init, hα_a_init]
  -- Apply ODE uniqueness on the closed interval.
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t y => f t y)
    (s := fun _ => closedBall x₀ r₀)
    (K := K)
    (fun t ht => h_lip t ht)
    ht₀_Ioo hα_Φ_cont
    (fun t ht => hα_Φ_deriv t ht)
    (fun t ht => h_Φ_in t ht)
    hα_a_cont
    (fun t ht => hα_a_deriv t ht)
    (fun t ht => h_a_in t ht)
    h_init_eq

end OrbitEqualityIcc

/-! ## Smoothness-clause witness of the level-1 variational-flow projection

The construction: build the augmented flow `aΦ` on `E × (E →L[ℝ] E)` via
`exists_isLocalFlow_augVF_of_C2`, apply `contDiffOn_flow_of_isLocalFlow_of_contDiff`
to `aΦ` to get joint `C^1`-smoothness of `aΦ` on an open neighbourhood (using closed-ball
compactness in finite dimensions to extract the uniform operator-norm bound on the
augmented linearization), and inherit this smoothness to the projection
`Y := fromAugFlow aΦ` via `contDiffOn_fromAugFlow_inherits`.

This produces the **smoothness clause** of the `IsVariationalFlowProjection hΦ T ρ Y 1`
witness, namely `ContDiffOn ℝ 1 Y ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T))`, together
with positive `T` and `ρ`.  The remaining `fderiv_eq` clause requires
`Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax` (so that the orbit `Φ ⟨x, ·⟩` is differentiable
on the slab), which in turn requires `t₀ ∈ Ioo tmin tmax` for positivity of `T`.  In
the natural usage downstream, `Φ` is constructed via `exists_isLocalFlow_of_contDiffOn_univ`
which always yields a positive interior; the headline below produces a positive
witness `(T, ρ, Y)` regardless, with the augmented-flow's positive `ε_aug` driving
the inner time width. -/

section LevelOneSmoothnessClause

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}

set_option maxHeartbeats 4000000 in
/-- **Smoothness clause of the level-1 variational-flow projection witness.**

If `f : ℝ → E → E` is jointly `C^2` on `Set.univ` and `E` is a finite-dimensional
Banach space, then there exist positive `T` and `ρ` together with a function
`Y : E × ℝ → (E →L[ℝ] E)` that is jointly `C^1` on the open neighbourhood
`(ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)`.

The function `Y` is `fromAugFlow aΦ` where `aΦ` is the local flow of the augmented
vector field `augVF f` on `E × (E →L[ℝ] E)` centred at `((x₀, id), t₀)`.

This headline is the **smoothness clause** of the full level-1
`IsVariationalFlowProjection` witness; the remaining `fderiv_eq` clause is shipped
separately and requires the orbit-equality identification on a closed time interval
(see `orbit_eq_Icc_of_augFlow_isLocalFlow`). -/
theorem exists_contDiffOn_fromAugFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      ContDiffOn ℝ 1 (fromAugFlow aΦ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Step 1: get the augmented flow.
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
    exists_isLocalFlow_augVF_of_C2 hf_C2 t₀ p₀
  -- Step 2: extract the C^1 regularity of `augVF f`.
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  -- Step 3: pick the outer slab for compactness-based M extraction.
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  set T_a_out : ℝ := ε_aug / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by rw [hT_a_out_def]; linarith
  have hT_a_out_lt : T_a_out < ε_aug := by rw [hT_a_out_def]; linarith
  have hslab_sub_a : closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug) := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact Icc_subset_Icc (by linarith) (by linarith)
  -- Step 4: extract M_aug via finite-dim compactness + continuity.
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    contDiffOn_partial_fderiv_of_succ (f := augVF f) (k := (0 : ℕ∞))
      (by simpa using h_augVF_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augVF f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug)) :=
    haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ
      (closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)) :=
    haΦ_cont_full.mono hslab_sub_a
  set Slab : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out) with hSlab_def
  have hSlab_cpt : IsCompact Slab :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_ne : Slab.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have h_aΦ_pair_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_along_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augVF f q.2) (aΦ q))
      Slab := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_aΦ_pair_cont hmaps
  have h_norm_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augVF f q.2) (aΦ q)‖)
      Slab :=
    continuous_norm.comp_continuousOn h_fderiv_along_cont
  rcases hSlab_cpt.exists_isMaxOn hSlab_ne h_norm_cont with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augVF f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := norm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab, ‖fderiv ℝ (augVF f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  -- Step 5: pick nested params for the augmented system.
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  -- Pick T_a_mid' strictly less than T_a_out with `M_aug * T_a_mid' < 1`.
  set T_a_mid' : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid'_def
  have hT_a_mid'_pos : 0 < T_a_mid' := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid'_lt_out : T_a_mid' < T_a_out := by
    have h1 : T_a_mid' ≤ T_a_out * 3 / 4 := min_le_left _ _
    have h2 : T_a_out * 3 / 4 < T_a_out := by linarith
    linarith
  have hMTmid' : M_aug * T_a_mid' < 1 := by
    have h1 : T_a_mid' ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid' ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  set T_a : ℝ := T_a_mid' / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by rw [hT_a_def]; linarith
  have hT_a_lt_mid' : T_a < T_a_mid' := by rw [hT_a_def]; linarith
  -- Spatial nesting: R_a < R_a_mid < R_a_out.
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := R_a_mid / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by rw [hR_a_def]; linarith
  have hR_a_lt_mid : R_a < R_a_mid := by rw [hR_a_def]; linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩ with hR_aN_def
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩ with hR_a_midN_def
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩ with hR_a_outN_def
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩ with hr'a_def
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    rw [hr'a_def]
    change 0 < (R_aug : ℝ) / 8
    linarith
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    have : (r'a : ℝ) = (R_aug : ℝ) / 8 := rfl
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  -- Convert bound on Slab into the form needed.
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab := ⟨hp, hτ⟩
    have h_pre : ‖fderiv ℝ (augVF f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre :=
      hM_aug_pre_bd _ hq_in
    linarith
  have hsub_a : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc (t₀ - ε_aug) (t₀ + ε_aug) :=
    Icc_subset_Icc (by linarith) (by linarith)
  -- Apply V.2.c.2 to `aΦ` for the augmented system to get joint C^1.
  have h_aug_C1 : ContDiffOn ℝ 1 aΦ ((ball p₀ (R_aN : ℝ))
      ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have hk_aug : (1 : ℕ∞) ≤ 1 := le_refl _
    refine contDiffOn_flow_of_isLocalFlow_of_contDiff (f := augVF f)
      (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug)
      (Φ := aΦ) haΦ hk_aug h_augVF_C1 hT_a_pos hT_a_lt_mid' hT_a_mid'_lt_out
      hM_aug_nn hMTmid' hsub_a (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN)
      hr'a_pos
      ?_ ?_ ?_ ?_ hA_bd_a
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith [hR_a_lt_mid]
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith [hR_a_mid_lt_out]
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
  -- Step 6: inherit C^1 smoothness to the projection.
  -- Pick T and ρ strictly less than (T_a, R_a) so that ball x₀ ρ × Ioo (t₀ - T) (t₀ + T)
  -- maps into ball p₀ R_a × Ioo (t₀ - T_a) (t₀ + T_a) via the (x, t) ↦ ((x, id), t) embedding.
  set T : ℝ := T_a / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_le_T_a : T ≤ T_a := by rw [hT_def]; linarith
  set ρ : ℝ := R_a / 2 with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
  have hρ_le_R_a : ρ ≤ R_a := by rw [hρ_def]; linarith
  set ρN : ℝ≥0 := ⟨ρ, le_of_lt hρ_pos⟩ with hρN_def
  have hρN_eq : (ρN : ℝ) = ρ := rfl
  have hρN_le_R_aN : (ρN : ℝ) ≤ (R_aN : ℝ) := by rw [hρN_eq, hR_aN_eq]; exact hρ_le_R_a
  -- Apply smoothness inheritance.
  refine ⟨T, ρN, hT_pos, hρ_pos, aΦ, ?_⟩
  refine contDiffOn_fromAugFlow_inherits (ρ_a := R_aN) (ρ := ρN) (T_a := T_a) (T := T)
    hρN_le_R_aN hT_le_T_a h_aug_C1

end LevelOneSmoothnessClause

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
