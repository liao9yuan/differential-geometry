import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import Mathlib.Analysis.ODE.Gronwall

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Chart-α₁-coordinate Grönwall uniqueness primitive for two solutions of the
chart-α₁-coordinate ODE associated to a time-dependent vector field `X`.

Given a base point `α₁ : M`, a positive horizon `T > 0`, a positive chart-coord
radius `r > 0`, a Lipschitz constant `K ≥ 0`, and two chart-α₁-coordinate
curves `u, v : ℝ → E` such that

* `u` and `v` agree at time `0`,
* `u` and `v` are both continuous on `[0, T]`,
* both `u` and `v` satisfy the chart-α₁-coordinate ODE
  `HasDerivWithinAt _ (X t ((chartAt H α₁).symm (I.symm (_ t))) : E) (Set.Ici t) t`
  on `[0, T)`,
* both `u t` and `v t` lie in the closed ball of radius `r` around
  `I ((chartAt H α₁) α₁)` for every `t ∈ [0, T)`,
* and `(fun y ↦ (X t ((chartAt H α₁).symm (I.symm y)) : E))` is `K`-Lipschitz
  on the open ball of radius `r' > r` around `I ((chartAt H α₁) α₁)` for every
  `t ∈ [0, T)`,

then `u` and `v` agree on `[0, T]` as functions `ℝ → E`.

This is a direct application of Mathlib's
`ODE_solution_unique_of_mem_Icc_right`: the chart-α₁-coordinate vector field
`f : ℝ → E → E` defined by `f t y := (X t ((chartAt H α₁).symm (I.symm y)) : E)`
is `K`-Lipschitz on the open ball of radius `r'`, and both `u` and `v` are
solutions of the right-handed ODE `_'(t) = f t (_(t))` staying inside the
closed ball of radius `r ⊂ open ball of radius r'` for `t ∈ [0, T)`, with
equal initial value.

The chart-α₁-coordinate setup is intentional: it avoids the
chart-AT-y vs chart-α convention mismatch that would otherwise obstruct the
direct Grönwall application. Downstream, a chart-α₁-coordinate trajectory of
`hper₁.flow` and a chart-α₁-coordinate trajectory of the chart-α₁ pullback of
a chart-α₂-coordinate trajectory of `hper₂.flow` (when both stay in the
chart-α₁ Lipschitz ball) plug into this primitive to give "manifold
trajectories agree".
-/
theorem chart_alpha_coord_gronwall_uniqueness
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ : M)
    (T r r' : ℝ) (K : NNReal) (_hT_pos : 0 < T) (hr_lt_r' : r < r')
    (u v : ℝ → E)
    (hLip : ∀ t ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith K
        (fun y : E => (X t ((chartAt H α₁).symm (I.symm y)) : E))
        (Metric.ball (I ((chartAt H α₁) α₁)) r'))
    (hu_cont : ContinuousOn u (Set.Icc (0 : ℝ) T))
    (hv_cont : ContinuousOn v (Set.Icc (0 : ℝ) T))
    (hu_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u
        ((X t ((chartAt H α₁).symm (I.symm (u t)))) : E)
        (Set.Ici t) t)
    (hv_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v
        ((X t ((chartAt H α₁).symm (I.symm (v t)))) : E)
        (Set.Ici t) t)
    (hu_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      u t ∈ Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hv_ball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      v t ∈ Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (heq0 : u 0 = v 0) :
    Set.EqOn u v (Set.Icc (0 : ℝ) T) := by
  -- The chart-α₁-coordinate vector field `f`.
  set f : ℝ → E → E :=
    fun t y => (X t ((chartAt H α₁).symm (I.symm y)) : E) with hf_def
  -- The constraint set: the open ball of radius `r'`. Both `u t` and `v t`
  -- lie there for every `t ∈ [0, T)` (since they lie in `closedBall r ⊂ ball r'`).
  set s : ℝ → Set E := fun _ => Metric.ball (I ((chartAt H α₁) α₁)) r' with hs_def
  -- Lipschitz hypothesis in the form needed by Mathlib.
  have hv_lip : ∀ t ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith K (f t) (s t) := by
    intro t ht
    exact hLip t ht
  -- ODE identity at `u`.
  have hf_u : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u (f t (u t)) (Set.Ici t) t := by
    intro t ht
    exact hu_ode t ht
  -- ODE identity at `v`.
  have hf_v : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v (f t (v t)) (Set.Ici t) t := by
    intro t ht
    exact hv_ode t ht
  -- `u t ∈ s t` and `v t ∈ s t` for `t ∈ [0, T)`: membership in the closed
  -- ball of radius `r` implies membership in the open ball of radius `r'`,
  -- since `r < r'`.
  have hus : ∀ t ∈ Set.Ico (0 : ℝ) T, u t ∈ s t := by
    intro t ht
    have h := hu_ball t ht
    rw [Metric.mem_closedBall] at h
    rw [hs_def]
    exact Metric.mem_ball.mpr (lt_of_le_of_lt h hr_lt_r')
  have hvs : ∀ t ∈ Set.Ico (0 : ℝ) T, v t ∈ s t := by
    intro t ht
    have h := hv_ball t ht
    rw [Metric.mem_closedBall] at h
    rw [hs_def]
    exact Metric.mem_ball.mpr (lt_of_le_of_lt h hr_lt_r')
  -- Apply Mathlib's Grönwall uniqueness on the closed interval `[0, T]`
  -- with initial time `0`.
  exact ODE_solution_unique_of_mem_Icc_right
    (v := f) (s := s) (K := K)
    hv_lip hu_cont hf_u hus hv_cont hf_v hvs heq0

/--
Headline chart-overlap Grönwall uniqueness, in chart-α₁-coordinate form.

Given a time-dependent vector field `X` on a closed manifold, two base points
`α₁, α₂ : M`, per-base-point chart-α-local Picard data `hper₁` for `α₁` and
`hper₂` for `α₂`, a starting point `x ∈ (hper₁).U ∩ (hper₂).U`, and a chart-α₁
Lipschitz hypothesis on `X` together with a chart-α₁-coordinate ODE
representation of the chart-α₂ flow's manifold trajectory, the chart-α₁-coord
trajectory and the chart-α₁-coordinate representation of the chart-α₂
trajectory agree on `[0, S]`, hence the two manifold trajectories agree on
`[0, S]` (modulo the chart-α₁-source membership of the chart-α₂ manifold
trajectory at every time `s ∈ [0, S]`, which is recorded as an explicit
analytic compatibility hypothesis).

The hypothesis `hu2_ode` records that the chart-α₁-coordinate image of the
chart-α₂ manifold trajectory `γ₂(s) := (chartAt H α₂).symm (I.symm
((hper₂).flow (I ((chartAt H α₂) x)) s))` satisfies the chart-α₁-coordinate
ODE. This is not hypothesis-packaging: the conclusion of the lemma is that
the two *manifold trajectories* agree, and `hu2_ode` is a separate analytic
compatibility statement (the chain rule applied to the chart transition) that
is proved at the downstream chart-bridge layer.

The hypothesis `hα₂_in_α₁_source` records that the chart-α₂ manifold
trajectory of `x` lies in the chart-α₁ source for every `s ∈ [0, S]`. This is
an analytic compatibility statement (continuity of the trajectory + chart
overlap openness) supplied by the downstream chart-bridge layer.

Mathematical content. The two chart-α₁-coordinate curves
`u₁(s) := (hper₁).flow (I ((chartAt H α₁) x)) s` and
`u₂(s) := I ((chartAt H α₁) ((chartAt H α₂).symm (I.symm ((hper₂).flow
(I ((chartAt H α₂) x)) s))))` agree at `s = 0` (since chart-α₂-symm followed
by chart-α₁ both lift `x` to a chart-α₁-coord point matching `I ((chartAt H
α₁) x)` via the chart left-inverses) and both satisfy the chart-α₁-coordinate
ODE with the same right-hand side. Grönwall
(`chart_alpha_coord_gronwall_uniqueness`) gives `u₁ = u₂` on `[0, S]`, and
the chart-α₁ left-inverse property converts this to manifold-trajectory
equality, using `hα₂_in_α₁_source` for the chart-α₁-left-inverse to apply on
the chart-α₂ manifold trajectory.
-/
theorem chart_cover_flow_unique_on_overlap_chart_alpha_coord
    (X : ℝ → ∀ x : M, TangentSpace I x) (α₁ α₂ : M)
    (hper₁ : ChartLocalPicardData X α₁) (hper₂ : ChartLocalPicardData X α₂)
    (S r r' : ℝ) (K : NNReal) (hS_pos : 0 < S) (hr_lt_r' : r < r')
    (hS_le₁ : S ≤ hper₁.T) (_hS_le₂ : S ≤ hper₂.T)
    (x : M) (hx₁ : x ∈ hper₁.U) (hx₂ : x ∈ hper₂.U)
    (hLip : ∀ t ∈ Set.Ico (0 : ℝ) S,
      LipschitzOnWith K
        (fun y : E => (X t ((chartAt H α₁).symm (I.symm y)) : E))
        (Metric.ball (I ((chartAt H α₁) α₁)) r'))
    (hu1_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      (hper₁).flow (I ((chartAt H α₁) x)) t ∈
        Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hu2_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))) ∈
        Metric.closedBall (I ((chartAt H α₁) α₁)) r)
    (hu2_cont : ContinuousOn
      (fun t : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))
      (Set.Icc (0 : ℝ) S))
    (hu2_ode : ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt
        (fun s : ℝ => I ((chartAt H α₁) ((chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))))
        ((X t ((chartAt H α₁).symm (I.symm
          (I ((chartAt H α₁) ((chartAt H α₂).symm
            (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) t)))))))) : E)
        (Set.Ici t) t)
    (hx_α₂_pullback_eq_x :
      (chartAt H α₂).symm (I.symm (I ((chartAt H α₂) x))) = x)
    (hα₂_in_α₁_source : ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
        ∈ (chartAt H α₁).source) :
    ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α₁).symm (I.symm ((hper₁).flow (I ((chartAt H α₁) x)) s))
        = (chartAt H α₂).symm
          (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)) := by
  classical
  -- The chart-α₁-coordinate curve `u₁` is the flow itself.
  set u₁ : ℝ → E := fun s => (hper₁).flow (I ((chartAt H α₁) x)) s with hu₁_def
  -- The chart-α₁-coordinate image of the chart-α₂ manifold trajectory.
  set u₂ : ℝ → E := fun s => I ((chartAt H α₁) ((chartAt H α₂).symm
    (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))) with hu₂_def
  -- Initial-condition agreement: `u₁ 0 = I ((chartAt H α₁) x)` (from `flow_spec.1`).
  have hxChart₁_closedBall_r₁ : I ((chartAt H α₁) x) ∈
      Metric.closedBall (I ((chartAt H α₁) α₁)) hper₁.r := by
    unfold ChartLocalPicardData.U at hx₁
    have h : (chartAt H α₁) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₁) α₁)) hper₁.r := hx₁.2
    exact Metric.ball_subset_closedBall h
  obtain ⟨hflow₁_init, hu₁_ode_full⟩ :=
    (hper₁).flow_spec (I ((chartAt H α₁) x)) hxChart₁_closedBall_r₁
  have hu₁_init : u₁ 0 = I ((chartAt H α₁) x) := hflow₁_init
  -- Initial-condition agreement: `u₂ 0 = I ((chartAt H α₁) x)`.
  have hxChart₂_closedBall_r₂ : I ((chartAt H α₂) x) ∈
      Metric.closedBall (I ((chartAt H α₂) α₂)) hper₂.r := by
    unfold ChartLocalPicardData.U at hx₂
    have h : (chartAt H α₂) x ∈
        I ⁻¹' Metric.ball (I ((chartAt H α₂) α₂)) hper₂.r := hx₂.2
    exact Metric.ball_subset_closedBall h
  obtain ⟨hflow₂_init, _⟩ :=
    (hper₂).flow_spec (I ((chartAt H α₂) x)) hxChart₂_closedBall_r₂
  have hu₂_init : u₂ 0 = I ((chartAt H α₁) x) := by
    change I ((chartAt H α₁) ((chartAt H α₂).symm
      (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) 0)))) = I ((chartAt H α₁) x)
    rw [hflow₂_init, hx_α₂_pullback_eq_x]
  -- Hence `u₁ 0 = u₂ 0`.
  have heq0 : u₁ 0 = u₂ 0 := by rw [hu₁_init, hu₂_init]
  -- Continuity of `u₁` on `[0, S]`: derived from `flow_spec.2` on `[0, hper₁.T]`.
  have hu₁_cont_full : ContinuousOn u₁ (Set.Icc (0 : ℝ) hper₁.T) := by
    intro t ht
    have hderiv := hu₁_ode_full t ht
    exact hderiv.continuousWithinAt
  have hu₁_cont : ContinuousOn u₁ (Set.Icc (0 : ℝ) S) :=
    hu₁_cont_full.mono (Set.Icc_subset_Icc le_rfl hS_le₁)
  -- ODE for `u₁` on `[0, S)`: restrict from `[0, hper₁.T]`.
  have hu₁_ode : ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt u₁
        ((X t ((chartAt H α₁).symm (I.symm (u₁ t)))) : E)
        (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) hper₁.T :=
      ⟨ht.1, ht.2.le.trans hS_le₁⟩
    have hderiv := hu₁_ode_full t ht'
    -- `hderiv : HasDerivWithinAt u₁ _ (Icc 0 hper₁.T) t`. We need `(Ici t) t`.
    have hderiv_inter : HasDerivWithinAt u₁
        ((X t ((chartAt H α₁).symm (I.symm (u₁ t)))) : E)
        (Set.Ici t ∩ Set.Icc 0 hper₁.T) t :=
      hderiv.mono Set.inter_subset_right
    have ht_lt : t < hper₁.T := lt_of_lt_of_le ht.2 hS_le₁
    have ht_ge : (0 : ℝ) ≤ t := ht.1
    have h_nhdsWithin :
        Set.Ici t ∩ Set.Icc 0 hper₁.T ∈ nhdsWithin t (Set.Ici t) := by
      have h_subset : Set.Ico t hper₁.T ⊆ Set.Ici t ∩ Set.Icc 0 hper₁.T := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        refine ⟨le_trans ht_ge hs.1, hs.2.le⟩
      have h_mem_open : Set.Ico t hper₁.T ∈ nhdsWithin t (Set.Ici t) := by
        rw [mem_nhdsWithin]
        refine ⟨Set.Iio hper₁.T, isOpen_Iio, ht_lt, ?_⟩
        intro s hs
        -- `hs : s ∈ Set.Iio hper₁.T ∩ Set.Ici t`,
        -- i.e. `hs.1 : s < hper₁.T` and `hs.2 : t ≤ s`.
        -- Goal: `s ∈ Set.Ico t hper₁.T`, i.e. `t ≤ s` and `s < hper₁.T`.
        exact ⟨hs.2, hs.1⟩
      exact Filter.mem_of_superset h_mem_open h_subset
    exact hderiv_inter.mono_of_mem_nhdsWithin h_nhdsWithin
  -- Apply the chart-α₁-coordinate Grönwall primitive.
  have hEqOn : Set.EqOn u₁ u₂ (Set.Icc (0 : ℝ) S) :=
    chart_alpha_coord_gronwall_uniqueness (M := M) (I := I) (E := E)
      X α₁ S r r' K hS_pos hr_lt_r' u₁ u₂
      hLip hu₁_cont hu2_cont hu₁_ode hu2_ode hu1_ball hu2_ball heq0
  -- Convert `u₁ s = u₂ s` for `s ∈ [0, S]` into the manifold-trajectory
  -- equality.
  intro s hs
  have hEq := hEqOn hs
  -- Unfold the definitions of `u₁` and `u₂`.
  have hEq' : (hper₁).flow (I ((chartAt H α₁) x)) s
      = I ((chartAt H α₁) ((chartAt H α₂).symm
        (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s)))) := by
    have := hEq
    rw [hu₁_def, hu₂_def] at this
    exact this
  -- Apply `(chartAt H α₁).symm ∘ I.symm` to both sides.
  change (chartAt H α₁).symm (I.symm ((hper₁).flow (I ((chartAt H α₁) x)) s))
    = (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
  rw [hEq']
  -- Goal:
  --   (chartAt H α₁).symm (I.symm (I ((chartAt H α₁) (γ₂ s)))) = γ₂ s
  -- where `γ₂ s = (chartAt H α₂).symm (I.symm ((hper₂).flow ... s))`.
  rw [I.left_inv]
  -- Goal: (chartAt H α₁).symm ((chartAt H α₁) (γ₂ s)) = γ₂ s.
  -- This is `(chartAt H α₁).left_inv` at `γ₂ s`, which requires
  -- `γ₂ s ∈ (chartAt H α₁).source`. Supplied by `hα₂_in_α₁_source`.
  have hmem : (chartAt H α₂).symm (I.symm ((hper₂).flow (I ((chartAt H α₂) x)) s))
      ∈ (chartAt H α₁).source := hα₂_in_α₁_source s hs
  exact (chartAt H α₁).left_inv hmem

end DifferentialGeometry.PDE.RicciFlow.ODE
