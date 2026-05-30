import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

/-!
# Forward (one-sided) uniqueness of integral curves

Mathlib's manifold integral-curve uniqueness
(`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`) is stated on a **two-sided** open
interval `Ioo a b` with agreement at an interior time.  A *forward* flow — one that solves its
ODE only for times `> 0`, starting from a fixed value at time `0` (the diffeomorphism family
`Φ_fam` of the Hamilton–DeTurck construction is exactly such a flow: `Φ_fam 0 = id`, and the
bare flow equation holds only on `(0, T)`) — cannot be plugged into the two-sided theorem with
agreement time `0`, because the ODE is not available on a two-sided neighbourhood of `0`.

This file develops the missing **forward** uniqueness on a closed interval `Icc a b`, with
agreement at the *left* endpoint `a`, by reading both curves into the local chart at their
common value `γ a` and invoking the Euclidean forward Grönwall uniqueness
`ODE_solution_unique_of_mem_Icc_right` (genuinely one-sided: `HasDerivWithinAt … (Ici t)` and
agreement at the initial time `a`).

* `isMIntegralCurveOn_forward_eqOn_Icc_of_contMDiffAt` — forward local uniqueness on a short
  closed interval `Icc t₁ (t₁ + δ)` with agreement at the left endpoint `t₁`, via the chart
  reading and `ODE_solution_unique_of_mem_Icc_right`.
* `isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff` — forward uniqueness on `Icc a b` for an
  autonomous `C¹` field, agreement at the left endpoint, on a boundaryless manifold (a sup /
  least-counterexample globalisation of the local result).
* `bare_forward_flow_eqOn_of_jointC1` — the manifold-level forward uniqueness for the **bare**
  time-dependent flow, obtained by lifting both curves to the autonomous field
  `autonomizedFlowVF X` on `ℝ × M`.  The forward analogue of `bare_integral_flow_eqOn_of_jointC1`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Manifold Bundle Filter
open scoped Manifold Topology ContDiff

section ForwardUniqueness

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
variable {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN 1 N]
  [T2Space N]

/-- **Forward local integral-curve uniqueness on a closed interval, agreement at the left
endpoint.**

If `v` is a `C¹` autonomous vector field at the point `γ t₁` (an interior point of the
boundaryless manifold `N`), and `γ`, `γ'` are integral curves of `v` on `Icc t₁ b` agreeing at
the left endpoint `t₁`, then there is a positive `δ` (with `t₁ + δ ≤ b`) such that `γ` and `γ'`
agree on `Icc t₁ (t₁ + δ)`.

The proof reads both curves into the local chart at the common value `γ t₁`, where they become
Euclidean solutions of the chart-pushforward field `v'` with `HasDerivWithinAt … (Ici t)`, both
confined to a fixed ball on which `v'` is Lipschitz, agreeing at `t₁`; the one-sided Euclidean
Grönwall uniqueness `ODE_solution_unique_of_mem_Icc_right` then forces chart-coordinate agreement,
which pulls back to manifold agreement. -/
theorem isMIntegralCurveOn_forward_eqOn_Icc_of_contMDiffAt [BoundarylessManifold IN N]
    {v : (x : N) → TangentSpace IN x} {γ γ' : ℝ → N} {t₁ b : ℝ} (ht₁b : t₁ < b)
    (hv : ContMDiffAt IN IN.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle IN N)) (γ t₁))
    (hγ : IsMIntegralCurveOn γ v (Icc t₁ b))
    (hγ' : IsMIntegralCurveOn γ' v (Icc t₁ b))
    (h : γ t₁ = γ' t₁) :
    ∃ δ : ℝ, 0 < δ ∧ t₁ + δ ≤ b ∧ EqOn γ γ' (Icc t₁ (t₁ + δ)) := by
  -- The chart-pushforward field `v'` at the common base point `p₀ := γ t₁`.
  set p₀ : N := γ t₁ with hp₀
  set v' : EN → EN := fun x ↦
    tangentCoordChange IN ((extChartAt IN p₀).symm x) p₀ ((extChartAt IN p₀).symm x)
      (v ((extChartAt IN p₀).symm x)) with hv'
  -- `p₀` is an interior point (boundaryless), so `v'` is `C¹` near the chart image of `p₀`.
  have hint : IN.IsInteriorPoint p₀ := BoundarylessManifold.isInteriorPoint
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv2⟩ := hv
  obtain ⟨K, sLip, hsLip, hlip⟩ : ∃ K, ∃ sLip ∈ 𝓝 _, LipschitzOnWith K v' sLip :=
    (hv2.contDiffAt (range_mem_nhds_isInteriorPoint hint)).snd.exists_lipschitzOnWith
  -- A ball around the chart image of `p₀` inside the Lipschitz set.
  obtain ⟨ρ, hρ, hρ_sub⟩ := Metric.mem_nhds_iff.mp hsLip
  set z₀ : EN := extChartAt IN p₀ p₀ with hz₀
  -- The chart source is a neighbourhood of `p₀`; the curves are continuous, so they stay in it.
  have hsrc_nhds : (extChartAt IN p₀).source ∈ 𝓝 p₀ := extChartAt_source_mem_nhds p₀
  -- Continuity of `γ`, `γ'` within `Icc t₁ b` at `t₁`.
  have hγcont : ContinuousWithinAt γ (Icc t₁ b) t₁ :=
    hγ.continuousWithinAt ⟨le_refl _, le_of_lt ht₁b⟩
  have hγ'cont : ContinuousWithinAt γ' (Icc t₁ b) t₁ :=
    hγ'.continuousWithinAt ⟨le_refl _, le_of_lt ht₁b⟩
  -- Choose `δ₀ > 0` so that on `Icc t₁ (t₁+δ₀)` both curves stay in the chart source AND their
  -- chart images stay in `ball z₀ ρ`.
  -- Set `O := (extChartAt IN p₀).source ∩ extChartAt IN p₀ ⁻¹' (ball z₀ ρ)` (open nbhd of `p₀`).
  set O : Set N := (extChartAt IN p₀).source ∩ (extChartAt IN p₀) ⁻¹' (Metric.ball z₀ ρ) with hO
  have hO_nhds : O ∈ 𝓝 p₀ := by
    refine Filter.inter_mem hsrc_nhds ?_
    refine (continuousAt_extChartAt p₀).preimage_mem_nhds ?_
    rw [← hz₀]; exact Metric.ball_mem_nhds z₀ hρ
  -- Preimage of `O` under `γ` is a within-`Icc`-neighbourhood of `t₁`.
  have hpre_γ : γ ⁻¹' O ∈ 𝓝[Icc t₁ b] t₁ := hγcont.preimage_mem_nhdsWithin hO_nhds
  have hpre_γ' : γ' ⁻¹' O ∈ 𝓝[Icc t₁ b] t₁ := by
    have : γ' t₁ ∈ O := by rw [← h]; exact mem_of_mem_nhds hO_nhds
    exact hγ'cont.preimage_mem_nhdsWithin (h ▸ hO_nhds)
  -- Extract `δ₀ > 0` with `Icc t₁ (t₁+δ₀) ⊆ γ⁻¹' O ∩ γ'⁻¹' O ∩ Icc t₁ b`.
  have hboth : γ ⁻¹' O ∩ γ' ⁻¹' O ∈ 𝓝[Icc t₁ b] t₁ := Filter.inter_mem hpre_γ hpre_γ'
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hboth
  obtain ⟨W, hW_nhds, hW_sub⟩ := hboth
  rw [Metric.mem_nhds_iff] at hW_nhds
  obtain ⟨ε, hε, hε_sub⟩ := hW_nhds
  -- `δ := min (ε/2) (b - t₁) > 0`, `t₁ + δ ≤ b`.
  set δ : ℝ := min (ε / 2) (b - t₁) with hδdef
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_le_b : t₁ + δ ≤ b := by
    have : δ ≤ b - t₁ := min_le_right _ _
    linarith
  refine ⟨δ, hδ_pos, hδ_le_b, ?_⟩
  -- On `Icc t₁ (t₁+δ)`, both curves land in `O` (chart source + chart image in `ball z₀ ρ`).
  have hIcc_sub_Icc : Icc t₁ (t₁ + δ) ⊆ Icc t₁ b := fun x hx =>
    ⟨hx.1, le_trans hx.2 hδ_le_b⟩
  have hIcc_in_O : ∀ x ∈ Icc t₁ (t₁ + δ), γ x ∈ O ∧ γ' x ∈ O := by
    intro x hx
    have hxb : x ∈ Icc t₁ b := hIcc_sub_Icc hx
    have hxball : x ∈ Metric.ball t₁ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      refine ⟨by linarith [hx.1], ?_⟩
      have hδle : δ ≤ ε / 2 := min_le_left _ _
      have := hx.2; linarith
    have hxW : x ∈ W := hε_sub hxball
    have := hW_sub ⟨hxW, hxb⟩
    exact ⟨this.1, this.2⟩
  -- Chart images of the two curves.
  set f : ℝ → EN := fun x => extChartAt IN p₀ (γ x) with hf
  set g : ℝ → EN := fun x => extChartAt IN p₀ (γ' x) with hg
  -- Both chart images are continuous on `Icc t₁ (t₁+δ)`.
  have hf_cont : ContinuousOn f (Icc t₁ (t₁ + δ)) := by
    intro x hx
    refine (continuousAt_extChartAt' (I := IN) ?_).comp_continuousWithinAt
      (hγ.continuousWithinAt (hIcc_sub_Icc hx) |>.mono hIcc_sub_Icc)
    exact (hIcc_in_O x hx).1.1
  have hg_cont : ContinuousOn g (Icc t₁ (t₁ + δ)) := by
    intro x hx
    refine (continuousAt_extChartAt' (I := IN) ?_).comp_continuousWithinAt
      (hγ'.continuousWithinAt (hIcc_sub_Icc hx) |>.mono hIcc_sub_Icc)
    exact (hIcc_in_O x hx).2.1
  -- The chart ODE (forward, within `Ici t`) for both, on `Ico t₁ (t₁+δ)`.
  have hf_deriv : ∀ x ∈ Ico t₁ (t₁ + δ), HasDerivWithinAt f (v' (f x)) (Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Icc t₁ (t₁ + δ) := ⟨hx.1, le_of_lt hx.2⟩
    have hxIccb : x ∈ Icc t₁ b := hIcc_sub_Icc hxIcc
    have hsrc : γ x ∈ (extChartAt IN p₀).source := (hIcc_in_O x hxIcc).1.1
    -- Read the manifold integral curve into the chart: `HasDerivWithinAt (chart ∘ γ) … (Icc t₁ b) x`.
    have hread : HasDerivWithinAt ((extChartAt IN p₀) ∘ γ)
        (tangentCoordChange IN (γ x) p₀ (γ x) (v (γ x))) (Icc t₁ b) x :=
      hγ.hasDerivWithinAt (t₀ := t₁) hxIccb hsrc
    -- The velocity is `v' (f x)` after the round-trip `(extChartAt p₀).symm (f x) = γ x`.
    have hround : (extChartAt IN p₀).symm (f x) = γ x := by
      change (extChartAt IN p₀).symm (extChartAt IN p₀ (γ x)) = γ x
      exact (extChartAt IN p₀).left_inv hsrc
    have hvel : tangentCoordChange IN (γ x) p₀ (γ x) (v (γ x)) = v' (f x) := by
      change tangentCoordChange IN (γ x) p₀ (γ x) (v (γ x))
        = tangentCoordChange IN ((extChartAt IN p₀).symm (f x)) p₀
            ((extChartAt IN p₀).symm (f x)) (v ((extChartAt IN p₀).symm (f x)))
      rw [hround]
    rw [hvel] at hread
    -- Upgrade `(Icc t₁ b)` → `(Ici x)`: `Icc t₁ b ⊇ Icc x b ∈ 𝓝[Ici x] x` (since `x < b`).
    have hxb : x < b := lt_of_lt_of_le hx.2 hδ_le_b
    have hmono : HasDerivWithinAt ((extChartAt IN p₀) ∘ γ) (v' (f x)) (Icc x b) x :=
      hread.mono (fun y hy => ⟨le_trans hxIccb.1 hy.1, hy.2⟩)
    have hIcc_in : Icc x b ∈ 𝓝[Ici x] x := Icc_mem_nhdsGE hxb
    exact hmono.mono_of_mem_nhdsWithin hIcc_in
  have hg_deriv : ∀ x ∈ Ico t₁ (t₁ + δ), HasDerivWithinAt g (v' (g x)) (Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Icc t₁ (t₁ + δ) := ⟨hx.1, le_of_lt hx.2⟩
    have hxIccb : x ∈ Icc t₁ b := hIcc_sub_Icc hxIcc
    have hsrc : γ' x ∈ (extChartAt IN p₀).source := (hIcc_in_O x hxIcc).2.1
    have hread : HasDerivWithinAt ((extChartAt IN p₀) ∘ γ')
        (tangentCoordChange IN (γ' x) p₀ (γ' x) (v (γ' x))) (Icc t₁ b) x := by
      have hkey := hγ'.hasDerivWithinAt (t₀ := t₁) hxIccb (h ▸ hsrc)
      rw [← h] at hkey
      exact hkey
    have hround : (extChartAt IN p₀).symm (g x) = γ' x := by
      change (extChartAt IN p₀).symm (extChartAt IN p₀ (γ' x)) = γ' x
      exact (extChartAt IN p₀).left_inv hsrc
    have hvel : tangentCoordChange IN (γ' x) p₀ (γ' x) (v (γ' x)) = v' (g x) := by
      change tangentCoordChange IN (γ' x) p₀ (γ' x) (v (γ' x))
        = tangentCoordChange IN ((extChartAt IN p₀).symm (g x)) p₀
            ((extChartAt IN p₀).symm (g x)) (v ((extChartAt IN p₀).symm (g x)))
      rw [hround]
    rw [hvel] at hread
    have hxb : x < b := lt_of_lt_of_le hx.2 hδ_le_b
    have hmono : HasDerivWithinAt ((extChartAt IN p₀) ∘ γ') (v' (g x)) (Icc x b) x :=
      hread.mono (fun y hy => ⟨le_trans hxIccb.1 hy.1, hy.2⟩)
    have hIcc_in : Icc x b ∈ 𝓝[Ici x] x := Icc_mem_nhdsGE hxb
    exact hmono.mono_of_mem_nhdsWithin hIcc_in
  -- Confinement: both chart images stay in `ball z₀ ρ ⊆ sLip` on `Ico t₁ (t₁+δ)`.
  have hf_mem : ∀ x ∈ Ico t₁ (t₁ + δ), f x ∈ sLip := by
    intro x hx
    have hxIcc : x ∈ Icc t₁ (t₁ + δ) := ⟨hx.1, le_of_lt hx.2⟩
    exact hρ_sub (hIcc_in_O x hxIcc).1.2
  have hg_mem : ∀ x ∈ Ico t₁ (t₁ + δ), g x ∈ sLip := by
    intro x hx
    have hxIcc : x ∈ Icc t₁ (t₁ + δ) := ⟨hx.1, le_of_lt hx.2⟩
    exact hρ_sub (hIcc_in_O x hxIcc).2.2
  -- Agreement at the left endpoint in chart coordinates.
  have hfa : f t₁ = g t₁ := by
    have hγγ' : γ t₁ = γ' t₁ := h
    change extChartAt IN p₀ (γ t₁) = extChartAt IN p₀ (γ' t₁)
    rw [hγγ']
  -- Apply the one-sided Euclidean Grönwall uniqueness.
  have heqOn_chart : EqOn f g (Icc t₁ (t₁ + δ)) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => v') (s := fun _ => sLip) (K := K)
      (fun t _ => hlip) hf_cont hf_deriv hf_mem hg_cont hg_deriv hg_mem hfa
  -- Pull back to manifold agreement.
  intro x hx
  have hfx : f x = g x := heqOn_chart hx
  have hγsrc : γ x ∈ (extChartAt IN p₀).source := (hIcc_in_O x hx).1.1
  have hγ'src : γ' x ∈ (extChartAt IN p₀).source := (hIcc_in_O x hx).2.1
  have : (extChartAt IN p₀).symm (f x) = (extChartAt IN p₀).symm (g x) := by rw [hfx]
  rwa [hf, hg, (extChartAt IN p₀).left_inv hγsrc, (extChartAt IN p₀).left_inv hγ'src] at this

/-- **Forward integral-curve uniqueness on a closed interval, agreement at the left endpoint.**

If a `C¹` autonomous vector field `v` on a boundaryless manifold `N` admits two integral curves
`γ`, `γ'` on `Icc a b` that agree at the left endpoint `a`, then they agree on all of `Icc a b`.

The agreement set `S := {t ∈ Icc a b | γ t = γ' t}` contains `a`; a least-counterexample (sup)
argument together with the forward *local* uniqueness
`isMIntegralCurveOn_forward_eqOn_Icc_of_contMDiffAt` (applied at the supremum of the agreement)
propagates the agreement all the way to `b`. -/
theorem isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff [BoundarylessManifold IN N]
    {v : (x : N) → TangentSpace IN x} {γ γ' : ℝ → N} {a b : ℝ}
    (hv : ContMDiff IN IN.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle IN N)))
    (hγ : IsMIntegralCurveOn γ v (Icc a b))
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b))
    (h : γ a = γ' a) :
    EqOn γ γ' (Icc a b) := by
  rcases le_or_gt a b with hab | hba
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hba)
  -- The agreement set inside `Icc a b`.
  set S : Set ℝ := {t | t ∈ Icc a b ∧ EqOn γ γ' (Icc a t)} with hS
  -- `c := sSup S`.
  have ha_in_S : a ∈ S := ⟨⟨le_refl _, hab⟩, by
    intro x hx
    have : x = a := le_antisymm hx.2 hx.1
    rw [this, h]⟩
  have hS_bdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  have hS_ne : S.Nonempty := ⟨a, ha_in_S⟩
  set c : ℝ := sSup S with hc
  have hc_mem_Icc : c ∈ Icc a b :=
    ⟨le_csSup hS_bdd ha_in_S, csSup_le hS_ne (fun x hx => hx.1.2)⟩
  -- `γ = γ'` on `Icc a c`: for any `t < c` there is `s ∈ S` with `t ≤ s` (by `sSup`), and `EqOn`
  -- on `Icc a s ⊇ Icc a t ∋ t`; the endpoint `c` follows by continuity.
  have heqOn_below : EqOn γ γ' (Ico a c) := by
    intro t ht
    obtain ⟨s, hsS, hts⟩ : ∃ s ∈ S, t ≤ s := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hct : c ≤ t := csSup_le hS_ne (fun x hx => le_of_lt (hcon x hx))
      exact absurd ht.2 (not_lt.mpr hct)
    exact hsS.2 ⟨ht.1, hts⟩
  -- `γ c = γ' c` by continuity (closure argument).
  have hγcont : ContinuousOn γ (Icc a b) := hγ.continuousOn
  have hγ'cont : ContinuousOn γ' (Icc a b) := hγ'.continuousOn
  have hc_eq : γ c = γ' c := by
    rcases eq_or_lt_of_le hc_mem_Icc.1 with hca | hca
    · rw [← hca]; exact h
    · have hac_subset : Ico a c ⊆ Icc a b := fun x hx =>
        ⟨hx.1, le_trans (le_of_lt hx.2) hc_mem_Icc.2⟩
      have hγc : ContinuousWithinAt γ (Icc a b) c := hγcont c hc_mem_Icc
      have hγ'c : ContinuousWithinAt γ' (Icc a b) c := hγ'cont c hc_mem_Icc
      have hclos : c ∈ closure (Ico a c) := by
        rw [closure_Ico (ne_of_lt hca)]; exact ⟨le_of_lt hca, le_refl c⟩
      have hcluster : (𝓝[Ico a c] c).NeBot := by
        rw [mem_closure_iff_clusterPt] at hclos; exact hclos
      have hγ_lim : Tendsto γ (𝓝[Ico a c] c) (𝓝 (γ c)) := (hγc.mono hac_subset).tendsto
      have hγ'_lim : Tendsto γ' (𝓝[Ico a c] c) (𝓝 (γ' c)) := (hγ'c.mono hac_subset).tendsto
      have hγeq_lim : Tendsto γ (𝓝[Ico a c] c) (𝓝 (γ' c)) :=
        hγ'_lim.congr' (heqOn_below.eventuallyEq_of_mem self_mem_nhdsWithin).symm
      exact tendsto_nhds_unique hγ_lim hγeq_lim
  -- So `c ∈ S` (agreement on `Icc a c`).
  have hc_in_S : c ∈ S := by
    refine ⟨hc_mem_Icc, ?_⟩
    intro x hx
    rcases eq_or_lt_of_le hx.2 with hxc | hxc
    · rw [hxc]; exact hc_eq
    · exact heqOn_below ⟨hx.1, hxc⟩
  -- If `c < b`, forward local uniqueness at `c` extends agreement past `c`, contradicting `sSup`.
  rcases eq_or_lt_of_le hc_mem_Icc.2 with hcb | hcb
  · -- `c = b`: agreement on `Icc a b`.
    rw [hcb] at hc_in_S; exact hc_in_S.2
  · exfalso
    -- Forward local uniqueness on `Icc c b` (agreement at `c`).
    have hvc : ContMDiffAt IN IN.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle IN N)) (γ c) := hv.contMDiffAt
    have hγ_cb : IsMIntegralCurveOn γ v (Icc c b) :=
      hγ.mono (fun x hx => ⟨le_trans hc_mem_Icc.1 hx.1, hx.2⟩)
    have hγ'_cb : IsMIntegralCurveOn γ' v (Icc c b) :=
      hγ'.mono (fun x hx => ⟨le_trans hc_mem_Icc.1 hx.1, hx.2⟩)
    obtain ⟨δ, hδ, hδb, heqloc⟩ :=
      isMIntegralCurveOn_forward_eqOn_Icc_of_contMDiffAt hcb hvc hγ_cb hγ'_cb hc_eq
    -- Then `c + δ ∈ S` (agreement on `Icc a (c+δ)`), but `c + δ > c = sSup S`.
    have hcδ_in_S : (c + δ) ∈ S := by
      refine ⟨⟨le_trans hc_mem_Icc.1 (by linarith), hδb⟩, ?_⟩
      intro x hx
      rcases le_or_gt x c with hxc | hxc
      · exact hc_in_S.2 ⟨hx.1, hxc⟩
      · exact heqloc ⟨le_of_lt hxc, hx.2⟩
    have : c + δ ≤ c := le_csSup hS_bdd hcδ_in_S
    linarith

end ForwardUniqueness

/-! ### Forward uniqueness for the bare time-dependent flow -/

section BareForward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

/-- **Forward uniqueness of the bare integral flow.**

The forward analogue of `bare_integral_flow_eqOn_of_jointC1`.  Suppose two curves `s ↦ Φ s x`
and `s ↦ Φ' s x'` both satisfy the bare flow equation of `X` on `Icc a b` (in the
`HasMFDerivWithinAt … (Icc a b)` form), agree at the *left endpoint* `a`, and the autonomised
field is jointly `C¹`.  Then the two curves agree on all of `Icc a b`.

The proof lifts both curves to `ℝ × M` via the autonomisation
(`autonomizedLift_isMIntegralCurveOn_of_bareFlow`), where they are integral curves of the
autonomous field `autonomizedFlowVF X`; the forward `Icc` uniqueness
`isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff` on the boundaryless product manifold `ℝ × M`
gives equality of the lifts, and projecting onto the second coordinate yields the statement.

Unlike the two-sided version, the agreement is required only at the *left* endpoint, so this
applies to forward-only flows (e.g. the diffeomorphism family `Φ_fam` with `Φ_fam 0 = id`, whose
bare flow equation holds only for positive times). -/
theorem bare_forward_flow_eqOn_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X)
    (Φ Φ' : ℝ → M → M) (x x' : M) {a b : ℝ}
    (hflow : ∀ t ∈ Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))))
    (hstart : Φ a x = Φ' a x') :
    ∀ t ∈ Icc a b, Φ t x = Φ' t x' := by
  -- Lift both curves to `ℝ × M`.
  have hc : IsMIntegralCurveOn (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF X) (Icc a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ x (Icc a b) hflow
  have hc' : IsMIntegralCurveOn (fun u : ℝ => (u, Φ' u x')) (autonomizedFlowVF X) (Icc a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ' x' (Icc a b) hflow'
  -- The autonomised field is `C¹` as a tangent-bundle section on `ℝ × M`.
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    fun p => hX p
  -- The two lifts agree at the left endpoint `a`.
  have hstartlift : (fun u : ℝ => (u, Φ u x)) a = (fun u : ℝ => (u, Φ' u x')) a := by
    simp only; rw [hstart]
  -- Apply forward `Icc` uniqueness on the boundaryless product manifold `ℝ × M`.
  have heq : EqOn (fun u : ℝ => (u, Φ u x)) (fun u : ℝ => (u, Φ' u x')) (Icc a b) :=
    isMIntegralCurveOn_Icc_eqOn_left_of_contMDiff hv hc hc' hstartlift
  intro t ht
  have := heq ht
  simpa using congrArg Prod.snd this

end BareForward

end DifferentialGeometry.PDE.RicciFlow.ODE
