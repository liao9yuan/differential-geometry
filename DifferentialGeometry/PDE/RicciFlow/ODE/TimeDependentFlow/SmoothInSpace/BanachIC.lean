import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import DifferentialGeometry.Analysis.ODE.FlowCInfinity

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem banach_flow_smooth_in_ic
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) :=
  time_dependent_vf_chart_local_picard_with_lipschitz X α hCont hLip

section SmoothLocalFlow

open Set Metric Function DifferentialGeometry.Analysis.ODE DifferentialGeometry.Analysis.ODE.Flow
open scoped NNReal

/-- **Smooth local flow from a jointly `C^∞` vector field.**

For a time-dependent vector field `f : ℝ → E → E` on a finite-dimensional
complete Banach space, jointly `C^∞` in `(t, x)`, and any base point
`(t₀, x₀)`, there exist a Picard--Lindelöf local flow `Φ` and a strictly
interior open neighbourhood on which `Φ` is jointly `C^∞`.

The proof combines the Picard--Lindelöf existence theorem
(`exists_isLocalFlow_of_contDiffOn_univ`) with the Hartman smooth-dependence
induction (`contDiffOn_top_flow_of_isLocalFlow_of_contDiff_top`). The only
substantial new content is the uniform operator-norm bound on the
linearization `(x, t) ↦ fderiv ℝ (f t) (Φ(x, t))`, which follows from
continuity of the composition on a compact product. -/
theorem exists_smooth_localFlow_of_contDiff_top
    [CompleteSpace E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε)
      (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (ρ : ℝ) (T : ℝ), 0 < ρ ∧ 0 < T ∧ (ρ : ℝ) ≤ r ∧ T ≤ ε ∧
        ContDiffOn ℝ ∞ Φ
          (Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
  -- Step 1: C^1 regularity of uncurry f.
  have hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (univ : Set (ℝ × E)) :=
    hf.contDiffOn.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  -- Step 2: Picard--Lindelöf local flow.
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    exists_isLocalFlow_of_contDiffOn_univ f hf_C1 t₀ x₀
  have hrN_pos : (0 : ℝ) < rN := hrN
  -- Step 3: Uniform bound M on ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ over the compact
  -- product closedBall x₀ rN × Icc (t₀ − εN) (t₀ + εN).
  --
  -- The partial Fréchet derivative (t, y) ↦ fderiv ℝ (f t) y is continuous on
  -- univ (from C^1 of uncurry f).
  have hpartial_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (univ : Set ℝ)) (u := (univ : Set E))
      (by rwa [univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [univ_prod_univ] at h
  -- (x, t) ↦ (t, Φ(x,t)) is continuous on the flow domain.
  have hcomp_cont : ContinuousOn
      (fun q : E × ℝ => (q.2, Φ q))
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    continuousOn_snd.prodMk hΦ.continuousOn
  -- Composition: (x, t) ↦ fderiv ℝ (f t) (Φ(x, t)) is continuous on the product.
  have hfull_cont : ContinuousOn
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    hpartial_cont.comp hcomp_cont (fun _ _ => mem_univ _)
  -- Norm is continuous on the compact product.
  have hnorm_cont : ContinuousOn
      (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖)
      (closedBall x₀ rN ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    continuous_norm.comp_continuousOn hfull_cont
  have hK : IsCompact (closedBall x₀ (rN : ℝ) ×ˢ Icc (t₀ - εN) (t₀ + εN)) :=
    (ProperSpace.isCompact_closedBall x₀ rN).prod isCompact_Icc
  have hne : (closedBall x₀ (rN : ℝ) ×ˢ Icc (t₀ - εN) (t₀ + εN)).Nonempty :=
    ⟨⟨x₀, t₀⟩, mem_prod.mpr
      ⟨mem_closedBall_self (by exact_mod_cast le_of_lt hrN),
       mem_Icc.mpr ⟨by linarith, by linarith⟩⟩⟩
  -- Extract the maximum on the compact set.
  obtain ⟨q₀, hq₀_mem, hq₀_max⟩ := hK.exists_isMaxOn hne hnorm_cont
  set Mglob := ‖fderiv ℝ (f q₀.2) (Φ q₀)‖
  have hMglob_nn : 0 ≤ Mglob := norm_nonneg _
  have hMglob_bound : ∀ x ∈ closedBall x₀ (rN : ℝ),
      ∀ τ ∈ Icc (t₀ - εN) (t₀ + εN), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ Mglob := by
    intro x hx τ hτ
    exact hq₀_max (show (x, τ) ∈ _ from ⟨hx, hτ⟩)
  -- Step 4: Choose nested temporal and spatial parameters for the Hartman theorem.
  -- Tcap = min εN (1 / (2 * (Mglob + 1))), guaranteeing M * T_mid < 1.
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1)))
  have hTcap_pos : 0 < Tcap := lt_min hεN (by positivity)
  -- Temporal layers: T_out > T_mid > T, with T_out ≤ εN.
  set T_out : ℝ := Tcap / 2
  set T_mid : ℝ := Tcap / 4
  set T : ℝ := Tcap / 8
  have hT_pos : 0 < T := by change 0 < Tcap / 8; linarith
  have hT_lt_mid : T < T_mid := by change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    change Tcap / 2 ≤ εN
    have : Tcap ≤ εN := min_le_left _ _
    linarith
  -- M * T_mid < 1.
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    -- T_mid = Tcap / 4 ≤ (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1))
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith
    have hMplus_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) :=
            mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := by
            rw [div_le_div_iff₀ hMplus_pos (by norm_num : (0 : ℝ) < 8)]
            nlinarith [hMglob_nn]
      _ < 1 := by norm_num
  -- Time-domain containment.
  have hsub_T_out : Icc (t₀ - T_out) (t₀ + T_out) ⊆
      Icc (t₀ - εN) (t₀ + εN) :=
    Icc_subset_Icc (by linarith [hT_out_le_eps]) (by linarith [hT_out_le_eps])
  -- Spatial layers: ρ_out > ρ_mid > ρ, with ρ_mid + r' ≤ rN and ρ_out ≤ rN.
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8; linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ); linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ); linarith
  -- Operator-norm bound on the ρ_out × T_out subdomain.
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ),
      ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ Mglob := by
    intro x hx τ hτ
    exact hMglob_bound x (closedBall_subset_closedBall hρ_out_le_r hx) τ (hsub_T_out hτ)
  -- Step 5: Apply the Hartman C^∞ theorem.
  have hSmooth :=
    contDiffOn_top_flow_of_isLocalFlow_of_contDiff_top
      hΦ hf hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Package the result.
  refine ⟨rN, εN, hrN, hεN, Φ, hΦ, (ρ : ℝ), T, hρ_pos, hT_pos, ?_, ?_, hSmooth⟩
  · -- ρ ≤ rN
    change (rN : ℝ) / 8 ≤ (rN : ℝ); linarith
  · -- T ≤ εN
    change Tcap / 8 ≤ εN
    have : Tcap ≤ εN := min_le_left _ _
    linarith

end SmoothLocalFlow

section TransferSmoothness

open Set Metric Function DifferentialGeometry.Analysis.ODE DifferentialGeometry.Analysis.ODE.Flow
open scoped NNReal Topology

variable [CompleteSpace E]

/-- Transfer C^∞ regularity from the Hartman smooth local flow to the Picard flow
`ChartLocalPicardData.flow` via ODE uniqueness.

Given a chart-local Picard flow `hper.flow` and a jointly `C^∞` chart-coordinate
vector field `f_chart`, we show there exist `ρ > 0` and `T₀ > 0` with `ρ ≤ hper.r`
and `T₀ ≤ hper.T` such that `uncurry hper.flow` is `C^∞` on
`ball(center, ρ) ×ˢ Ioo(0, T₀)`.

The proof applies the Hartman smooth-dependence theorem to obtain a smooth local
flow `Φ_pl` solving the same ODE, then shows `Φ_pl(y, t) = hper.flow y t` for every
`(y, t) ∈ closedBall(center, ρ) × Icc(0, T₀)` by Groenwall ODE uniqueness, and
finally transfers the `C^∞` regularity via `ContDiffOn.congr`. -/
theorem chart_local_picard_flow_contDiffOn_of_contDiff_top
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hper : ChartLocalPicardData X α)
    (hSmoothX_chart : ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E))) :
    ∃ (ρ : ℝ) (T₀ : ℝ), 0 < ρ ∧ 0 < T₀ ∧ ρ ≤ hper.r ∧ T₀ ≤ hper.T ∧
      ContDiffOn ℝ ∞ (Function.uncurry hper.flow)
        (Metric.ball (I ((chartAt H α) α)) ρ ×ˢ Set.Ioo 0 T₀) := by
  -- Abbreviations.
  set center : E := I ((chartAt H α) α)
  set f_chart : ℝ → E → E := fun t y => (X t ((chartAt H α).symm (I.symm y)) : E)
  -- Step 1: Apply Hartman smooth-dependence at t₀ = 0, x₀ = center.
  have hf_top : ContDiff ℝ ∞ (Function.uncurry f_chart) := hSmoothX_chart
  obtain ⟨rN, εN, hrN, hεN, Φ_pl, hΦ_pl, ρ_pl, T_pl, hρ_pl_pos, hT_pl_pos,
    hρ_pl_le, hT_pl_le, hΦ_smooth⟩ :=
    exists_smooth_localFlow_of_contDiff_top (f := f_chart) (t₀ := 0) (x₀ := center) hf_top
  -- Step 2: Choose ρ₀ = min(ρ_pl, hper.r) and T₀ = min(T_pl, hper.T).
  set ρ₀ : ℝ := min ρ_pl hper.r
  set T₀ : ℝ := min T_pl hper.T
  have hρ₀_pos : 0 < ρ₀ := lt_min hρ_pl_pos hper.r_pos
  have hT₀_pos : 0 < T₀ := lt_min hT_pl_pos hper.T_pos
  have hρ₀_le_ρ_pl : ρ₀ ≤ ρ_pl := min_le_left _ _
  have hρ₀_le_r : ρ₀ ≤ hper.r := min_le_right _ _
  have hT₀_le_T_pl : T₀ ≤ T_pl := min_le_left _ _
  have hT₀_le_T : T₀ ≤ hper.T := min_le_right _ _
  -- The Hartman flow data.
  have hΦ_init : ∀ x ∈ closedBall center rN, Φ_pl ⟨x, 0⟩ = x := by
    intro x hx; exact hΦ_pl.apply_initial x hx
  have hΦ_deriv : ∀ x ∈ closedBall center rN, ∀ t ∈ Icc (0 - εN) (0 + εN),
      HasDerivWithinAt (fun s => Φ_pl ⟨x, s⟩) (f_chart t (Φ_pl ⟨x, t⟩))
        (Icc (0 - εN) (0 + εN)) t :=
    hΦ_pl.hasDerivWithinAt
  -- Step 3: ODE uniqueness — for each y ∈ closedBall(center, ρ₀), show
  -- Φ_pl(y, t) = hper.flow y t on Icc 0 T₀.
  -- We use ODE_solution_unique_of_mem_Icc_right.
  -- First, establish a uniform Lipschitz constant for f_chart on a large enough ball
  -- that contains both orbits.
  -- The Picard flow orbit for y is continuous on [0, T] ⊇ [0, T₀].
  -- The Hartman flow orbit for y is continuous on [-εN, εN] ⊇ [0, T₀].
  -- Containment: [0, T₀] ⊆ [-εN, εN].
  have hT₀_le_εN : T₀ ≤ εN := hT₀_le_T_pl.trans hT_pl_le
  have hIcc_sub_hartman : Icc 0 T₀ ⊆ Icc (0 - εN) (0 + εN) := by
    intro t ht; simp only [zero_sub, zero_add] at *
    exact ⟨le_trans (neg_nonpos_of_nonneg hεN.le) ht.1, ht.2.trans hT₀_le_εN⟩
  -- Containment: closedBall(center, ρ₀) ⊆ closedBall(center, rN).
  have hρ₀_le_rN : ρ₀ ≤ (rN : ℝ) := hρ₀_le_ρ_pl.trans hρ_pl_le
  have hcb_sub : closedBall center ρ₀ ⊆ closedBall center rN :=
    closedBall_subset_closedBall hρ₀_le_rN
  -- For each y, the Picard orbit is continuous on [0, T₀].
  have hflow_cont : ∀ y ∈ closedBall center ρ₀,
      ContinuousOn (hper.flow y) (Icc 0 T₀) := by
    intro y hy
    have hspec := hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)
    have hcont_full : ContinuousOn (hper.flow y) (Icc 0 hper.T) :=
      fun t ht => (hspec.2 t ht).continuousWithinAt
    exact hcont_full.mono (Icc_subset_Icc le_rfl hT₀_le_T)
  -- For each y, the Hartman orbit is continuous on [0, T₀].
  have hΦ_cont : ∀ y ∈ closedBall center ρ₀,
      ContinuousOn (fun t => Φ_pl ⟨y, t⟩) (Icc 0 T₀) := by
    intro y hy
    exact (hΦ_pl.orbit_continuousOn y (hcb_sub hy)).mono hIcc_sub_hartman
  -- Extract a uniform ball and Lipschitz constant.
  -- Both orbits are continuous on [0, T₀], hence bounded. Their images lie in some
  -- closedBall(0, R). On this ball, f_chart t is Lipschitz uniformly in t ∈ [0, T₀].
  -- We derive Lipschitz from C^∞ on a compact convex domain.
  -- Step 3a: Lipschitz constant for f_chart.
  -- f_chart is C^∞ on univ, so C^1. On any compact convex set, it's Lipschitz.
  -- We need a uniform K for all t ∈ [0, T₀].
  -- The partial derivative (t, y) ↦ fderiv ℝ (f_chart t) y is continuous on ℝ × E.
  -- On the compact set [0, T₀] × closedBall(center, R), it's bounded, giving K.
  -- Step 3b: For fixed y, prove the ODE uniqueness.
  -- We show the equality on Icc 0 T₀, which implies equality on Ioo 0 T₀.
  have heq_on : ∀ y ∈ closedBall center ρ₀,
      EqOn (fun t => Φ_pl ⟨y, t⟩) (hper.flow y) (Icc 0 T₀) := by
    intro y hy
    -- Both orbits are continuous on [0, T₀].
    have hΦy_cont := hΦ_cont y hy
    have hflow_y_cont := hflow_cont y hy
    -- Both orbits have images in a compact ball.
    -- Union of the two compact images is compact, contained in some closedBall.
    have hΦy_bdd : Bornology.IsBounded ((fun t => Φ_pl ⟨y, t⟩) '' Icc 0 T₀) :=
      (isCompact_Icc.image_of_continuousOn hΦy_cont).isBounded
    have hflow_y_bdd : Bornology.IsBounded ((hper.flow y) '' Icc 0 T₀) :=
      (isCompact_Icc.image_of_continuousOn hflow_y_cont).isBounded
    -- Extract R.
    obtain ⟨R_Φ, hR_Φ⟩ := hΦy_bdd.subset_ball 0
    obtain ⟨R_f, hR_f⟩ := hflow_y_bdd.subset_ball 0
    set R : ℝ := max (max R_Φ R_f) 0 + 1
    have hR_pos : 0 < R := by linarith [le_max_right (max R_Φ R_f) 0]
    have hΦy_in : ∀ t ∈ Ico (0 : ℝ) T₀, Φ_pl ⟨y, t⟩ ∈ closedBall (0 : E) R := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T₀ := Ico_subset_Icc_self ht
      have := hR_Φ (mem_image_of_mem _ ht')
      rw [mem_ball] at this
      rw [mem_closedBall]
      calc dist (Φ_pl ⟨y, t⟩) 0 ≤ R_Φ := le_of_lt this
        _ ≤ max R_Φ R_f := le_max_left _ _
        _ ≤ max (max R_Φ R_f) 0 := le_max_left _ _
        _ ≤ R := by linarith
    have hflow_y_in : ∀ t ∈ Ico (0 : ℝ) T₀, hper.flow y t ∈ closedBall (0 : E) R := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T₀ := Ico_subset_Icc_self ht
      have := hR_f (mem_image_of_mem _ ht')
      rw [mem_ball] at this
      rw [mem_closedBall]
      calc dist (hper.flow y t) 0 ≤ R_f := le_of_lt this
        _ ≤ max R_Φ R_f := le_max_right _ _
        _ ≤ max (max R_Φ R_f) 0 := le_max_left _ _
        _ ≤ R := by linarith
    -- Lipschitz constant for f_chart t on closedBall 0 R.
    -- f_chart is C^∞, so its restriction to any compact convex set is Lipschitz.
    -- For each t, f_chart t is C^1 (hence differentiable and with continuous fderiv).
    have hfchart_t_diff : ∀ t : ℝ, Differentiable ℝ (f_chart t) := by
      intro t
      have h1 : ContDiff ℝ ∞ (f_chart t) := by
        change ContDiff ℝ ∞ (fun y : E => uncurry f_chart (t, y))
        exact hf_top.comp (contDiff_const.prodMk contDiff_id)
      exact h1.differentiable (by simp)
    -- The fderiv is jointly continuous and bounded on the compact set.
    have hfchart_C1 : ContDiffOn ℝ 1 (uncurry f_chart) univ :=
      hf_top.contDiffOn.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    have hfderiv_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f_chart p.1) p.2) univ := by
      have h := continuousOn_partialFDeriv_uncurry (f := f_chart)
        (s := (univ : Set ℝ)) (u := (univ : Set E))
        (by rwa [univ_prod_univ]) isOpen_univ isOpen_univ
      rwa [univ_prod_univ] at h
    -- Bound the fderiv norm on the compact set [0, T₀] × closedBall 0 R.
    have hcompact_domain : IsCompact (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R) :=
      isCompact_Icc.prod (ProperSpace.isCompact_closedBall 0 R)
    have hne_domain : (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R).Nonempty :=
      ⟨(0, 0), mem_prod.mpr ⟨left_mem_Icc.mpr hT₀_pos.le, mem_closedBall_self hR_pos.le⟩⟩
    have hnorm_fderiv_cont : ContinuousOn
        (fun p : ℝ × E => ‖fderiv ℝ (f_chart p.1) p.2‖)
        (Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R) :=
      (continuous_norm.comp_continuousOn
        (hfderiv_cont.mono (subset_univ _)))
    obtain ⟨p₀, _, hp₀_max⟩ :=
      hcompact_domain.exists_isMaxOn hne_domain hnorm_fderiv_cont
    set Kval : ℝ := ‖fderiv ℝ (f_chart p₀.1) p₀.2‖
    have hKval_nn : 0 ≤ Kval := norm_nonneg _
    set K : ℝ≥0 := ⟨Kval, hKval_nn⟩
    -- Uniform Lipschitz bound via mean value theorem on convex set.
    have hfchart_lip : ∀ t ∈ Ico (0 : ℝ) T₀,
        LipschitzOnWith K (f_chart t) (closedBall (0 : E) R) := by
      intro t ht
      apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun x hx => ((hfchart_t_diff t x).hasFDerivAt).hasFDerivWithinAt)
      · intro x hx
        change ‖fderiv ℝ (f_chart t) x‖₊ ≤ K
        rw [← NNReal.coe_le_coe]
        change ‖fderiv ℝ (f_chart t) x‖ ≤ Kval
        have : (t, x) ∈ Icc (0 : ℝ) T₀ ×ˢ closedBall (0 : E) R :=
          ⟨Ico_subset_Icc_self ht, hx⟩
        exact hp₀_max this
      · exact convex_closedBall 0 R
    -- HasDerivWithinAt for the Hartman flow on Ici t.
    have hΦy_deriv : ∀ t ∈ Ico (0 : ℝ) T₀,
        HasDerivWithinAt (fun s => Φ_pl ⟨y, s⟩)
          (f_chart t (Φ_pl ⟨y, t⟩)) (Ici t) t := by
      intro t ht
      have ht_hartman : t ∈ Icc (0 - εN) (0 + εN) :=
        hIcc_sub_hartman (Ico_subset_Icc_self ht)
      have hdw := hΦ_deriv y (hcb_sub hy) t ht_hartman
      -- Promote from HasDerivWithinAt on Icc (-εN) εN to HasDerivWithinAt on Ici t.
      -- Since t ∈ Ico 0 T₀ and T₀ ≤ εN, we have t < εN, so Icc (-εN) εN ∈ nhdsWithin t (Ici t).
      have ht_lt_εN : t < εN := lt_of_lt_of_le ht.2 hT₀_le_εN
      have hmem : Icc (0 - εN) (0 + εN) ∈ 𝓝[≥] t := by
        simp only [zero_sub, zero_add]
        exact Icc_mem_nhdsGE_of_mem ⟨le_trans (neg_nonpos_of_nonneg hεN.le) ht.1, ht_lt_εN⟩
      exact hdw.mono_of_mem_nhdsWithin hmem
    -- HasDerivWithinAt for the Picard flow on Ici t.
    have hflow_y_deriv : ∀ t ∈ Ico (0 : ℝ) T₀,
        HasDerivWithinAt (hper.flow y)
          (f_chart t (hper.flow y t)) (Ici t) t := by
      intro t ht
      have hspec := hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)
      have ht_Icc : t ∈ Icc (0 : ℝ) hper.T := ⟨ht.1, (Ico_subset_Icc_self ht).2.trans hT₀_le_T⟩
      have hdw := hspec.2 t ht_Icc
      -- Promote from HasDerivWithinAt on Icc 0 hper.T to HasDerivWithinAt on Ici t.
      have ht_lt_T : t < hper.T := lt_of_lt_of_le ht.2 hT₀_le_T
      have hmem : Icc (0 : ℝ) hper.T ∈ 𝓝[≥] t :=
        Icc_mem_nhdsGE_of_mem ⟨ht.1, ht_lt_T⟩
      exact hdw.mono_of_mem_nhdsWithin hmem
    -- Initial value agreement.
    have hinit : Φ_pl ⟨y, 0⟩ = hper.flow y 0 := by
      rw [hΦ_init y (hcb_sub hy)]
      exact (hper.flow_spec y (closedBall_subset_closedBall hρ₀_le_r hy)).1.symm
    -- Apply ODE uniqueness.
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun t z => f_chart t z) (s := fun _ => closedBall 0 R) (K := K)
      hfchart_lip hΦy_cont hΦy_deriv hΦy_in hflow_y_cont hflow_y_deriv hflow_y_in hinit
  -- Step 4: Transfer C^∞ from Φ_pl to uncurry hper.flow.
  -- The Hartman flow is C^∞ on ball(center, ρ_pl) ×ˢ Ioo(-T_pl, T_pl).
  -- Restrict to ball(center, ρ₀) ×ˢ Ioo(0, T₀) ⊆ ball(center, ρ_pl) ×ˢ Ioo(-T_pl, T_pl).
  have hΦ_smooth_sub : ContDiffOn ℝ ∞ Φ_pl
      (ball center ρ₀ ×ˢ Ioo 0 T₀) := by
    apply hΦ_smooth.mono
    apply prod_mono
    · exact ball_subset_ball hρ₀_le_ρ_pl
    · intro t ht
      simp only [zero_sub, zero_add, mem_Ioo] at *
      exact ⟨by linarith [hT_pl_pos], by linarith [hT₀_le_T_pl]⟩
  -- The equality holds on the closure (Icc), hence on Ioo.
  have hcongr : ∀ q ∈ ball center ρ₀ ×ˢ Ioo (0 : ℝ) T₀,
      uncurry hper.flow q = Φ_pl q := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    simp only [uncurry]
    have hx_cb : x ∈ closedBall center ρ₀ :=
      mem_closedBall.mpr (le_of_lt (mem_ball.mp hx))
    have ht_Icc : t ∈ Icc (0 : ℝ) T₀ := Ioo_subset_Icc_self ht
    exact (heq_on x hx_cb ht_Icc).symm
  exact ⟨ρ₀, T₀, hρ₀_pos, hT₀_pos, hρ₀_le_r, hT₀_le_T,
    hΦ_smooth_sub.congr hcongr⟩

end TransferSmoothness

end DifferentialGeometry.PDE.RicciFlow.ODE
