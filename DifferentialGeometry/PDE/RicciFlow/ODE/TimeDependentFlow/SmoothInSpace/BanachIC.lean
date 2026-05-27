import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
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

end DifferentialGeometry.PDE.RicciFlow.ODE
