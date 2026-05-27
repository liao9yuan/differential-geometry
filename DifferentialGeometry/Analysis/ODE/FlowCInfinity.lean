import DifferentialGeometry.Analysis.ODE.ParametricLinearODE
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Joint `C^∞` regularity of the local flow (Hartman smooth-dependence theorem)

For a time-dependent vector field `f : ℝ → E → E` on a finite-dimensional Banach space
`E` and a local Picard–Lindelöf flow `Φ : E × ℝ → E` packaged by `IsLocalFlow`, this
file proves that `Φ` is jointly `C^∞` on the strictly-interior open neighbourhood
`ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`, provided `f` is jointly `C^∞`.

## Strategy

The proof is by induction on `n : ℕ`, showing that `Φ` is `C^n` on the *fixed* open
neighbourhood for every `n`.

**Base case**: `C^1` from `contDiffOn_flow_of_isLocalFlow`.

**Inductive step (`n → n + 1`)**: assuming `Φ` is `C^n`, the variational coefficient
`A(x, t) := fderiv ℝ (f t) (Φ(x, t))` is jointly `C^n` (composition of `C^∞` with
`C^n`).  For each `δ`, the variational solution equals
`linearODESolution A ... (fun _ => δ) x t` by ODE uniqueness, hence is `C^n` by
`linearODESolution_contDiffOn`.  By `contDiffOn_clm_apply` (finite-dimensional `E`),
the CLM-valued spatial piece is `C^n`, and `contDiffOn_flow_succ_of_spatial_smooth`
upgrades `Φ` to `C^{n+1}`.

## Main result

* `contDiffOn_top_flow_of_isLocalFlow_of_contDiff_top`
-/

noncomputable section

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set Metric Function
open scoped ContDiff NNReal

/-! ## `C^∞` from finite-order regularity -/

/-- If `f` is `C^k` on `S` for every natural number `k`, then `f` is `C^∞` on `S`. -/
theorem contDiffOn_top_of_forall_nat
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {S : Set E}
    (h : ∀ k : ℕ, ContDiffOn 𝕜 (k : ℕ∞) f S) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) f S :=
  contDiffOn_infty.mpr h

/-! ## Coefficient regularity -/

section CoefficientRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {Φ : E × ℝ → E}

/-- The variational coefficient `(x, t) ↦ fderiv ℝ (f t) (Φ(x, t))` is `C^n` when
`f` is `C^{n+1}` and `Φ` is `C^n`. -/
theorem contDiffOn_variational_coeff
    {n : ℕ} {T : ℝ} {ρ : ℝ≥0}
    (hf_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) (univ : Set (ℝ × E)))
    (hΦ_Cn : ContDiffOn ℝ (n : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ (n : ℕ∞)
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set pfD : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2
  set iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  suffices h : ContDiffOn ℝ (n : ℕ∞) (pfD ∘ iM) U by exact h.congr (fun _ _ => rfl)
  have hpfd : ContDiffOn ℝ (n : ℕ∞) pfD (univ : Set (ℝ × E)) :=
    contDiffOn_partial_fderiv_of_succ hf_succ
  have hiM : ContDiffOn ℝ (n : ℕ∞) iM U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ (n : ℕ∞) Prod.snd U).prodMk hΦ_Cn
  exact hpfd.comp hiM (fun _ _ => mem_univ _)

end CoefficientRegularity

/-! ## The Hartman `C^∞` theorem -/

section HartmanTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Hartman smooth-dependence theorem for ODE flows.**

If the vector field `f : ℝ → E → E` is jointly `C^∞` and `Φ` is a local
Picard–Lindelöf flow of `f`, then `Φ` is jointly `C^∞` on the strictly interior open
neighbourhood `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem contDiffOn_top_flow_of_isLocalFlow_of_contDiff_top
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_top : ContDiff ℝ ∞ (uncurry f))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid)
      (hT_mid_lt_out : T_mid < T_out) (hM : 0 ≤ M)
      (hMT_mid : M * T_mid < 1)
      (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
      (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ))
      (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
      (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
      (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ),
       ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
       ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ ∞ Φ
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  apply contDiffOn_top_of_forall_nat
  intro n
  -- Abbreviations.
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  -- f is C^k for every k.
  have hf_Ck : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞) (uncurry f) (univ : Set (ℝ × E)) :=
    fun k => (hf_top.contDiffOn : ContDiffOn ℝ ∞ (uncurry f) univ).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  -- C^1 base.
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (univ : Set (ℝ × E)) := by simpa using hf_Ck 1
  have hΦ_C1 : ContDiffOn ℝ 1 Φ U :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Picard parameter setup for variational linear map.
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M :=
    fun x hx τ hτ =>
      hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  have hab : t₀ - T < t₀ + T := by linarith
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  -- Induction on n.
  induction n with
  | zero => exact hΦ_C1.of_le (by decide)
  | succ n ih =>
    -- f is C^{n+1} (and more).
    have hf_Csucc : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) (univ : Set (ℝ × E)) := by
      simpa using hf_Ck (n + 1)
    -- Coefficient A(x,t) := fderiv ℝ (f t) (Φ(x,t)) is C^n.
    have hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q)) U :=
      contDiffOn_variational_coeff hf_Csucc ih
    -- Coefficient in curried form for linearODESolution.
    set A : E → ℝ → (E →L[ℝ] E) := fun x t => fderiv ℝ (f t) (Φ ⟨x, t⟩)
    -- Each scalar variational solution linearODESolution(A, ..., fun _ => δ) is C^n.
    have hlinear_Cn : ∀ δ : E, ContDiffOn ℝ (n : ℕ∞)
        (uncurry (linearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ)))
        (ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
      fun δ => linearODESolution_contDiffOn hab ht₀_mem isOpen_ball n
        (hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry A) _)
        (contDiffOn_const : ContDiffOn ℝ (n : ℕ∞) (fun (_ : E) => δ) (ball x₀ (ρ : ℝ)))
    -- The spatial piece of fderiv Φ.
    set Lsp : E × ℝ → E →L[ℝ] E :=
      fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)
    -- fderiv_eq: fderiv Φ = Lsp.coprod(timePieceFn) on U.
    have hfderiv_coprod : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q) := by
      intro ⟨x, t⟩ ⟨hx, ht⟩
      have hx' : dist x x₀ < ↑ρ := mem_ball.mp hx
      have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
        mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
      have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hfd := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid
        hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
      -- fderiv Φ (x,t) = (vlm).coprod(tp)  by hfd.fderiv
      -- Lsp (x,t) = (fderiv Φ (x,t)).comp(inl) = vlm  by coprod_comp_inl
      -- So fderiv Φ = Lsp.coprod(tp).
      -- From coprod decomposition: L = L.comp(inl).coprod(L.comp(inr))
      -- After rw [hfd.fderiv], the goal becomes:
      --   (vlm).coprod(tp) = Lsp(x,t).coprod(timePieceFn ...)
      -- Since Lsp(x,t) = (fderiv Φ (x,t)).comp(inl) = (vlm.coprod(tp)).comp(inl) = vlm
      -- and timePieceFn agrees with the time piece, this is done.
      rw [hfd.fderiv]
      change (variationalLinearMapAt hT_mid_pos hM hMT_mid _ _ _).coprod
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ (x, t))))
        = (Lsp (x, t)).coprod (timePieceFn f Φ (x, t))
      congr 1
      · -- Lsp(x,t) = vlm
        change _ = (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
        rw [hfd.fderiv]
        exact (ContinuousLinearMap.coprod_comp_inl _ _).symm
    -- Lsp is C^n via contDiffOn_clm_apply + linearODESolution identification.
    have hLsp_Cn : ContDiffOn ℝ (n : ℕ∞) Lsp U := by
      rw [contDiffOn_clm_apply]
      intro δ
      -- Show: (x,t) ↦ Lsp(x,t)(δ) is C^n.
      -- Strategy: show it equals linearODESolution(A, ..., fun _ => δ, x, t) on U,
      -- which is C^n by hlinear_Cn.
      refine (hlinear_Cn δ).congr (fun q hq => ?_)
      -- Need: Lsp q δ = uncurry (linearODESolution A ...) q.
      obtain ⟨hx_ball, ht_Ioo⟩ := hq
      have hx' : dist q.1 x₀ < ↑ρ := mem_ball.mp hx_ball
      have hx_cb_mid : q.1 ∈ closedBall x₀ (ρ_mid : ℝ) :=
        mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
      have ht_mid : q.2 ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
        ⟨by linarith [ht_Ioo.1], by linarith [ht_Ioo.2]⟩
      have hΦ_restr := hΦ.restrict_center_of_norm_le (x₁ := q.1) (r' := r') (by
        rw [mem_closedBall] at hx_cb_mid; linarith)
      have hA_cont_x := ((hΦ_restr.continuousOn_fderiv_along_orbit hf_C1 q.1
        (mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub_mid)
      have hA_bd_x := fun τ hτ => hA_bd_mid q.1 hx_cb_mid τ hτ
      have ht_Icc : q.2 ∈ Icc (t₀ - T_mid) (t₀ + T_mid) := Ioo_subset_Icc_self ht_mid
      -- From hasFDerivAt_flow_jointly_at:
      have hfd := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid
        hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
      -- Step 1: Lsp q = variationalLinearMapAt(...)
      have hLsp_eq_vlm : Lsp q =
          variationalLinearMapAt hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x ht_Icc := by
        change (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) = _
        conv_lhs => rw [show q = (q.1, q.2) from Prod.mk.eta.symm]
        rw [hfd.fderiv]
        exact ContinuousLinearMap.coprod_comp_inl _ _
      -- Step 2: variationalLinearMapAt(δ) = variationalSolutionFun(δ)(q.2)
      have hvlm_eq := variationalLinearMapAt_apply hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x
        ht_Icc δ
      -- Step 3: variationalSolutionFun(δ)(q.2) = linearODESolution(A, ...)(q.1)(q.2)
      have hvsf := variationalSolutionFun_isSolution hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x δ
      have hA_cont_Ioo : ContinuousOn (A q.1) (Ioo (t₀ - T) (t₀ + T)) :=
        hA_cont_x.mono (fun s hs => Ioo_subset_Icc_self
          (⟨by linarith [hs.1], by linarith [hs.2]⟩ : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid)))
      have hA_joint_cont : ContinuousOn (uncurry A)
          (ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T)) := hcoeff_Cn.continuousOn
      have h_exists : HasLinearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ) q.1 :=
        hasLinearODESolution_of_continuousOn hab ht₀_mem isOpen_ball hA_joint_cont (mem_ball.mpr hx')
      have h_uniq := linearODE_unique_on_Ioo (G := E) ht₀_mem hA_cont_Ioo
        (fun s hs => by
          have hs_mid : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
            ⟨by linarith [hs.1], by linarith [hs.2]⟩
          exact (hvsf.2 s (Ioo_subset_Icc_self hs_mid)).hasDerivAt (Icc_mem_nhds_iff.mpr hs_mid))
        (fun s hs => linearODESolution_hasDerivAt_of_hasSolution A (t₀ - T) (t₀ + T) t₀
          (fun _ => δ) h_exists hs)
        (by rw [hvsf.1, linearODESolution_init])
      -- Combine.
      simp only [hLsp_eq_vlm, hvlm_eq, uncurry]
      have h_eq := h_uniq ht_Ioo
      -- h_eq : variationalSolutionFun ... q.2 = linearODESolution ... q.1 q.2
      -- (up to beta-reduction in linearODE_unique_on_Ioo's EqOn conclusion)
      dsimp at h_eq
      exact h_eq
    -- Upgrade Φ from C^n to C^{n+1} by `contDiffOn_flow_succ_of_spatial_smooth`.
    exact contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub
      hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
      (by simpa using hf_Ck (n + 1)) ih hLsp_Cn hfderiv_coprod

end HartmanTheorem

end DifferentialGeometry.Analysis.ODE.Flow

end
