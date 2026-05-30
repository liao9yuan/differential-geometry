import RicciFlower.Analysis.ODE.ParametricLinearODE
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
set_option linter.unusedSectionVars false

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

* `IsLocalFlow.contDiffOn_top`
-/

noncomputable section

namespace RicciFlower.Analysis.ODE.Flow

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
private theorem contDiffOn_variational_coeff_aux
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

/-- Local version of `contDiffOn_variational_coeff_aux` on an open domain
`Ω`, provided the flow graph over `U` stays in `Ω`. -/
private theorem contDiffOn_variational_coeff_aux_local
    {n : ℕ} {T : ℝ} {ρ : ℝ}
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) Ω)
    (hΦ_Cn : ContDiffOn ℝ (n : ℕ∞) Φ ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    (hΩ_map :
      ∀ q ∈ ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)),
        (q.2, Φ q) ∈ Ω) :
    ContDiffOn ℝ (n : ℕ∞)
      (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      ((ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set pfD : ℝ × E → (E →L[ℝ] E) := fun p => fderiv ℝ (f p.1) p.2
  set iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  set U := (ball x₀ ρ) ×ˢ Ioo (t₀ - T) (t₀ + T)
  suffices h : ContDiffOn ℝ (n : ℕ∞) (pfD ∘ iM) U by
    exact h.congr (fun _ _ => rfl)
  have hpfd : ContDiffOn ℝ (n : ℕ∞) pfD Ω :=
    contDiffOn_partial_fderiv_of_succ_local hΩ hf_succ
  have hiM : ContDiffOn ℝ (n : ℕ∞) iM U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ (n : ℕ∞) Prod.snd U).prodMk hΦ_Cn
  exact hpfd.comp hiM hΩ_map

end CoefficientRegularity

/-! ## Local flow-tube bounds -/

section LocalFlowTubeBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

/-- Joint continuity of the spatial linearization on a compact flow tube
contained in a local smoothness domain. -/
private theorem continuousOn_fderiv_jointly_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  let G : E × ℝ → E →L[ℝ] E := fun q => fderiv ℝ (f q.2) (Φ q)
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hG : ContinuousOn G K := by
    have hcomp := hpfD.continuousOn.comp hiM hmaps
    exact hcomp.congr (fun q _hq => rfl)
  exact hG

/-- Local version of `IsLocalFlow.continuousOn_fderiv_along_orbit`. -/
private theorem IsLocalFlow.continuousOn_fderiv_along_orbit_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    (x : E) (hx : x ∈ closedBall x₀ (r : ℝ)) :
    ContinuousOn (fun τ => fderiv ℝ (f τ) (Φ (x, τ))) (Icc tmin tmax) := by
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have horbit : ContinuousOn (fun τ : ℝ => (τ, Φ (x, τ))) (Icc tmin tmax) :=
    continuousOn_id.prodMk (hΦ.orbit_continuousOn x hx)
  have hmaps : MapsTo (fun τ : ℝ => (τ, Φ (x, τ))) (Icc tmin tmax) Ω := by
    intro τ hτ
    exact hΩ_flow x hx τ hτ
  have hcomp := hpfD.continuousOn.comp horbit hmaps
  exact hcomp.congr (fun τ _hτ => rfl)

/-- Local continuity of the time piece `(x,t) ↦ f t (Φ(x,t))` on a
closed-ball/time slab. -/
private theorem continuousOn_timePiece_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)}
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun q : E × ℝ => f q.2 (Φ q))
      (closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hcomp := hf_one.continuousOn.comp hiM hmaps
  exact hcomp.congr (fun q _hq => rfl)

/-- On a compact flow tube contained in an open smoothness domain, the spatial
linearization of the vector field along the flow is uniformly bounded. -/
theorem exists_fderiv_bound_on_flow_tube_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_one : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T ρ : ℝ}
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hρ_le : ρ ≤ (r : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ closedBall x₀ ρ, ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
        ‖fderiv ℝ (f τ) (Φ (x, τ))‖ ≤ M := by
  let K : Set (E × ℝ) := closedBall x₀ ρ ×ˢ Icc (t₀ - T) (t₀ + T)
  let G : E × ℝ → E →L[ℝ] E := fun q => fderiv ℝ (f q.2) (Φ q)
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hK : IsCompact K := (isCompact_closedBall x₀ ρ).prod isCompact_Icc
  have hK_sub : K ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    exact ⟨closedBall_subset_closedBall hρ_le hq.1, hsub hq.2⟩
  have hΦcont : ContinuousOn Φ K := hΦ.continuousOn.mono hK_sub
  let pfD : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (f p.1) p.2
  let iM : E × ℝ → ℝ × E := fun q => (q.2, Φ q)
  have hpfD : ContDiffOn ℝ 0 pfD Ω := by
    simpa [pfD] using
      (contDiffOn_partial_fderiv_of_succ_local
        (f := f) (k := (0 : ℕ∞)) hΩ (by simpa using hf_one))
  have hiM : ContinuousOn iM K := by
    exact continuousOn_snd.prodMk hΦcont
  have hmaps : MapsTo iM K Ω := by
    intro q hq
    exact hΩ_flow q.1 (closedBall_subset_closedBall hρ_le hq.1) q.2 (hsub hq.2)
  have hG : ContinuousOn G K := by
    have hcomp := hpfD.continuousOn.comp hiM hmaps
    exact hcomp.congr (fun q hq => rfl)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx τ hτ
  have hq : (x, τ) ∈ K := ⟨hx, hτ⟩
  exact (hC (x, τ) hq).trans (le_max_left _ _)

end LocalFlowTubeBounds

/-! ## The Hartman `C^∞` theorem -/

section HartmanTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- Local version of the CLM-valued time-piece smoothness theorem. -/
private theorem contDiffOn_timePieceFn_local
    {k : ℕ∞} {U : Set (E × ℝ)} {Ω : Set (ℝ × E)}
    (hf_Ck : ContDiffOn ℝ k (uncurry f) Ω)
    (hΦ_Ck : ContDiffOn ℝ k Φ U)
    (hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω) :
    ContDiffOn ℝ k (timePieceFn f Φ) U := by
  set g : E × ℝ → ℝ × E := fun q => (q.2, Φ q) with hg_def
  have hg : ContDiffOn ℝ k g U :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ k Prod.snd U).prodMk hΦ_Ck
  have horbit : ContDiffOn ℝ k (fun q : E × ℝ => f q.2 (Φ q)) U := by
    have hcomp : ContDiffOn ℝ k (uncurry f ∘ g) U := hf_Ck.comp hg hΩ_map
    exact hcomp.congr (fun _ _ => rfl)
  set S : E →L[ℝ] (ℝ →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ) with hS_def
  have heq : timePieceFn f Φ = S ∘ (fun q : E × ℝ => f q.2 (Φ q)) := by
    funext q
    simp [timePieceFn, S, ContinuousLinearMap.smulRightL]
  rw [heq]
  exact horbit.continuousLinearMap_comp S

/-- Local inductive promotion for Hartman's smooth-dependence proof. -/
private theorem contDiffOn_flow_succ_of_spatial_smooth_local
    {U : Set (E × ℝ)} (hU_open : IsOpen U)
    {Ω : Set (ℝ × E)}
    {k : ℕ∞}
    (hf_Csucc : ContDiffOn ℝ (k + 1) (uncurry f) Ω)
    (hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω)
    (hΦ_diff : DifferentiableOn ℝ Φ U)
    (hΦ_Ck : ContDiffOn ℝ k Φ U)
    {Lsp : E × ℝ → (E →L[ℝ] E)}
    (hLsp_Ck : ContDiffOn ℝ k Lsp U)
    (hLsp_eq : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ U := by
  have hf_Ck : ContDiffOn ℝ k (uncurry f) Ω := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_Csucc.of_le h_le
  have hLti_Ck : ContDiffOn ℝ k (timePieceFn f Φ) U :=
    contDiffOn_timePieceFn_local hf_Ck hΦ_Ck hΩ_map
  exact contDiffOn_succ_of_fderiv_coprod_smooth hU_open hΦ_diff hLsp_Ck hLti_Ck hLsp_eq

/-- Local pointwise `C¹` formula for the flow.

This is the remaining local C¹ frontier under the localized Hartman theorem:
the existing checked version assumes global smoothness of the vector field,
while the normal-coordinate application only supplies smoothness on an open
tube `Ω`. -/
private theorem hasFDerivAt_flow_jointly_at_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasFDerivAt Φ
      (((variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
            hT hM hMT
            (((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow x
              (by
                have hρ_le_r : (ρ : ℝ) ≤ (r : ℝ) := by
                  have hr'_nonneg : 0 ≤ (r' : ℝ) := NNReal.coe_nonneg _
                  linarith
                exact closedBall_subset_closedBall hρ_le_r hx)).mono hsub))
            (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht))).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩))))
      (x, t) := by
  -- Genuine frontier: port `hasFDerivAt_flow_jointly_at` from the global
  -- vector-field hypothesis to the open-domain/tube-contained setting.
  sorry

/-- **Local Hartman smooth-dependence theorem for ODE flows.**

This is the chart-local form needed by normal coordinates: the vector field is
assumed smooth only on an open set `Ω`, and the controlled flow tube is assumed
to stay in `Ω`.  The existing global theorem is the special case `Ω = univ`.

The statement deliberately keeps the same nested small-time and nested-radius
data as the checked global Hartman theorem.  Without these data, the current
`IsLocalFlow` API has no time-subdivision/semigroup structure from which to
recover the smallness condition `M * T_mid < 1`. -/
theorem IsLocalFlow.contDiffOn_top_local
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {Ω : Set (ℝ × E)}
    (hΩ : IsOpen Ω)
    (hf_top : ContDiffOn ℝ ∞ (uncurry f) Ω)
    (hΩ_flow :
      ∀ x ∈ closedBall x₀ (r : ℝ), ∀ τ ∈ Icc tmin tmax,
        (τ, Φ (x, τ)) ∈ Ω)
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
    ContDiffOn ℝ ∞ Φ (ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  apply contDiffOn_top_of_forall_nat
  intro n
  set U := (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
  have hU_open : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax :=
    hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ),
      ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M :=
    fun x hx τ hτ =>
      hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  have hρ_mid_le_r : (ρ_mid : ℝ) ≤ (r : ℝ) :=
    le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r
  have hρ_le_r : (ρ : ℝ) ≤ (r : ℝ) :=
    le_trans (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hρ_out_le_r
  have hU_sub_flow : U ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    refine ⟨?_, ?_⟩
    · exact closedBall_subset_closedBall hρ_le_r (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
    · have ht_out : q.2 ∈ Icc (t₀ - T_out) (t₀ + T_out) :=
        ⟨by linarith [hq.2.1, hT_lt_mid, hT_mid_lt_out],
          by linarith [hq.2.2, hT_lt_mid, hT_mid_lt_out]⟩
      exact hsub ht_out
  have hΩ_map : ∀ q ∈ U, (q.2, Φ q) ∈ Ω := by
    intro q hq
    exact hΩ_flow q.1 (hU_sub_flow hq).1 q.2 (hU_sub_flow hq).2
  have hf_Ck : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞) (uncurry f) Ω :=
    fun k => (hf_top : ContDiffOn ℝ ∞ (uncurry f) Ω).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω := by simpa using hf_Ck 1
  have hΦ_C0 : ContDiffOn ℝ (0 : ℕ∞) Φ U := by
    exact contDiffOn_zero.mpr (hΦ.continuousOn.mono hU_sub_flow)
  have hab : t₀ - T < t₀ + T := by linarith
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  induction n with
  | zero =>
      exact hΦ_C0
  | succ n ih =>
      have hf_Csucc : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry f) Ω := by
        simpa using hf_Ck (n + 1)
      have hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞)
          (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q)) U :=
        contDiffOn_variational_coeff_aux_local hΩ hf_Csucc ih hΩ_map
      set A : E → ℝ → (E →L[ℝ] E) := fun x t => fderiv ℝ (f t) (Φ ⟨x, t⟩)
      have hlinear_Cn : ∀ δ : E, ContDiffOn ℝ (n : ℕ∞)
          (uncurry (linearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ))) U :=
        fun δ => linearODESolution_contDiffOn hab ht₀_mem isOpen_ball n
          (hcoeff_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry A) _)
          (contDiffOn_const : ContDiffOn ℝ (n : ℕ∞) (fun (_ : E) => δ) (ball x₀ (ρ : ℝ)))
      set Lsp : E × ℝ → E →L[ℝ] E :=
        fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)
      have hΦ_diff : DifferentiableOn ℝ Φ U := by
        intro q hq
        obtain ⟨x, t⟩ := q
        rcases hq with ⟨hx, ht⟩
        have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans (mem_ball.mp hx) hρ_lt_mid))
        have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht.1, hT_lt_mid],
            by linarith [ht.2, hT_lt_mid]⟩
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        exact hfd.differentiableAt.differentiableWithinAt
      have hfderiv_coprod : ∀ q ∈ U, fderiv ℝ Φ q = (Lsp q).coprod (timePieceFn f Φ q) := by
        intro q hq
        obtain ⟨x, t⟩ := q
        rcases hq with ⟨hx, ht⟩
        have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans (mem_ball.mp hx) hρ_lt_mid))
        have ht_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht.1, hT_lt_mid],
            by linarith [ht.2, hT_lt_mid]⟩
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        rw [hfd.fderiv]
        change (variationalLinearMapAt hT_mid_pos hM hMT_mid _ _ _).coprod
              ((ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ (x, t))))
          = (Lsp (x, t)).coprod (timePieceFn f Φ (x, t))
        congr 1
        · change _ = (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
          rw [hfd.fderiv]
          exact (ContinuousLinearMap.coprod_comp_inl _ _).symm
      have hLsp_Cn : ContDiffOn ℝ (n : ℕ∞) Lsp U := by
        rw [contDiffOn_clm_apply]
        intro δ
        refine (hlinear_Cn δ).congr (fun q hq => ?_)
        obtain ⟨hx_ball, ht_Ioo⟩ := hq
        have hx' : dist q.1 x₀ < ↑ρ := mem_ball.mp hx_ball
        have hx_cb_mid : q.1 ∈ closedBall x₀ (ρ_mid : ℝ) :=
          mem_closedBall.mpr (le_of_lt (lt_trans hx' hρ_lt_mid))
        have hx_cb_r : q.1 ∈ closedBall x₀ (r : ℝ) :=
          closedBall_subset_closedBall hρ_mid_le_r hx_cb_mid
        have ht_mid : q.2 ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
          ⟨by linarith [ht_Ioo.1, hT_lt_mid],
            by linarith [ht_Ioo.2, hT_lt_mid]⟩
        have hA_cont_x : ContinuousOn (A q.1) (Icc (t₀ - T_mid) (t₀ + T_mid)) := by
          simpa [A] using
            ((hΦ.continuousOn_fderiv_along_orbit_local hΩ hf_C1 hΩ_flow q.1 hx_cb_r).mono
              hsub_mid)
        have hA_bd_x : ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid), ‖A q.1 τ‖ ≤ M := by
          intro τ hτ
          simpa [A] using hA_bd_mid q.1 hx_cb_mid τ hτ
        have ht_Icc : q.2 ∈ Icc (t₀ - T_mid) (t₀ + T_mid) := Ioo_subset_Icc_self ht_mid
        have hfd := hasFDerivAt_flow_jointly_at_local
          (f := f) (t₀ := t₀) (x₀ := x₀) (r := r) (tmin := tmin) (tmax := tmax)
          (Φ := Φ) hΦ hΩ hf_C1 hΩ_flow hT_mid_pos hM hMT_mid hsub_mid
          hr' hρρ' hA_bd_mid hx_cb_mid ht_mid
        have hLsp_eq_vlm : Lsp q =
            variationalLinearMapAt hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x ht_Icc := by
          change (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) = _
          conv_lhs => rw [show q = (q.1, q.2) from Prod.mk.eta.symm]
          rw [hfd.fderiv]
          exact ContinuousLinearMap.coprod_comp_inl _ _
        have hvlm_eq := variationalLinearMapAt_apply hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x
          ht_Icc δ
        have hvsf := variationalSolutionFun_isSolution hT_mid_pos hM hMT_mid hA_cont_x hA_bd_x δ
        have hA_cont_Ioo : ContinuousOn (A q.1) (Ioo (t₀ - T) (t₀ + T)) :=
          hA_cont_x.mono (fun s hs => Ioo_subset_Icc_self
            (⟨by linarith [hs.1, hT_lt_mid],
              by linarith [hs.2, hT_lt_mid]⟩ : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid)))
        have hA_joint_cont : ContinuousOn (uncurry A) U := hcoeff_Cn.continuousOn
        have h_exists : HasLinearODESolution A (t₀ - T) (t₀ + T) t₀ (fun _ => δ) q.1 :=
          hasLinearODESolution_of_continuousOn hab ht₀_mem isOpen_ball hA_joint_cont (mem_ball.mpr hx')
        have h_uniq := linearODE_unique_on_Ioo (G := E) ht₀_mem hA_cont_Ioo
          (fun s hs => by
            have hs_mid : s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
              ⟨by linarith [hs.1, hT_lt_mid],
                by linarith [hs.2, hT_lt_mid]⟩
            exact (hvsf.2 s (Ioo_subset_Icc_self hs_mid)).hasDerivAt (Icc_mem_nhds_iff.mpr hs_mid))
          (fun s hs => linearODESolution_hasDerivAt_of_hasSolution A (t₀ - T) (t₀ + T) t₀
            (fun _ => δ) h_exists hs)
          (by rw [hvsf.1, linearODESolution_init])
        simp only [hLsp_eq_vlm, hvlm_eq, uncurry]
        have h_eq := h_uniq ht_Ioo
        dsimp at h_eq
        exact h_eq
      simpa using
        contDiffOn_flow_succ_of_spatial_smooth_local
          (f := f) (Φ := Φ) hU_open hf_Csucc hΩ_map hΦ_diff ih hLsp_Cn hfderiv_coprod

/-- **Hartman smooth-dependence theorem for ODE flows.**

If the vector field `f : ℝ → E → E` is jointly `C^∞` and `Φ` is a local
Picard–Lindelöf flow of `f`, then `Φ` is jointly `C^∞` on the strictly interior open
neighbourhood `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`. -/
theorem IsLocalFlow.contDiffOn_top
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
      contDiffOn_variational_coeff_aux hf_Csucc ih
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

end RicciFlower.Analysis.ODE.Flow

end
