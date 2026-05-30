import DifferentialGeometry.Analysis.ODE.FlowC1

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

/-! ## H4 — smooth dependence on parameters (headline) -/

theorem h4_exists_isLocalFlow_param_contDiffOn_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {x₀ : E} {lam₀ : P}
    (hf : ContDiff ℝ ∞ (fun q : ℝ × P × E => f q.1 q.2.1 q.2.2)) :
    ∃ (ρP ρE ε : ℝ) (Φ : P × E × ℝ → E),
      0 < ρP ∧ 0 < ρE ∧ 0 < ε ∧
      (∀ lam ∈ Metric.ball lam₀ ρP, ∀ x ∈ Metric.ball x₀ ρE, Φ (lam, x, t₀) = x) ∧
      (∀ lam ∈ Metric.ball lam₀ ρP, ∀ x ∈ Metric.ball x₀ ρE,
          ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s => Φ (lam, x, s)) (f t lam (Φ (lam, x, t))) t) ∧
      ContDiffOn ℝ ∞ Φ
        (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - ε) (t₀ + ε)) := sorry

/-! ## Pending proof-target children — Euclidean (H4) -/

-- [H4: augmented-field-contDiff-top]
theorem h4_augmented_field_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : ℝ → P → E → E} (hf : ContDiff ℝ ∞ (fun q : ℝ × P × E => f q.1 q.2.1 q.2.2)) :
    ContDiff ℝ ∞ (Function.uncurry
      (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))) := by
  -- The uncurried augmented field `g q = (f q.1 q.2.2 q.2.1, 0)` is a pair.
  -- First component: `hf` precomposed with the linear coordinate reshuffle
  -- `q ↦ (q.1, q.2.2, q.2.1)`; second component: the constant `0`.
  have hshuffle :
      ContDiff ℝ ∞ (fun q : ℝ × (E × P) => (q.1, q.2.2, q.2.1) : _ → ℝ × P × E) :=
    contDiff_fst.prodMk ((contDiff_snd.comp contDiff_snd).prodMk
      (contDiff_fst.comp contDiff_snd))
  have hfst : ContDiff ℝ ∞ (fun q : ℝ × (E × P) => f q.1 q.2.2 q.2.1) :=
    hf.comp hshuffle
  exact hfst.prodMk contDiff_const

-- [H4: augmented-orbit-param-component-constant]
theorem h4_orbit_param_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {z₀ : E × P} {r : ℝ≥0} {ε : ℝ}
    {Ψ : (E × P) × ℝ → E × P}
    (hΨ : IsLocalFlow (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))
      t₀ z₀ r (t₀ - ε) (t₀ + ε) Ψ) :
    ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2 := by
  intro z hz t ht
  -- The P-component of the orbit, as a function of time.
  set g : ℝ → P := fun u => (Ψ (z, u)).2 with hg
  -- STEP A (orbit-snd-hasDerivWithinAt-zero): zero within-derivative on the closed interval.
  -- The augmented field's P-component is the literal `0`, and `snd : E × P →L[ℝ] P`
  -- projects the orbit derivative onto that component.
  have hA : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt g (0 : P) (Set.Icc (t₀ - ε) (t₀ + ε)) s := by
    intro s hs
    have horbit := hΨ.hasDerivWithinAt z hz s hs
    have hcomp :=
      (ContinuousLinearMap.snd ℝ E P).hasFDerivAt.comp_hasDerivWithinAt s horbit
    simpa [g, Function.comp, ContinuousLinearMap.coe_snd'] using hcomp
  -- STEP B (orbit-snd-right-deriv-zero): upgrade to zero right-derivative on `Ico`.
  have hB : ∀ s ∈ Set.Ico (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt g (0 : P) (Set.Ici s) s := by
    intro s hs
    exact (hA s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  -- STEP C (orbit-snd-continuousOn): continuity on the closed interval.
  have hC : ContinuousOn g (Set.Icc (t₀ - ε) (t₀ + ε)) :=
    continuous_snd.comp_continuousOn (hΨ.orbit_continuousOn z hz)
  -- Mean-value constancy: `g` is constant on the interval, equal to `g (t₀ - ε)`.
  have hconst := constant_of_has_deriv_right_zero hC hB
  have ht' : g t = g (t₀ - ε) := hconst t ht
  have ht₀' : g t₀ = g (t₀ - ε) := hconst t₀ hΨ.t₀_mem_Icc
  -- Initial value of the orbit: `g t₀ = (Ψ (z, t₀)).2 = z.2`.
  have hinit : g t₀ = z.2 := by
    simp only [g]
    rw [hΨ.apply_initial z hz]
  change g t = z.2
  rw [ht', ← ht₀', hinit]

-- [H4: projected-flow-ode-and-initial]
theorem h4_projected_ode_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {z₀ : E × P} {r : ℝ≥0} {ε : ℝ}
    {Ψ : (E × P) × ℝ → E × P}
    (hΨ : IsLocalFlow (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))
      t₀ z₀ r (t₀ - ε) (t₀ + ε) Ψ)
    (hinv : ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2) :
    ∀ (x : E) (lam : P), ((x, lam) : E × P) ∈ Metric.closedBall z₀ (r : ℝ) →
      (Ψ ((x, lam), t₀)).1 = x ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s => (Ψ ((x, lam), s)).1) (f t lam (Ψ ((x, lam), t)).1) t := by
  intro x lam hz
  set z : E × P := (x, lam) with hzdef
  refine ⟨?_, ?_⟩
  · -- Initial value: `Ψ (z, t₀) = z`, project to the first component.
    have hinit : Ψ (z, t₀) = z := hΨ.apply_initial z hz
    calc (Ψ (z, t₀)).1 = z.1 := congrArg Prod.fst hinit
      _ = x := rfl
  · -- ODE for the first component on the open time interval.
    intro t ht
    have htIcc : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := Set.Ioo_subset_Icc_self ht
    -- The orbit solves `ż = (f t z.2 z.1, 0)` within `Icc`.
    have horbit := hΨ.hasDerivWithinAt z hz t htIcc
    -- `Icc` is a neighbourhood of the interior point `t`, so upgrade to `HasDerivAt`.
    have horbitAt : HasDerivAt (fun s => Ψ (z, s))
        ((f t (Ψ (z, t)).2 (Ψ (z, t)).1, (0 : P)) : E × P) t :=
      horbit.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    -- Project the pair-valued derivative onto its first component via `fst`.
    have hfst :=
      (ContinuousLinearMap.fst ℝ E P).hasFDerivAt.comp_hasDerivAt t horbitAt
    -- The parameter component of the orbit is fixed at `z.2 = lam` by `hinv`.
    have hpar : (Ψ (z, t)).2 = lam := by
      have := hinv z hz t htIcc
      simpa [hzdef] using this
    simpa [Function.comp, ContinuousLinearMap.coe_fst', hpar] using hfst

-- [H4: projected-flow-contDiffOn-top]
theorem h4_projected_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {t₀ : ℝ} {z₀ : E × P} {Ψ : (E × P) × ℝ → E × P} {ρ T : ℝ}
    (hΨsmooth : ContDiffOn ℝ ∞ Ψ (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    {lam₀ : P} {x₀ : E} {ρP ρE : ℝ}
    (hmaps : Set.MapsTo (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2))
      (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - T) (t₀ + T))
      (Metric.ball z₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ ∞ (fun w : P × E × ℝ => (Ψ ((w.2.1, w.1), w.2.2)).1)
      (Metric.ball lam₀ ρP ×ˢ Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := sorry

/-! ## Pending grandchild (under projected-flow-contDiffOn-top) -/

-- [under projected-flow-contDiffOn-top]
theorem reindex_contDiff_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ContDiff ℝ ∞ (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2)) :=
  ((contDiff_snd.fst).prodMk contDiff_fst).prodMk contDiff_snd.snd

end DifferentialGeometry.PDE.RicciFlow.ODE
