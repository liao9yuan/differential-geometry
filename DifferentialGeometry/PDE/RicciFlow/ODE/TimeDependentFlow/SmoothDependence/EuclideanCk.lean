import DifferentialGeometry.Analysis.ODE.FlowCkVariational

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

/-! ## H1 — finite-`C^k` clean unconditional Euclidean smooth dependence (headline) -/

theorem h1_exists_isLocalFlow_contDiffOn_Ck
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {k : ℕ∞} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (ρ : ℝ) (T : ℝ), 0 < ρ ∧ 0 < T ∧ ρ ≤ (r : ℝ) ∧ T ≤ ε ∧
        ContDiffOn ℝ k Φ (Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := sorry

/-! ## Pending proof-target child — H1 uniform-fderiv-bound -/

-- [H1: uniform-fderiv-bound]
theorem exists_uniform_norm_fderiv_le_on_flow_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {ε : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ)
    (hf_C1 : ContDiffOn ℝ 1 (Function.uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Metric.closedBall x₀ (r : ℝ), ∀ τ ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := sorry

-- [H1: shrink-variational-projection]
theorem stub_isVariationalFlowProjection_mono_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
    {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T T' : ℝ} {ρ ρ' : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k)
    (hT' : T' ≤ T) (hρ' : (ρ' : ℝ) ≤ (ρ : ℝ)) :
    IsVariationalFlowProjection hΦ T' ρ' Y k := by
  -- The smaller box `ball x₀ ρ' ×ˢ Ioo (t₀ - T') (t₀ + T')` is contained in the
  -- larger box `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`: the radial factor shrinks via
  -- `ball_subset_ball` (since `ρ' ≤ ρ`) and the time factor shrinks via
  -- `Ioo_subset_Ioo` (since `t₀ - T ≤ t₀ - T'` and `t₀ + T' ≤ t₀ + T`, both from `T' ≤ T`).
  have hbox :
      (Metric.ball x₀ (ρ' : ℝ)) ×ˢ Set.Ioo (t₀ - T') (t₀ + T') ⊆
        (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T) :=
    Set.prod_mono (Metric.ball_subset_ball hρ')
      (Set.Ioo_subset_Ioo (by linarith) (by linarith))
  exact
    { contDiffOn := hY.contDiffOn.mono hbox
      fderiv_eq := fun q hq => hY.fderiv_eq q (hbox hq) }

/-! ## Pending grandchild (Stage C round-1 output; round-2 expansion target) -/

-- [under uniform-fderiv-bound]
theorem linearizationNorm_continuousOn_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {ε : ℝ} {Φ : E × ℝ → E}
    (hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)))
    (horbit : ContinuousOn (fun q : E × ℝ => (q.2, Φ q))
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε))) :
    ContinuousOn (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖)
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) := by
  -- Step 1: compose the partial Fréchet derivative (continuous on `univ`) with the
  -- orbit map `q ↦ (q.2, Φ q)` (continuous on the box) to get continuity of the full
  -- composite `q ↦ fderiv ℝ (f q.2) (Φ q)` on the box.  The `MapsTo … univ` side goal
  -- is trivial.
  have hfull :
      ContinuousOn (fun q : E × ℝ => fderiv ℝ (f q.2) (Φ q))
        (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) :=
    hpartial.comp horbit (fun _ _ => Set.mem_univ _)
  -- Step 2: post-compose with the (globally) continuous norm map.
  exact continuous_norm.comp_continuousOn hfull

end DifferentialGeometry.PDE.RicciFlow.ODE
