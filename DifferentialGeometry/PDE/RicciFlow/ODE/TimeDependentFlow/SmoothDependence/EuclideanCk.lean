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
    IsVariationalFlowProjection hΦ T' ρ' Y k := sorry

/-! ## Pending grandchild (Stage C round-1 output; round-2 expansion target) -/

-- [under uniform-fderiv-bound]
theorem linearizationNorm_continuousOn_box
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {ε : ℝ} {Φ : E × ℝ → E}
    (hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)))
    (horbit : ContinuousOn (fun q : E × ℝ => (q.2, Φ q))
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε))) :
    ContinuousOn (fun q : E × ℝ => ‖fderiv ℝ (f q.2) (Φ q)‖)
      (Metric.closedBall x₀ (r : ℝ) ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
