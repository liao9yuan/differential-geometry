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
      (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))) := sorry

-- [H4: augmented-orbit-param-component-constant]
theorem h4_orbit_param_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : ℝ → P → E → E} {t₀ : ℝ} {z₀ : E × P} {r : ℝ≥0} {ε : ℝ}
    {Ψ : (E × P) × ℝ → E × P}
    (hΨ : IsLocalFlow (fun (t : ℝ) (z : E × P) => ((f t z.2 z.1, (0 : P)) : E × P))
      t₀ z₀ r (t₀ - ε) (t₀ + ε) Ψ) :
    ∀ z ∈ Metric.closedBall z₀ (r : ℝ), ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      (Ψ (z, t)).2 = z.2 := sorry

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
        HasDerivAt (fun s => (Ψ ((x, lam), s)).1) (f t lam (Ψ ((x, lam), t)).1) t := sorry

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
    ContDiff ℝ ∞ (fun w : P × E × ℝ => (((w.2.1, w.1) : E × P), w.2.2)) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
