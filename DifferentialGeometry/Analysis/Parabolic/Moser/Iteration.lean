import DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration.Recurrence


noncomputable section

open Filter Metric

namespace DifferentialGeometry.Analysis.Parabolic.Moser

variable (n : ℕ) [NeZero n]

def parabolicMoserGain : ℝ :=
  1 + 2 / (n : ℝ)

def parabolicMoserDecay : ℝ :=
  (n : ℝ) / ((n : ℝ) + 2)

def parabolicMoserExponent (p₀ : ℝ) (k : ℕ) : ℝ :=
  p₀ * parabolicMoserGain n ^ k

theorem one_lt_parabolicMoserGain :
    1 < parabolicMoserGain n := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiv : 0 < (2 : ℝ) / (n : ℝ) := div_pos (by norm_num) hn
  simp only [parabolicMoserGain]
  linarith

theorem parabolicMoserGain_pos :
    0 < parabolicMoserGain n :=
  (zero_lt_one.trans (one_lt_parabolicMoserGain n))

theorem parabolicMoserDecay_pos :
    0 < parabolicMoserDecay n := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [parabolicMoserDecay]
  positivity

theorem parabolicMoserDecay_lt_one :
    parabolicMoserDecay n < 1 := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [parabolicMoserDecay]
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem parabolicMoserDecay_eq_inv_gain :
    parabolicMoserDecay n = (parabolicMoserGain n)⁻¹ := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  simp only [parabolicMoserDecay, parabolicMoserGain]
  field_simp

omit [NeZero n] in
theorem parabolicMoserExponent_zero (p₀ : ℝ) :
    parabolicMoserExponent n p₀ 0 = p₀ := by
  simp [parabolicMoserExponent]

omit [NeZero n] in
theorem parabolicMoserExponent_succ (p₀ : ℝ) (k : ℕ) :
    parabolicMoserExponent n p₀ (k + 1) =
      parabolicMoserGain n * parabolicMoserExponent n p₀ k := by
  rw [parabolicMoserExponent, pow_succ, parabolicMoserExponent]
  ring

theorem parabolicMoserExponent_pos {p₀ : ℝ} (hp₀ : 0 < p₀) (k : ℕ) :
    0 < parabolicMoserExponent n p₀ k := by
  rw [parabolicMoserExponent]
  exact mul_pos hp₀ (pow_pos (parabolicMoserGain_pos n) k)

theorem parabolicMoserExponent_tendsto_atTop {p₀ : ℝ} (hp₀ : 0 < p₀) :
    Tendsto (parabolicMoserExponent n p₀) atTop atTop := by
  simpa only [parabolicMoserExponent, mul_comm] using
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_parabolicMoserGain n)).atTop_mul_const hp₀

theorem inv_parabolicMoserExponent {p₀ : ℝ} (hp₀ : 0 < p₀) (k : ℕ) :
    1 / parabolicMoserExponent n p₀ k =
      parabolicMoserDecay n ^ k / p₀ := by
  rw [parabolicMoserExponent, parabolicMoserDecay_eq_inv_gain]
  have hgain : parabolicMoserGain n ≠ 0 := (parabolicMoserGain_pos n).ne'
  rw [inv_pow]
  field_simp [hp₀.ne', pow_ne_zero k hgain]

omit [NeZero n] in
theorem superlinear_recurrence_tendsto_zero
    {Y : ℕ → ℝ} {C B alpha : ℝ}
    (hC : 0 < C) (hB : 1 < B) (halpha : 0 < alpha)
    (hY_nonneg : ∀ k, 0 ≤ Y k)
    (hrec : ∀ k, Y (k + 1) ≤ C * B ^ k * Y k ^ (1 + alpha))
    (hsmall : Y 0 ≤ C ^ (-(1 : ℝ) / alpha) * B ^ (-(1 : ℝ) / alpha ^ 2)) :
    Tendsto Y atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := DeGiorgi.deGiorgi_recurrence_closeout
    hC hB halpha hY_nonneg hrec hsmall epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hY_nonneg k)]
  exact hN k hk

end DifferentialGeometry.Analysis.Parabolic.Moser

end
