import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

theorem pointwise_oscillation_decay_of_complementary_harnack
    {X : Type*} {early late : Set X} (hearly : early.Nonempty)
    (u : X → ℝ) (m M F : ℝ) (hF : 1 ≤ F)
    (hupper : ∀ e ∈ early, ∀ y ∈ late,
      M - u e ≤ F * (M - u y))
    (hlower : ∀ e ∈ early, ∀ y ∈ late,
      u e - m ≤ F * (u y - m)) :
    ∀ x ∈ late, ∀ y ∈ late,
      u y - u x ≤ (1 - 1 / F) * (M - m) := by
  obtain ⟨e, he⟩ := hearly
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  intro x hx y hy
  have hsum := add_le_add (hupper e he y hy) (hlower e he x hx)
  have hraw : M - m ≤ F * ((M - m) - (u y - u x)) := by
    convert hsum using 1 <;> ring
  have hdiv : (M - m) / F ≤ (M - m) - (u y - u x) := by
    apply (div_le_iff₀ hFpos).2
    simpa only [mul_comm] using hraw
  calc
    u y - u x ≤ (M - m) - (M - m) / F := by linarith
    _ = (1 - 1 / F) * (M - m) := by ring

theorem geometric_oscillation_decay
    (oscillation : ℕ → ℝ) {theta : ℝ}
    (htheta : 0 ≤ theta)
    (hstep : ∀ k, oscillation (k + 1) ≤ theta * oscillation k) :
    ∀ k, oscillation k ≤ theta ^ k * oscillation 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        oscillation (k + 1) ≤ theta * oscillation k := hstep k
        _ ≤ theta * (theta ^ k * oscillation 0) :=
          mul_le_mul_of_nonneg_left ih htheta
        _ = theta ^ (k + 1) * oscillation 0 := by ring

end DifferentialGeometry.Analysis.Parabolic.Harnack
