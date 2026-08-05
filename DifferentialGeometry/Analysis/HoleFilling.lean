import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open Filter

namespace DifferentialGeometry.Analysis

theorem geometric_hole_filling
    {X : ℕ → ℝ} {theta A B : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (hB : 1 ≤ B) (hA : 0 ≤ A)
    (hthetaB : theta * B < 1)
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + A * B ^ k) :
    X 0 ≤ A / (1 - theta * B) := by
  have htheta_one : theta < 1 := by
    calc
      theta = theta * 1 := (mul_one theta).symm
      _ ≤ theta * B := mul_le_mul_of_nonneg_left hB htheta
      _ < 1 := hthetaB
  have hratio_nonneg : 0 ≤ theta * B :=
    mul_nonneg htheta (le_trans zero_le_one hB)
  have hratio_summable : Summable (fun k : ℕ ↦ (theta * B) ^ k) :=
    summable_geometric_of_lt_one hratio_nonneg hthetaB
  obtain ⟨K, hK⟩ := hX_bdd
  have hfinite : ∀ m : ℕ,
      X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := hm
          _ ≤ theta ^ m * (theta * X (m + 1) + A * B ^ m) +
                A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hstep m) (pow_nonneg htheta m)) le_rfl
          _ = theta ^ (m + 1) * X (m + 1) +
                A * ∑ k ∈ Finset.range (m + 1), (theta * B) ^ k := by
            rw [Finset.sum_range_succ, pow_succ theta, mul_pow]
            ring
  have hbound : ∀ m : ℕ,
      X 0 ≤ theta ^ m * K + A * (1 - theta * B)⁻¹ := by
    intro m
    calc
      X 0 ≤ theta ^ m * X m + A * ∑ k ∈ Finset.range m, (theta * B) ^ k :=
        hfinite m
      _ ≤ theta ^ m * K + A * ∑ k ∈ Finset.range m, (theta * B) ^ k := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hK (Set.mem_range_self m)) (pow_nonneg htheta m)) le_rfl
      _ ≤ theta ^ m * K + A * ∑' k : ℕ, (theta * B) ^ k := by
        gcongr
        exact hratio_summable.sum_le_tsum (Finset.range m)
          (fun k _ ↦ pow_nonneg hratio_nonneg k)
      _ = theta ^ m * K + A * (1 - theta * B)⁻¹ := by
        rw [tsum_geometric_of_lt_one hratio_nonneg hthetaB]
  have htendsto : Tendsto
      (fun m : ℕ ↦ theta ^ m * K + A * (1 - theta * B)⁻¹)
      atTop (nhds (A * (1 - theta * B)⁻¹)) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta_one).mul_const K).add_const
        (A * (1 - theta * B)⁻¹)
  have hlimit : X 0 ≤ A * (1 - theta * B)⁻¹ :=
    ge_of_tendsto htendsto (Filter.Eventually.of_forall hbound)
  simpa only [div_eq_mul_inv] using hlimit

theorem summable_hole_filling
    {X cost : ℕ → ℝ} {theta : ℝ}
    (hX_bdd : BddAbove (Set.range X))
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hcost : Summable (fun k : ℕ ↦ theta ^ k * cost k))
    (hstep : ∀ k, X k ≤ theta * X (k + 1) + cost k) :
    X 0 ≤ ∑' k : ℕ, theta ^ k * cost k := by
  obtain ⟨K, hK⟩ := hX_bdd
  have hfinite : ∀ m : ℕ,
      X 0 ≤ theta ^ m * X m + ∑ k ∈ Finset.range m, theta ^ k * cost k := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X 0 ≤ theta ^ m * X m +
              ∑ k ∈ Finset.range m, theta ^ k * cost k := hm
          _ ≤ theta ^ m * (theta * X (m + 1) + cost m) +
              ∑ k ∈ Finset.range m, theta ^ k * cost k := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hstep m) (pow_nonneg htheta m)) le_rfl
          _ = theta ^ (m + 1) * X (m + 1) +
              ∑ k ∈ Finset.range (m + 1), theta ^ k * cost k := by
            rw [Finset.sum_range_succ, pow_succ]
            ring
  have hbound : ∀ m : ℕ,
      X 0 ≤ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k := by
    intro m
    calc
      X 0 ≤ theta ^ m * X m +
          ∑ k ∈ Finset.range m, theta ^ k * cost k := hfinite m
      _ ≤ theta ^ m * K +
          ∑ k ∈ Finset.range m, theta ^ k * cost k := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hK (Set.mem_range_self m))
            (pow_nonneg htheta m)) le_rfl
      _ ≤ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k := by
        gcongr
        exact hcost.sum_le_tsum (Finset.range m)
          (fun k _ ↦ mul_nonneg (pow_nonneg htheta k) (hcost_nonneg k))
  have htendsto : Tendsto
      (fun m : ℕ ↦ theta ^ m * K + ∑' k : ℕ, theta ^ k * cost k)
      atTop (nhds (∑' k : ℕ, theta ^ k * cost k)) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta_one).mul_const K).add_const
        (∑' k : ℕ, theta ^ k * cost k)
  exact ge_of_tendsto htendsto (Filter.Eventually.of_forall hbound)

end DifferentialGeometry.Analysis

end
