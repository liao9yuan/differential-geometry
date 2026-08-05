import DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration.Recurrence
import DifferentialGeometry.Analysis.Integration.LpLimit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed


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

def moserIterationCost (theta a b : ℝ) (k : ℕ) : ℝ :=
  (a + b * k) * theta ^ k

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
theorem moserIterationCost_nonneg
    {theta a b : ℝ} (htheta : 0 ≤ theta) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ moserIterationCost theta a b k := by
  exact mul_nonneg (add_nonneg ha (mul_nonneg hb (Nat.cast_nonneg k)))
    (pow_nonneg htheta k)

omit [NeZero n] in
theorem summable_moserIterationCost
    {theta a b : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta < 1) :
    Summable (moserIterationCost theta a b) := by
  have htheta_norm : ‖theta‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg htheta] using htheta_one
  have hgeom : Summable (fun k : ℕ => theta ^ k) :=
    summable_geometric_of_lt_one htheta htheta_one
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * theta ^ k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 htheta_norm
    simpa only [pow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg htheta _))] using h
  refine ((hgeom.mul_left a).add (hlinear.mul_left b)).congr ?_
  intro k
  simp only [moserIterationCost]
  ring

omit [NeZero n] in
theorem additive_iteration_le_initial_add_tsum
    {X cost : ℕ → ℝ}
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ X k + cost k) (k : ℕ) :
    X k ≤ X 0 + ∑' j, cost j := by
  have hfinite : ∀ m : ℕ, X m ≤ X 0 + ∑ j ∈ Finset.range m, cost j := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          X (m + 1) ≤ X m + cost m := hstep m
          _ ≤ (X 0 + ∑ j ∈ Finset.range m, cost j) + cost m := by linarith
          _ = X 0 + ∑ j ∈ Finset.range (m + 1), cost j := by
            rw [Finset.sum_range_succ]
            ring
  refine (hfinite k).trans ?_
  gcongr
  exact hcost.sum_le_tsum (Finset.range k) (fun j _ => hcost_nonneg j)

omit [NeZero n] in
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
  have hratio_nonneg : 0 ≤ theta * B := mul_nonneg htheta (le_trans zero_le_one hB)
  have hratio_summable : Summable (fun k : ℕ => (theta * B) ^ k) :=
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
          (fun k _ => pow_nonneg hratio_nonneg k)
      _ = theta ^ m * K + A * (1 - theta * B)⁻¹ := by
        rw [tsum_geometric_of_lt_one hratio_nonneg hthetaB]
  have htendsto : Tendsto
      (fun m : ℕ => theta ^ m * K + A * (1 - theta * B)⁻¹)
      atTop (nhds (A * (1 - theta * B)⁻¹)) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta_one).mul_const K).add_const
        (A * (1 - theta * B)⁻¹)
  have hlimit : X 0 ≤ A * (1 - theta * B)⁻¹ :=
    ge_of_tendsto htendsto (Filter.Eventually.of_forall hbound)
  simpa only [div_eq_mul_inv] using hlimit

omit [NeZero n] in
theorem multiplicative_iteration_bound
    {X cost : ℕ → ℝ}
    (hX_zero : 0 ≤ X 0)
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ Real.exp (cost k) * X k) (k : ℕ) :
    X k ≤ Real.exp (∑' j, cost j) * X 0 := by
  have hfinite : ∀ m : ℕ,
      X m ≤ Real.exp (∑ j ∈ Finset.range m, cost j) * X 0 := by
    intro m
    induction m with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, one_mul]
        exact le_rfl
    | succ m hm =>
        calc
          X (m + 1) ≤ Real.exp (cost m) * X m := hstep m
          _ ≤ Real.exp (cost m) *
              (Real.exp (∑ j ∈ Finset.range m, cost j) * X 0) := by
            gcongr
          _ = Real.exp (∑ j ∈ Finset.range (m + 1), cost j) * X 0 := by
            rw [Finset.sum_range_succ, Real.exp_add]
            ring
  refine (hfinite k).trans ?_
  gcongr
  exact hcost.sum_le_tsum (Finset.range k) (fun j _ => hcost_nonneg j)

omit [NeZero n] in
theorem bddAbove_range_of_multiplicative_iteration
    {X cost : ℕ → ℝ}
    (hX_zero : 0 ≤ X 0)
    (hcost : Summable cost) (hcost_nonneg : ∀ k, 0 ≤ cost k)
    (hstep : ∀ k, X (k + 1) ≤ Real.exp (cost k) * X k) :
    BddAbove (Set.range X) := by
  refine ⟨Real.exp (∑' j, cost j) * X 0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact multiplicative_iteration_bound hX_zero hcost hcost_nonneg hstep k

omit [NeZero n] in
theorem moser_iteration_bound
    {X : ℕ → ℝ} {theta a b : ℝ}
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) (k : ℕ) :
    X k ≤ Real.exp (∑' j, moserIterationCost theta a b j) * X 0 := by
  exact multiplicative_iteration_bound hX_zero
    (summable_moserIterationCost htheta htheta_one)
    (moserIterationCost_nonneg htheta ha hb) hstep k

omit [NeZero n] in
theorem moser_iteration_bddAbove
    {X : ℕ → ℝ} {theta a b : ℝ}
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    BddAbove (Set.range X) := by
  exact bddAbove_range_of_multiplicative_iteration hX_zero
    (summable_moserIterationCost htheta htheta_one)
    (moserIterationCost_nonneg htheta ha hb) hstep

theorem normalized_moser_step
    {p₀ C A L L' : ℝ}
    (hp₀ : 0 < p₀) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') (k : ℕ)
    (hstep : L' ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n) :
    L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) ≤
      Real.exp
          (moserIterationCost (parabolicMoserDecay n)
            ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
            (Real.log 16 / p₀) k) *
        L ^ (1 / parabolicMoserExponent n p₀ k) := by
  have hp : 0 < parabolicMoserExponent n p₀ k :=
    parabolicMoserExponent_pos n hp₀ k
  have hp' : 0 < parabolicMoserExponent n p₀ (k + 1) :=
    parabolicMoserExponent_pos n hp₀ (k + 1)
  have hgain : 0 < parabolicMoserGain n := parabolicMoserGain_pos n
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hApos : 0 < A := zero_lt_one.trans_le hA
  by_cases hLzero : L = 0
  · have hL'le : L' ≤ 0 := by
      simpa only [hLzero, mul_zero, Real.zero_rpow hgain.ne', mul_zero] using hstep
    have hL'zero : L' = 0 := le_antisymm hL'le hL'
    rw [hL'zero, hLzero, Real.zero_rpow (one_div_ne_zero hp'.ne'),
      Real.zero_rpow (one_div_ne_zero hp.ne'), mul_zero]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
    have hfactor_pos : 0 < A * 16 ^ k :=
      mul_pos hApos (pow_pos (by norm_num) k)
    have hbase_pos : 0 < (A * 16 ^ k) * L := mul_pos hfactor_pos hLpos
    have htotal_nonneg : 0 ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n :=
      mul_nonneg hCpos.le (Real.rpow_nonneg hbase_pos.le _)
    have hroot := Real.rpow_le_rpow hL' hstep (by positivity :
      0 ≤ 1 / parabolicMoserExponent n p₀ (k + 1))
    have hexponent :
        parabolicMoserGain n *
            (1 / parabolicMoserExponent n p₀ (k + 1)) =
          1 / parabolicMoserExponent n p₀ k := by
      rw [parabolicMoserExponent_succ]
      field_simp [hgain.ne', hp.ne']
    have hprefactor :
        C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
              A ^ (1 / parabolicMoserExponent n p₀ k) *
              (16 ^ k : ℝ) ^ (1 / parabolicMoserExponent n p₀ k) =
          Real.exp
            (moserIterationCost (parabolicMoserDecay n)
              ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
              (Real.log 16 / p₀) k) := by
      rw [Real.rpow_def_of_pos hCpos, Real.rpow_def_of_pos hApos,
        Real.rpow_def_of_pos (pow_pos (by norm_num) k), ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      rw [inv_parabolicMoserExponent n hp₀ k,
        inv_parabolicMoserExponent n hp₀ (k + 1), pow_succ, Real.log_pow]
      simp only [moserIterationCost]
      ring
    calc
      L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) ≤
          (C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n) ^
            (1 / parabolicMoserExponent n p₀ (k + 1)) := hroot
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          (((A * 16 ^ k) * L) ^ parabolicMoserGain n) ^
            (1 / parabolicMoserExponent n p₀ (k + 1)) := by
        rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hbase_pos.le _)]
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          ((A * 16 ^ k) * L) ^
            (1 / parabolicMoserExponent n p₀ k) := by
        rw [← Real.rpow_mul hbase_pos.le, hexponent]
      _ = C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
            A ^ (1 / parabolicMoserExponent n p₀ k) *
            (16 ^ k : ℝ) ^ (1 / parabolicMoserExponent n p₀ k) *
            L ^ (1 / parabolicMoserExponent n p₀ k) := by
        rw [Real.mul_rpow hfactor_pos.le hLpos.le,
          Real.mul_rpow hApos.le (pow_nonneg (by norm_num) k)]
        ring
      _ = Real.exp
            (moserIterationCost (parabolicMoserDecay n)
              ((parabolicMoserDecay n * Real.log C + Real.log A) / p₀)
              (Real.log 16 / p₀) k) *
          L ^ (1 / parabolicMoserExponent n p₀ k) := by
        rw [hprefactor]

theorem local_boundedness_on_open_of_moser_iteration
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {μ : MeasureTheory.Measure Y} {U : Set Y}
    [MeasureTheory.IsFiniteMeasure (μ.restrict U)] [μ.IsOpenPosMeasure]
    {f : Y → ℝ} {X : ℕ → ℝ} {p₀ theta a b : ℝ}
    (hU : IsOpen U)
    (hp₀ : 0 < p₀)
    (hf : ContinuousOn f U)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_integrable : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) (μ.restrict U))
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hintegral : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    ∀ y ∈ U, f y ≤
      Real.exp (∑' k, moserIterationCost theta a b k) * X 0 := by
  let C := Real.exp (∑' k, moserIterationCost theta a b k) * X 0
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le hX_zero
  have hroot_le : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ C := by
    intro k
    exact (hintegral k).trans
      (moser_iteration_bound hX_zero htheta htheta_one ha hb hstep k)
  have hbound : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict U) ≤
        C ^ parabolicMoserExponent n p₀ k := by
    intro k
    let p := parabolicMoserExponent n p₀ k
    let integral := ∫ y, f y ^ p ∂μ.restrict U
    have hp : 0 < p := by
      dsimp [p, parabolicMoserExponent]
      exact mul_pos hp₀ (pow_pos (by
        dsimp [parabolicMoserGain]
        have hn : 0 < (n : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
        positivity) k)
    have hintegral_nonneg : 0 ≤ integral := by
      dsimp [integral]
      exact MeasureTheory.integral_nonneg fun y => Real.rpow_nonneg (hf_nonneg y) _
    have hroot : integral ^ (1 / p) ≤ C := by
      simpa only [integral, p] using hroot_le k
    calc
      integral = integral ^ (1 : ℝ) := (Real.rpow_one integral).symm
      _ = integral ^ ((1 / p) * p) := by
        congr 2
        field_simp [hp.ne']
      _ = (integral ^ (1 / p)) ^ p := by
        rw [Real.rpow_mul hintegral_nonneg]
      _ ≤ C ^ p := Real.rpow_le_rpow
        (Real.rpow_nonneg hintegral_nonneg _) hroot hp.le
  exact DifferentialGeometry.Analysis.Integration.le_on_open_of_integral_rpow_le
    hU hC
    (parabolicMoserExponent_pos n hp₀)
    (parabolicMoserExponent_tendsto_atTop n hp₀)
    hf hf_nonneg hf_integrable hbound

theorem local_boundedness_of_moser_iteration
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {μ : MeasureTheory.Measure Y}
    [MeasureTheory.IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : Y → ℝ} {X : ℕ → ℝ} {p₀ theta a b : ℝ}
    (hp₀ : 0 < p₀)
    (hf : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_integrable : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) μ)
    (hX_zero : 0 ≤ X 0)
    (htheta : 0 ≤ theta) (htheta_one : theta < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hintegral : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k)
    (hstep : ∀ k, X (k + 1) ≤
      Real.exp (moserIterationCost theta a b k) * X k) :
    ∀ y, f y ≤
      Real.exp (∑' k, moserIterationCost theta a b k) * X 0 := by
  have hf_integrable' : ∀ k,
      MeasureTheory.Integrable
        (fun y => f y ^ parabolicMoserExponent n p₀ k) (μ.restrict Set.univ) := by
    simpa only [MeasureTheory.Measure.restrict_univ] using hf_integrable
  have hintegral' : ∀ k,
      (∫ y, f y ^ parabolicMoserExponent n p₀ k ∂μ.restrict Set.univ) ^
          (1 / parabolicMoserExponent n p₀ k) ≤ X k := by
    simpa only [MeasureTheory.Measure.restrict_univ] using hintegral
  have h := local_boundedness_on_open_of_moser_iteration (n := n)
    (μ := μ) (U := Set.univ) isOpen_univ hp₀ hf.continuousOn hf_nonneg
    hf_integrable' hX_zero htheta htheta_one ha hb hintegral' hstep
  exact fun y => h y (Set.mem_univ y)

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
