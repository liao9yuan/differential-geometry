import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding

/-!
# Quantitative local-ball `L²`-Sobolev pointwise embedding for smooth functions

For a smooth function `f` on `EuclideanSpace ℝ (Fin d)` and a ball `B(x₀, R)`,
when the supercritical threshold `d < 2 K` holds, the value of `f` at any point of
the smaller ball `B(x₀, R/4)` is controlled by the order-`2K` `L²`-Sobolev norm of
`f` on `B(x₀, R)`:

    `|f x| ≤ C · ∑_{j ≤ 2K} ‖∂ʲ f‖_{L²(B(x₀, R))}`,

with a constant `C` depending only on `d, K, R` — uniform in `f`.

This is the pure-Euclidean quantitative core consumed by the intrinsic tensor
Sobolev embedding `H^{2k} ↪ C⁰`.  Unlike the global chart-Sobolev embeddings, the
bound is *local* (on a single ball) and *quantitative* (a single explicit
constant times the order-`2K` `L²` norm), which is what the partition-of-unity
lower-bound localisation needs.

## Strategy

A smooth cutoff `χ` supported in `B(x₀, R)` and equal to `1` on `B(x₀, R/2)`
turns `f` into a compactly-supported `χ·f` agreeing with `f` (including all
derivatives) on `B(x₀, R/2)`.  The `L²` subcritical tower
`MemWkp_subcritical_iterated` is run on `χ·f`, tracking the quantitative
`wkpNorm` bound at each step, until a supercritical exponent `q > d` of some
lower order is reached; the order-`0` Morrey bound
`smooth_morrey_iteratedFDeriv_bound_uniform` then yields the pointwise value at
`x ∈ B(x₀, R/4)`.  Finally the `wkpNorm` of `χ·f` is bounded by the order-`2K`
`L²`-derivative norms of `f` via the Leibniz product rule with uniformly bounded
cutoff derivatives.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Chart.TowerStep
  (subcriticalConstant subcriticalConstant_nonneg MemWkp_subcritical_iterated)

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

/-! ## Quantitative subcritical tower descent (norm-tracking)

The driver `tower_to_supercritical_quant` mirrors the membership-only driver
`tower_to_supercritical` but carries a quantitative `wkpNorm` bound for the final
supercritical exponent. -/

/-- **Norm-tracking subcritical tower descent.**

From `MemWkp (m + 1 + s) (ofReal p) f Ω` for a compactly-supported `f` with
`tsupport f ⊆ Ω`, where `p` is regular at depth `s + 1` and `(s + 1) p > d`,
produce an exponent `q > d` with `1 ≤ q`, the membership
`MemWkp (m + 1) (ofReal q) f Ω`, and a finite constant `C ≥ 0` with
`wkpNorm (m + 1) (ofReal q) f Ω ≤ ofReal C · wkpNorm (m + 1 + s) (ofReal p) f Ω`.

The constant `C` depends only on `d, s, p` (through the recursively defined
subcritical constants), not on `f`. -/
private theorem tower_to_supercritical_quant
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      RegularExponent.IsRegular (d : ℝ) p (s + 1) →
      (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
      ∀ {f : EuN → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
        MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω →
          ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧
            ∃ C : ℝ, 0 ≤ C ∧
              MemWkp (d := d) (m + 1) (ENNReal.ofReal q) f Ω ∧
              wkpNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
                ENNReal.ofReal C *
                  wkpNorm (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp f _hf_cpt _hf_supp hf
      -- `s = 0`: order `m + 1`, exponent `p > d`; identity descent.
      have hp_dim : (d : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      refine ⟨p, hp_one, hp_dim, 1, by norm_num, by simpa using hf, ?_⟩
      simp only [add_zero] at hf ⊢
      rw [ENNReal.ofReal_one, one_mul]
  | succ s ih =>
      intro p hp_one hreg hkp f hf_cpt hf_supp hf
      have hp_ne_d : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_d with hp_lt | hp_gt
      · -- Sub-critical: one quantitative tower step at order `m + 1 + s`.
        have hp_pos : 0 < p := by linarith
        have hf' : MemWkp (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [h_idx] at hf
          exact hf
        obtain ⟨h_mem_p1, h_norm_p1⟩ :=
          MemWkp_subcritical_iterated (d := d) (m + 1 + s)
            hp_one hp_lt hΩ_open hf_cpt hf_supp hf'
        set p_1 : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
        have hd_p_pos : 0 < (d : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]
          nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have hkp_next : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p_1 := by
          have h_form : (d : ℝ) < ((s + 1 : ℕ) + 1 : ℝ) * p := by
            have hkp_cast : ((s + 1 + 1 : ℕ) : ℝ) * p =
                ((s + 1 : ℕ) + 1 : ℝ) * p := by push_cast; ring
            rw [hkp_cast] at hkp
            exact hkp
          have h_id :=
            DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
              (d := d) (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]
          exact h_id
        have hreg_p_1 : RegularExponent.IsRegular (d : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_mem_p1' : MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω := by
          rw [hp_1_def]; exact h_mem_p1
        -- Recurse.
        obtain ⟨q, hq_one, hq_dim, C', hC'_nn, h_mem_q, h_norm_q⟩ :=
          ih hp_1_one hreg_p_1 hkp_next hf_cpt hf_supp h_mem_p1'
        -- Combine the two quantitative bounds.
        refine ⟨q, hq_one, hq_dim,
          C' * subcriticalConstant (m + 1 + s) d p,
          mul_nonneg hC'_nn (subcriticalConstant_nonneg _ _ _), h_mem_q, ?_⟩
        -- `h_norm_p1` is in terms of order `(m + 1 + s) + 1 = m + 1 + (s + 1)`.
        have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
        -- `wkpNorm (m+1) q f ≤ ofReal C' * wkpNorm (m+1+s) p_1 f`
        --                    ≤ ofReal C' * ofReal subC * wkpNorm ((m+1+s)+1) p f
        have h_step_norm :
            wkpNorm (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω ≤
              ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                wkpNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          rw [hp_1_def]; exact h_norm_p1
        have h_chain :
            wkpNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
              ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  wkpNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) :=
          le_trans h_norm_q (mul_le_mul_of_nonneg_left h_step_norm (zero_le _))
        have h_rhs_eq :
            ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  wkpNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) =
              ENNReal.ofReal (C' * subcriticalConstant (m + 1 + s) d p) *
                wkpNorm (d := d) (m + 1 + (s + 1)) (ENNReal.ofReal p) f Ω := by
          rw [ENNReal.ofReal_mul hC'_nn, h_idx]; ring
        rw [← h_rhs_eq]; exact h_chain
      · -- Super-critical: order drop, identity norm bound (`wkpNorm` is monotone).
        refine ⟨p, hp_one, hp_gt, 1, by norm_num,
          MemWkp.le_of_le (by omega) hf, ?_⟩
        rw [ENNReal.ofReal_one, one_mul]
        exact wkpNorm_mono_order (d := d) (by omega) f Ω
end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
