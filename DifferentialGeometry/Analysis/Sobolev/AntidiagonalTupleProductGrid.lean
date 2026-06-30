import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open scoped BigOperators

namespace DifferentialGeometry
namespace Combinatorics

noncomputable def antidiagonalTupleGrid (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (i + 1),
    ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n, b (e m)

lemma antidiagonalTupleGrid_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) :
    0 ≤ antidiagonalTupleGrid b i :=
  Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => hb _)))

lemma antidiagonalTupleGrid_zero (b : ℕ → ℝ) :
    antidiagonalTupleGrid b 0 = 1 := by
  rw [antidiagonalTupleGrid, Finset.sum_range_one,
    Finset.Nat.antidiagonalTuple_zero_zero, Finset.sum_singleton, Fin.prod_univ_zero]

private def consQ (q n : ℕ) (e : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons q e

private lemma consQ_injective (q n : ℕ) :
    Function.Injective (consQ q n) := by
  intro e₁ e₂ h
  have h₁ : Fin.tail (consQ q n e₁) = Fin.tail (consQ q n e₂) := by rw [h]
  rwa [consQ, consQ, Fin.tail_cons, Fin.tail_cons] at h₁

private lemma consQ_mem (q k n : ℕ) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    consQ q n e ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at he ⊢
  rw [consQ, Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [he]; omega

lemma single_factor_mul_antidiagonalTupleGrid_le
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (k q : ℕ) (hq : 1 ≤ q) :
    b q * antidiagonalTupleGrid b k ≤ antidiagonalTupleGrid b (k + q) := by
  classical
  have hterm : ∀ n : ℕ,
      b q * (∑ e ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e m)) ≤
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) := by
    intro n
    rw [Finset.mul_sum]
    have hcons : ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
        b q * ∏ m : Fin n, b (e m) =
          ∏ m : Fin (n + 1), b (consQ q n e m) := by
      intro e _
      rw [consQ, Fin.prod_univ_succ, Fin.cons_zero]
      refine congrArg (fun t => b q * t) (Finset.prod_congr rfl (fun m _ => ?_))
      rw [Fin.cons_succ]
    rw [Finset.sum_congr rfl hcons]
    rw [← Finset.sum_image
      (f := fun e' : Fin (n + 1) → ℕ => ∏ m : Fin (n + 1), b (e' m))
      (g := consQ q n)
      ((consQ_injective q n).injOn)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun e' _ _ => Finset.prod_nonneg (fun _ _ => hb _))
    intro e' he'
    rw [Finset.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact consQ_mem q k n e he
  have hstep : b q * antidiagonalTupleGrid b k ≤
      ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) := by
    rw [antidiagonalTupleGrid, Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => hterm n)
  refine hstep.trans ?_
  rw [antidiagonalTupleGrid]
  have hshift : ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) =
      ∑ N ∈ Finset.Ico 1 (k + 2),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple N (k + q), ∏ m : Fin N, b (e' m) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by rw [show k + 2 - 1 = k + 1 from by omega]) (fun n _ => ?_)
    rw [show 1 + n = n + 1 from by omega]
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun N _ _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun _ _ => hb _)))
  intro N hN
  rw [Finset.mem_Ico] at hN
  rw [Finset.mem_range]
  omega

noncomputable def recGridCS (A : ℝ) (B : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (A, A)
  | (n + 1) => let p := recGridCS A B n; (B n * p.2, p.2 + B n * p.2)

lemma recGridCS_snd_eq (A : ℝ) (B : ℕ → ℝ) :
    ∀ i, (recGridCS A B i).2 = ∑ k ∈ Finset.range (i + 1), (recGridCS A B k).1 := by
  intro i
  induction i with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    change (recGridCS A B n).2 + B n * (recGridCS A B n).2 =
      (recGridCS A B n).2 + (recGridCS A B (n + 1)).1
    rw [recGridCS]

lemma recGridCS_nonneg (A : ℝ) (B : ℕ → ℝ) (hA : 0 ≤ A) (hB : ∀ m, 0 ≤ B m) :
    ∀ i, 0 ≤ (recGridCS A B i).1 ∧ 0 ≤ (recGridCS A B i).2 := by
  intro i
  induction i with
  | zero => exact ⟨hA, hA⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩ <;>
      · show 0 ≤ _
        rw [recGridCS]
        first
        | exact mul_nonneg (hB n) ih.2
        | exact add_nonneg ih.2 (mul_nonneg (hB n) ih.2)

theorem antidiagonalTupleGrid_convolution_bound
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (a : ℕ → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hbase : a 0 ≤ A)
    (hstep : ∀ m, a (m + 1) ≤
      B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k) :
    ∀ i, a i ≤ (recGridCS A B i).1 * antidiagonalTupleGrid b i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
      rw [antidiagonalTupleGrid_zero, mul_one]
      change a 0 ≤ (recGridCS A B 0).1
      rw [recGridCS]; exact hbase
    | (m + 1) =>
      refine (hstep m).trans ?_
      have hkey : ∀ k ∈ Finset.range (m + 1),
          b ((m - k) + 1) * a k ≤
            (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hIH : a k ≤ (recGridCS A B k).1 * antidiagonalTupleGrid b k := ih k (by omega)
        have hCk_nn : 0 ≤ (recGridCS A B k).1 := (recGridCS_nonneg A B hA hB k).1
        calc b ((m - k) + 1) * a k
            ≤ b ((m - k) + 1) * ((recGridCS A B k).1 * antidiagonalTupleGrid b k) :=
              mul_le_mul_of_nonneg_left hIH (hb _)
          _ = (recGridCS A B k).1 * (b ((m - k) + 1) * antidiagonalTupleGrid b k) := by ring
          _ ≤ (recGridCS A B k).1 *
                antidiagonalTupleGrid b (k + ((m - k) + 1)) :=
              mul_le_mul_of_nonneg_left
                (single_factor_mul_antidiagonalTupleGrid_le b hb k ((m - k) + 1)
                  (by omega)) hCk_nn
          _ = (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) := by
              rw [show k + ((m - k) + 1) = m + 1 from by omega]
      calc B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k
          ≤ B m * ∑ k ∈ Finset.range (m + 1),
              (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey) (hB m)
        _ = B m * ((∑ k ∈ Finset.range (m + 1), (recGridCS A B k).1) *
              antidiagonalTupleGrid b (m + 1)) := by rw [← Finset.sum_mul]
        _ = (recGridCS A B (m + 1)).1 * antidiagonalTupleGrid b (m + 1) := by
            rw [← recGridCS_snd_eq A B m]
            show B m * ((recGridCS A B m).2 * antidiagonalTupleGrid b (m + 1)) = _
            rw [recGridCS]; ring

theorem antidiagonalTupleGrid_convolution_closure
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (a : ℕ → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hbase : a 0 ≤ A)
    (hstep : ∀ m, a (m + 1) ≤
      B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i, a i ≤ C i * antidiagonalTupleGrid b i :=
  ⟨fun i => (recGridCS A B i).1, fun i => (recGridCS_nonneg A B hA hB i).1,
    antidiagonalTupleGrid_convolution_bound b hb a A hA B hB hbase hstep⟩

end Combinatorics
end DifferentialGeometry
