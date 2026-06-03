import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Constants for MSM135 Lemma 4.5

This file contains only the geometry-free constants used to turn the informal
"sum of terms" and "choose a larger constant" steps in MSM135 Lemma 4.5 into
explicit finite algebra.
-/

noncomputable section

namespace RicciFlower
namespace HCGCompactness

open scoped BigOperators

/-- One-step constant for bounding the Leibniz expansion of
`nabla_H^k (A * T)` in MSM135 Lemma 4.5.

`B a` is the order-`a` bound for the connection-difference tensor, and `m` is
the tensor rank in the covariant `(0,m)` first pass. -/
noncomputable def oneStepConst (B : Nat -> Real) (k m : Nat) : Real :=
  (m : Real) *
    Finset.sum (Finset.range (k + 1))
      (fun a => (k.choose a : Real) * B a)

/-- Recursive constants for the abstract covariant version of MSM135 Lemma 4.5.

The extra `+ 1` is deliberate: it makes positivity and monotonicity immediate,
formalizing the book's "choose the next constant larger" step. -/
noncomputable def lemma45Const (B : Nat -> Real) : Nat -> Nat -> Real
  | 0, _m => 1
  | p + 1, m =>
      lemma45Const B p m
        + 1
        + oneStepConst B p m
        + lemma45Const B p (m + 1) *
          (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m))

theorem oneStepConst_nonneg
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (k m : Nat) :
    0 <= oneStepConst B k m := by
  unfold oneStepConst
  refine mul_nonneg (by exact_mod_cast Nat.zero_le m) ?_
  refine Finset.sum_nonneg ?_
  intro a _ha
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (k.choose a)) (hB a)

theorem lemma45Const_pos
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    0 < lemma45Const B p m := by
  induction p generalizing m with
  | zero =>
      simp [lemma45Const]
  | succ p ih =>
      have hprev_nonneg : 0 <= lemma45Const B p m := le_of_lt (ih m)
      have hstep_nonneg : 0 <= oneStepConst B p m :=
        oneStepConst_nonneg hB p m
      have hprev_succ_nonneg : 0 <= lemma45Const B p (m + 1) :=
        le_of_lt (ih (m + 1))
      have hsum_nonneg :
          0 <= Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
        exact Finset.sum_nonneg fun k _hk => oneStepConst_nonneg hB k m
      have hfactor_nonneg :
          0 <= 1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
        linarith
      have hprod_nonneg :
          0 <= lemma45Const B p (m + 1) *
            (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m)) :=
        mul_nonneg hprev_succ_nonneg hfactor_nonneg
      simp [lemma45Const]
      linarith

theorem lemma45Const_nonneg
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    0 <= lemma45Const B p m :=
  le_of_lt (lemma45Const_pos hB p m)

theorem lemma45Const_le_succ
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    lemma45Const B p m <= lemma45Const B (p + 1) m := by
  have hstep_nonneg : 0 <= oneStepConst B p m :=
    oneStepConst_nonneg hB p m
  have hprev_succ_nonneg : 0 <= lemma45Const B p (m + 1) :=
    lemma45Const_nonneg hB p (m + 1)
  have hsum_nonneg :
      0 <= Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
    exact Finset.sum_nonneg fun k _hk => oneStepConst_nonneg hB k m
  have hfactor_nonneg :
      0 <= 1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
    linarith
  have hprod_nonneg :
      0 <= lemma45Const B p (m + 1) *
        (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m)) :=
    mul_nonneg hprev_succ_nonneg hfactor_nonneg
  simp [lemma45Const]
  linarith

end HCGCompactness
end RicciFlower
