import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Claim 2 (mixed derivatives): the conversion engine

MSM135 Lemma 3.11, eq-(3.4) bookkeeping **Claim 2**: if `|∇^r g_k| ≤ C_r` for
`1 ≤ r ≤ L`, then `|∇^a ∇_k^b T| ≤ C_{a,b}` for `a + b ≤ L` and `T` with
Shi-bounded `∇_k`-towers (`Rm_k`, `Rc_k`).

Engine design (all at the component-array level, reusing the `AkMFold` machinery):
1. `akAct A B` — the per-slot `A_k`-action, the ONE-STEP conversion term:
   `covDerivStepComp ext chrRef B = covDerivStepComp ext chrK B + akAct ak B`
   (`covStep_chr_convert`; the `ext` parts cancel, pure algebra).
2. `akAct` decomposes as a finite sum of REINDEXED `contrTail`s
   (`akActTerm_eq`, slot combinators `(finRotate).symm.trans (swap s last)` +
   `frontExtendEquiv`), so the m-fold norm bound for `∇^a(akAct ak B)` is a
   corollary of the proven `P(m)` (`compL2_iterCovComp_contrTail_le`) — NO new
   Leibniz machinery.
3. Claim 2 = strong induction on `a`: bottom-pull + conversion + `P(m)`-corollary;
   the `∇_k`-step composes definitionally (`iterCovComp chr (iterCovComp chr F b) 1
   = iterCovComp chr F (b+1)` by `rfl`).

SIGN CONVENTION (`Claim1Wiring.md` §1b): `ak = chr(g_k) − chr(g_ref)`, so
`∇_ref-step = ∇_k-step + akAct ak` (the `−Γ` corrections differ by `−(chrR − chrK)
= +ak`).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## The one-step conversion `∇_ref = ∇_k + akAct` -/

/-- The per-slot action of a `(1,2)`-component array `A` (upper slot LAST) on a `(0,q)`
component array `B`: the conversion term between the covariant-derivative steps of two
connections.  Slot `0` of the result is the derivative direction. -/
def akAct {q : ℕ} (A : (Fin (2 + 1) → Idx) → Real) (B : (Fin q → Idx) → Real) :
    (Fin (q + 1) → Idx) → Real :=
  fun n => ∑ s : Fin q, ∑ p : Idx,
    A ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)

/-- **The one-step conversion**: the covariant-derivative step w.r.t. `chrR` equals the
step w.r.t. `chrK` plus the action of the Christoffel-difference array `chrK − chrR`
(the `ext` parts are identical and the `−Γ` sums differ by the difference action). -/
theorem covStep_chr_convert {q : ℕ}
    (ext : (Fin q → Idx) → Idx → Real)
    (chrR chrK : Idx → Idx → Idx → Real)
    (B : (Fin q → Idx) → Real) (n : Fin (q + 1) → Idx) :
    covDerivStepComp ext chrR B n =
      covDerivStepComp ext chrK B n +
        akAct (fun m => chrK (m 0) (m 1) (m 2) - chrR (m 0) (m 1) (m 2)) B n := by
  unfold covDerivStepComp akAct
  have hdiff : (∑ s : Fin q, ∑ p : Idx,
        (fun m : Fin (2 + 1) → Idx =>
            chrK (m 0) (m 1) (m 2) - chrR (m 0) (m 1) (m 2))
          ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)) =
      (∑ s : Fin q, ∑ p : Idx,
        chrK (n 0) (Fin.tail n s) p * B (Function.update (Fin.tail n) s p)) -
      (∑ s : Fin q, ∑ p : Idx,
        chrR (n 0) (Fin.tail n s) p * B (Function.update (Fin.tail n) s p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdiff]
  ring

/-! ## The slot decomposition: each `akAct` summand is a reindexed `contrTail` -/

/-- The inner slot permutation of the `s`-th `akAct` summand: `0 ↦ s`, `succ i ↦`
(`castSucc i`, with `s` deflected to `last`).  Built from combinators
(`finRotate` rotation + transposition), per the project lesson. -/
def akInnerPerm {q : ℕ} (s : Fin (q + 1)) : Equiv.Perm (Fin (q + 1)) :=
  ((finRotate (q + 1)).symm).trans (Equiv.swap s (Fin.last q))

theorem akInnerPerm_zero {q : ℕ} (s : Fin (q + 1)) :
    akInnerPerm s 0 = s := by
  have h0 : (finRotate (q + 1)).symm 0 = Fin.last q := by
    rw [Equiv.symm_apply_eq, finRotate_succ_apply, Fin.last_add_one]
  rcases eq_or_ne s (Fin.last q) with rfl | hs
  · simp [akInnerPerm, h0]
  · simp [akInnerPerm, h0, Equiv.swap_apply_right]

theorem akInnerPerm_succ {q : ℕ} (s : Fin (q + 1)) (i : Fin q) :
    akInnerPerm s i.succ =
      if Fin.castSucc i = s then Fin.last q else Fin.castSucc i := by
  have hrot : (finRotate (q + 1)).symm i.succ = Fin.castSucc i := by
    rw [Equiv.symm_apply_eq, finRotate_succ_apply]
    exact Fin.ext (by
      rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)]
      simp)
  rcases eq_or_ne (Fin.castSucc i) s with h | h
  · simp [akInnerPerm, hrot, h]
  · have hlast : Fin.castSucc i ≠ Fin.last q := (Fin.castSucc_lt_last i).ne
    simp [akInnerPerm, hrot, Equiv.swap_apply_of_ne_of_ne h hlast, h]

/-- The outer index reindex of the `s`-th `akAct` summand (`contrTail`'s `Fin (2+q)`
slots into the `Fin (q+1+1)` slots of the stepped array). -/
def akSlotEquiv {q : ℕ} (s : Fin (q + 1)) : Fin (2 + q) ≃ Fin (q + 1 + 1) :=
  (finCongr (show 2 + q = q + 1 + 1 by omega)).trans (frontExtendEquiv (akInnerPerm s))

theorem akSlotEquiv_castAdd0 {q : ℕ} (s : Fin (q + 1)) :
    akSlotEquiv s (Fin.castAdd q (0 : Fin 2)) = 0 := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.castAdd q (0 : Fin 2)) : Fin (q + 1 + 1)) = 0 := Fin.ext (by simp)
  simp [akSlotEquiv, h, frontExtendEquiv_zero]

theorem akSlotEquiv_castAdd1 {q : ℕ} (s : Fin (q + 1)) :
    akSlotEquiv s (Fin.castAdd q (1 : Fin 2)) = s.succ := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.castAdd q (1 : Fin 2)) : Fin (q + 1 + 1)) = (0 : Fin (q + 1)).succ :=
    Fin.ext (by simp)
  rw [akSlotEquiv, Equiv.trans_apply, h, frontExtendEquiv_succ, akInnerPerm_zero]

theorem akSlotEquiv_natAdd {q : ℕ} (s : Fin (q + 1)) (i : Fin q) :
    akSlotEquiv s (Fin.natAdd 2 i) =
      (if Fin.castSucc i = s then Fin.last q else Fin.castSucc i).succ := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.natAdd 2 i) : Fin (q + 1 + 1)) = (i.succ).succ :=
    Fin.ext (by simp)
  rw [akSlotEquiv, Equiv.trans_apply, h, frontExtendEquiv_succ, akInnerPerm_succ]

/-- **The `s`-th `akAct` summand is a reindexed `contrTail`**: contracting `A`'s upper
slot against `B`'s `s`-th slot equals the natural last-slot contraction against the
`swap s last`-reindexed `B`, with the free slots reindexed by `akSlotEquiv`. -/
theorem akActTerm_eq {q : ℕ} (A : (Fin (2 + 1) → Idx) → Real)
    (B : (Fin (q + 1) → Idx) → Real) (s : Fin (q + 1)) (n : Fin (q + 1 + 1) → Idx) :
    (∑ p : Idx, A ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)) =
      contrTail A (fun w => B (fun j => w (Equiv.swap s (Fin.last q) j)))
        (fun j => n (akSlotEquiv s j)) := by
  classical
  rw [contrTail_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  · -- the A-factor arguments agree
    congr 1
    funext m
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      refine Fin.cases ?_ (fun m'' => ?_) m'
      · show (![n 0, Fin.tail n s, c] : Fin 3 → Idx) 0 =
          n (akSlotEquiv s (Fin.castAdd q (0 : Fin 2)))
        rw [akSlotEquiv_castAdd0]
        rfl
      · have hm : m'' = 0 := Subsingleton.elim _ _
        subst hm
        show (![n 0, Fin.tail n s, c] : Fin 3 → Idx) 1 =
          n (akSlotEquiv s (Fin.castAdd q (1 : Fin 2)))
        rw [akSlotEquiv_castAdd1]
        rfl
  · -- the B-factor arguments agree
    congr 1
    funext j
    rcases eq_or_ne j s with rfl | hjs
    · rw [Function.update_self, Equiv.swap_apply_left, Fin.snoc_last]
    · rw [Function.update_of_ne hjs]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hjl : Fin.castSucc j' ≠ Fin.last q := (Fin.castSucc_lt_last j').ne
        rw [Equiv.swap_apply_of_ne_of_ne hjs hjl, Fin.snoc_castSucc,
          show n (akSlotEquiv s (Fin.natAdd 2 j')) = n ((Fin.castSucc j').succ) from by
            rw [akSlotEquiv_natAdd, if_neg hjs]]
        rfl
      · rw [Equiv.swap_apply_right]
        have hs : s ≠ Fin.last q := fun h => hjs h.symm
        rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
        · rw [Fin.snoc_castSucc,
            show n (akSlotEquiv (Fin.castSucc s') (Fin.natAdd 2 s')) =
              n ((Fin.last q).succ) from by
              rw [akSlotEquiv_natAdd, if_pos rfl]]
          rfl
        · exact absurd rfl hs

end DifferentialGeometry.PDE.RicciFlow
