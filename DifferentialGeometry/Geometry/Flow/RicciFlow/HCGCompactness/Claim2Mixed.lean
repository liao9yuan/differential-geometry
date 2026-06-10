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

/-! ## Finite-sum tower and norm lemmas -/

private theorem contMDiffOn_finsetSum' {ι : Type*} {u : Set M} (t : Finset ι)
    (F : ι → M → Real)
    (hF : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, F i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ))
  | insert a s has ih =>
    have hsum : (fun y => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y
      rw [Finset.sum_insert has]
    rw [hsum]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- The component tower of a finite sum of (smooth) fields is the sum of the towers
(`iterCovComp_add` iterated over the finset). -/
theorem iterCovComp_sum {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    {ι : Type*} (t : Finset ι) (F : ι → M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hF : ∀ i ∈ t, ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => F i y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => ∑ i ∈ t, F i z k) a y n =
        ∑ i ∈ t, iterCovComp (I := I) frame chr (F i) a y n := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro y hy n
    have hzero : (fun (z : M) (k : Fin r → Idx) => ∑ i ∈ (∅ : Finset ι), F i z k) =
        fun z k => (0 : ℝ) * (0 : ℝ) := by
      funext z k
      simp
    rw [hzero,
      iterCovComp_smul hu frame chr 0 (fun _ _ => (0 : ℝ)) hframe hchr
        (fun m => contMDiffOn_const) a y hy n]
    simp
  | insert b s hbs ih =>
    intro y hy n
    have hsplit : (fun (z : M) (k : Fin r → Idx) => ∑ i ∈ insert b s, F i z k) =
        fun z k => F b z k + ∑ i ∈ s, F i z k := by
      funext z k
      rw [Finset.sum_insert hbs]
    rw [hsplit,
      iterCovComp_add hu frame chr (F b) (fun z k => ∑ i ∈ s, F i z k) hframe hchr
        (hF b (Finset.mem_insert_self b s))
        (fun m => contMDiffOn_finsetSum' s (fun i y => F i y m)
          (fun i hi => hF i (Finset.mem_insert_of_mem hi) m)) a y hy n,
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) y hy n,
      Finset.sum_insert hbs]

/-- Triangle inequality for finite sums of component arrays. -/
theorem compL2_sum_le {r : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → (Fin r → Idx) → Real) :
    compL2 (fun n => ∑ i ∈ t, F i n) ≤ ∑ i ∈ t, compL2 (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : compL2 (fun _ : Fin r → Idx => (0 : ℝ)) = 0 := by
      simp [compL2, compL2Sq]
    exact le_of_eq this
  | insert b s hbs ih =>
    simp only [Finset.sum_insert hbs]
    exact le_trans (compL2_add_le (F b) (fun n => ∑ i ∈ s, F i n))
      (add_le_add le_rfl ih)

/-! ## The m-fold norm bound for the conversion term (`P(m)` reused) -/

/-- **The m-fold bound for the conversion action**: `|∇^a(akAct A B)|` obeys the same
binomial bound as the natural contraction, slot-multiplied — each of the `q+1` slot
summands is a reindexed `contrTail` (`akActTerm_eq`), so `P(m)`
(`compL2_iterCovComp_contrTail_le`) applies verbatim after the reindex norm-invariances. -/
theorem compL2_akAct_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (A : M → (Fin (2 + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (a : ℕ) {y : M} (hy : y ∈ u) :
    compL2 (iterCovComp (I := I) frame chr (fun z => akAct (A z) (B z)) a y) ≤
      (q + 1 : ℝ) * ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c y) *
        compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
  classical
  -- the base field as a finite sum of reindexed contrTails
  have hbase : (fun z => akAct (A z) (B z)) =
      fun z (n : Fin (q + 1 + 1) → Idx) => ∑ s : Fin (q + 1),
        contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          (fun j => n (akSlotEquiv s j)) := by
    funext z n
    unfold akAct
    exact Finset.sum_congr rfl fun s _ => akActTerm_eq (A z) (B z) s n
  -- smoothness of each slot summand
  have hFsm : ∀ s : Fin (q + 1), ∀ k : Fin (q + 1 + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun z => contrTail (A z)
          (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          (fun j => k (akSlotEquiv s j))) u :=
    fun s k => contMDiffOn_contrTail _ _ hA
      (fun k' => hB (fun j => k' (Equiv.swap s (Fin.last q) j))) _
  rw [hbase]
  -- tower of the finite sum, then triangle
  have htower := iterCovComp_sum hu frame chr Finset.univ
    (fun (s : Fin (q + 1)) (z : M) (n : Fin (q + 1 + 1) → Idx) =>
      contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
        (fun j => n (akSlotEquiv s j)))
    hframe hchr (fun s _ => hFsm s) a y hy
  calc compL2 (iterCovComp (I := I) frame chr
        (fun z n => ∑ s : Fin (q + 1),
          contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
            (fun j => n (akSlotEquiv s j))) a y)
      = compL2 (fun n : Fin (q + 1 + 1 + a) → Idx => ∑ s : Fin (q + 1),
          iterCovComp (I := I) frame chr
            (fun z (nn : Fin (q + 1 + 1) → Idx) =>
              contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
                (fun j => nn (akSlotEquiv s j))) a y n) :=
        congrArg compL2 (funext fun n => htower n)
    _ ≤ ∑ s : Fin (q + 1), compL2 (iterCovComp (I := I) frame chr
          (fun z (nn : Fin (q + 1 + 1) → Idx) =>
            contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
              (fun j => nn (akSlotEquiv s j))) a y) :=
        compL2_sum_le Finset.univ _
    _ ≤ ∑ _s : Fin (q + 1), ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c y) *
          compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
        refine Finset.sum_le_sum fun s _ => ?_
        -- kill the outer reindex, apply `P(a)`, kill the inner reindex
        rw [compL2_iterCovComp_compReindex (akSlotEquiv s) frame chr
          (fun z => contrTail (A z)
            (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))) a y]
        refine le_trans (compL2_iterCovComp_contrTail_le hu frame chr hframe hchr a A
          (fun z (w : Fin (q + 1) → Idx) => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          hA (fun k' => hB (fun j => k' (Equiv.swap s (Fin.last q) j))) hy)
          (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [compL2_iterCovComp_compReindex (Equiv.swap s (Fin.last q)) frame chr B (a - c) y]
    _ = (q + 1 : ℝ) * ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c y) *
          compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The field-level conversion -/

/-- **The field-level one-step conversion** (pointwise, no smoothness needed): the first
`chrR`-tower step of a field equals the first `chrK`-step plus the action of the
pointwise Christoffel-difference array. -/
theorem iterCov_chr_convert {q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrR chrK : M → Idx → Idx → Idx → Real)
    (B : M → (Fin q → Idx) → Real) (y : M) (n : Fin (q + 1) → Idx) :
    iterCovComp (I := I) frame chrR B 1 y n =
      iterCovComp (I := I) frame chrK B 1 y n +
        akAct (fun m => chrK y (m 0) (m 1) (m 2) - chrR y (m 0) (m 1) (m 2)) (B y) n := by
  simp only [iterCovComp_succ, iterCovComp_zero]
  exact covStep_chr_convert _ _ _ _ n

end DifferentialGeometry.PDE.RicciFlow
