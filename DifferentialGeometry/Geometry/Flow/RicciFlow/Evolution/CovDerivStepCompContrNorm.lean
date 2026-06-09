import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Component-`ℓ²` norm bound for the natural contraction

`ric_bound` (MSM135 Lemma 3.11, Claim 1) bounds `√normSq0S` of a contraction by the
product of the factor norms.  In a `gRef`-orthonormal frame `normSq0S = ∑ component²`
(`normSq0S_identity_eq_sum_sq`), so the component-level inequality
`|A ∗ B|² ≤ |A|² · |B|²` (Cauchy–Schwarz on the contracted index, then the free index
sums factor) is the base case (`m = 0`) of the iterated-Leibniz norm bound and the
per-term bound `|∇ᶜA ∗ ∇^{m−c}B| ≤ |∇ᶜA| |∇^{m−c}B|`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Squared component `ℓ²`-norm of a raw component array. -/
def compL2Sq {r : ℕ} (T : (Fin r → Idx) → Real) : Real :=
  ∑ idx : Fin r → Idx, (T idx) ^ 2

theorem compL2Sq_nonneg {r : ℕ} (T : (Fin r → Idx) → Real) : 0 ≤ compL2Sq T :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Reindex a sum over `(r+1)`-tuples as a sum over the first `r` slots and the last. -/
private theorem sum_snoc_split {p : ℕ} (F : (Fin (p + 1) → Idx) → Real) :
    (∑ f : Fin (p + 1) → Idx, F f) =
      ∑ g : Fin p → Idx, ∑ c : Idx, F (Fin.snoc g c) := by
  classical
  let e : (Fin (p + 1) → Idx) ≃ (Fin p → Idx) × Idx :=
    { toFun := fun f => (Fin.init f, f (Fin.last p))
      invFun := fun gc => Fin.snoc gc.1 gc.2
      left_inv := fun f => Fin.snoc_init_self f
      right_inv := fun gc => by simp [Fin.init_snoc, Fin.snoc_last] }
  rw [show (∑ g : Fin p → Idx, ∑ c : Idx, F (Fin.snoc g c))
      = ∑ gc : (Fin p → Idx) × Idx, F (Fin.snoc gc.1 gc.2) from
    (Fintype.sum_prod_type (fun gc : (Fin p → Idx) × Idx => F (Fin.snoc gc.1 gc.2))).symm]
  exact Fintype.sum_equiv e F (fun gc => F (Fin.snoc gc.1 gc.2))
    (fun f => by simp only [e, Equiv.coe_fn_mk, Fin.snoc_init_self])

/-- Reindex a sum over `(p+q)`-tuples as a double sum over the two free blocks. -/
private theorem sum_append_split {p q : ℕ} (F : (Fin (p + q) → Idx) → Real) :
    (∑ idx : Fin (p + q) → Idx, F idx) =
      ∑ a : Fin p → Idx, ∑ b : Fin q → Idx, F (Fin.append a b) := by
  classical
  rw [show (∑ a : Fin p → Idx, ∑ b : Fin q → Idx, F (Fin.append a b))
      = ∑ ab : (Fin p → Idx) × (Fin q → Idx), F (Fin.append ab.1 ab.2) from
    (Fintype.sum_prod_type (fun ab => F (Fin.append ab.1 ab.2))).symm]
  refine Fintype.sum_equiv
    { toFun := fun idx => (fun i => idx (Fin.castAdd q i), fun j => idx (Fin.natAdd p j))
      invFun := fun ab => Fin.append ab.1 ab.2
      left_inv := fun idx => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · simp [Fin.append_left]
        · simp [Fin.append_right]
      right_inv := fun ab => by
        refine Prod.ext ?_ ?_
        · funext i; simp [Fin.append_left]
        · funext j; simp [Fin.append_right] } F (fun ab => F (Fin.append ab.1 ab.2)) ?_
  intro idx
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [Fin.append_left]
  · simp [Fin.append_right]

/-- **The contraction is `ℓ²`-norm sub-multiplicative.**  `|A ∗ B|² ≤ |A|² · |B|²`,
by Cauchy–Schwarz on the contracted index and factoring the free-index sums. -/
theorem compL2Sq_contrTail_le {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    compL2Sq (contrTail A B) ≤ compL2Sq A * compL2Sq B := by
  classical
  have hcs : ∀ idx : Fin (p + q) → Idx,
      (contrTail A B idx) ^ 2 ≤
        (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
          (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2) := by
    intro idx
    rw [contrTail_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    compL2Sq (contrTail A B)
        = ∑ idx : Fin (p + q) → Idx, (contrTail A B idx) ^ 2 := rfl
    _ ≤ ∑ idx : Fin (p + q) → Idx,
          (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
            (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2) :=
          Finset.sum_le_sum fun idx _ => hcs idx
    _ = (∑ a : Fin p → Idx, ∑ c : Idx, A (Fin.snoc a c) ^ 2) *
          (∑ b : Fin q → Idx, ∑ c : Idx, B (Fin.snoc b c) ^ 2) := by
          rw [sum_append_split
            (F := fun idx =>
              (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
                (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2))]
          simp only [Fin.append_left, Fin.append_right]
          rw [← Finset.sum_mul_sum]
    _ = compL2Sq A * compL2Sq B := by
          rw [compL2Sq, compL2Sq, sum_snoc_split (F := fun f => A f ^ 2),
            sum_snoc_split (F := fun f => B f ^ 2)]

/-- The component `ℓ²`-norm. -/
def compL2 {r : ℕ} (T : (Fin r → Idx) → Real) : Real := Real.sqrt (compL2Sq T)

theorem compL2_nonneg {r : ℕ} (T : (Fin r → Idx) → Real) : 0 ≤ compL2 T :=
  Real.sqrt_nonneg _

theorem compL2_sq {r : ℕ} (T : (Fin r → Idx) → Real) : compL2 T ^ 2 = compL2Sq T := by
  rw [compL2, Real.sq_sqrt (compL2Sq_nonneg T)]

/-- `compL2Sq` is invariant under reindexing the slots by an equivalence (the squared
norm is a sum over all index tuples, which the reindexing merely permutes). -/
theorem compL2Sq_comp_equiv {r r' : ℕ} (T : (Fin r → Idx) → Real) (e : Fin r ≃ Fin r') :
    compL2Sq (fun idx : Fin r' → Idx => T (fun i => idx (e i))) = compL2Sq T := by
  classical
  simp only [compL2Sq]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx))
    (fun idx : Fin r' → Idx => T (fun i => idx (e i)) ^ 2)
    (fun g : Fin r → Idx => T g ^ 2) ?_
  intro idx
  have hfun : (e.symm.arrowCongr (Equiv.refl Idx)) idx = fun i => idx (e i) := by
    funext i
    simp [Equiv.arrowCongr_apply, Equiv.symm_symm]
  rw [hfun]

/-- `compL2` is invariant under reindexing the slots by an equivalence. -/
theorem compL2_comp_equiv {r r' : ℕ} (T : (Fin r → Idx) → Real) (e : Fin r ≃ Fin r') :
    compL2 (fun idx : Fin r' → Idx => T (fun i => idx (e i))) = compL2 T := by
  rw [compL2, compL2, compL2Sq_comp_equiv]

/-- The contraction is `ℓ²`-norm sub-multiplicative (the `√` form). -/
theorem compL2_contrTail_le {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    compL2 (contrTail A B) ≤ compL2 A * compL2 B := by
  rw [compL2, compL2, compL2, ← Real.sqrt_mul (compL2Sq_nonneg A)]
  exact Real.sqrt_le_sqrt (compL2Sq_contrTail_le A B)

/-- **Minkowski for the component `ℓ²`-norm**: the triangle inequality. -/
theorem compL2_add_le {r : ℕ} (T U : (Fin r → Idx) → Real) :
    compL2 (fun idx => T idx + U idx) ≤ compL2 T + compL2 U := by
  have hCS : (∑ idx : Fin r → Idx, T idx * U idx) ≤ compL2 T * compL2 U := by
    have hle : (∑ idx : Fin r → Idx, T idx * U idx)
        ≤ Real.sqrt ((∑ idx : Fin r → Idx, T idx * U idx) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    calc ∑ idx : Fin r → Idx, T idx * U idx
        ≤ Real.sqrt ((∑ idx : Fin r → Idx, T idx * U idx) ^ 2) := hle
      _ ≤ Real.sqrt (compL2Sq T * compL2Sq U) :=
            Real.sqrt_le_sqrt
              (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun idx => T idx) (fun idx => U idx))
      _ = compL2 T * compL2 U := by rw [compL2, compL2, Real.sqrt_mul (compL2Sq_nonneg T)]
  have hsq : compL2Sq (fun idx => T idx + U idx) ≤ (compL2 T + compL2 U) ^ 2 := by
    have hexp : compL2Sq (fun idx => T idx + U idx)
        = compL2Sq T + 2 * (∑ idx : Fin r → Idx, T idx * U idx) + compL2Sq U := by
      simp only [compL2Sq]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun idx _ => by ring
    rw [hexp]
    have h1 := compL2_sq T
    have h2 := compL2_sq U
    nlinarith [hCS, compL2_nonneg T, compL2_nonneg U]
  rw [compL2]
  calc Real.sqrt (compL2Sq (fun idx => T idx + U idx))
      ≤ Real.sqrt ((compL2 T + compL2 U) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = compL2 T + compL2 U :=
          Real.sqrt_sq (add_nonneg (compL2_nonneg T) (compL2_nonneg U))

end DifferentialGeometry.PDE.RicciFlow
