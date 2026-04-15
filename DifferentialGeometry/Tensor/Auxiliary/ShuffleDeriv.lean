/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Auxiliary.ShuffleDecomposition
import DifferentialGeometry.Tensor.Auxiliary.Fin
import Mathlib.GroupTheory.Perm.Fin

/-!
# Shuffle-derivative bijection

For the graded Leibniz rule `d(ω ∧ τ) = dω ∧ τ + (-1)^m ω ∧ dτ`, the proof requires
a sign-preserving bijection between the two double-sum index sets.

## Key construction

Given `k : Fin (m + n + 1)` (derivative position) and
`σ : Perm (Fin m ⊕ Fin n)` (inner shuffle), the combined permutation

  `π := (Fin.cycleRange k)⁻¹ * Equiv.Perm.decomposeFin.symm (0, σ_fin)`

of `Fin (m + n + 1)` sends `0 ↦ k` and `(j+1) ↦ k.succAbove (σ_fin j)`,
with sign `(-1)^k * sign(σ)`.

Conjugating by `Φ := finSumFinEquiv.trans Fin.finAddFlipAssoc` gives the
corresponding `τ : Perm (Fin (m+1) ⊕ Fin n)`.
-/

open Equiv

namespace ContinuousAlternatingMap

variable {m n : ℕ}

/-- Transport a permutation of `Fin m ⊕ Fin n` to a permutation of `Fin (m + n)`. -/
noncomputable abbrev permFinOfSum (σ : Equiv.Perm (Fin m ⊕ Fin n)) : Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.permCongr σ : Equiv.Perm (Fin (m + n)))

/-- The identification `Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1)`. -/
noncomputable abbrev finSuccSumEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1) :=
  finSumFinEquiv.trans Fin.finAddFlipAssoc

/-- Given `k : Fin (m + n + 1)` and `σ : Perm (Fin m ⊕ Fin n)`, construct the corresponding
permutation of `Fin (m + 1) ⊕ Fin n` for the left-differentiation Leibniz rule.

The construction:
1. Transport `σ` to `σ_fin : Perm (Fin (m + n))`.
2. Build `π := (cycleRange k)⁻¹ * decomposeFin.symm (0, σ_fin) : Perm (Fin (m + n + 1))`.
   - `π 0 = k` (the derivative position).
   - `π (j+1) = k.succAbove (σ_fin j)` (the shuffle applied to remaining positions).
   - `sign π = (-1)^k * sign σ`.
3. Conjugate by `finSuccSumEquiv` to get `Perm (Fin (m + 1) ⊕ Fin n)`. -/
noncomputable def derivShuffleLeftFwd
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  let σ_fin := permFinOfSum σ
  let π := (Fin.cycleRange k)⁻¹ * Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), σ_fin)
  finSuccSumEquiv.symm.permCongr π

/-- The derivative-position index produced by the forward map. Always `0` since
`cycleRange` places `k` at position `0`, which corresponds to `inl 0`. -/
def derivShuffleLeftIdx
    (_k : Fin (m + n + 1)) (_σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) := 0

/-- Sign of the forward-map representative: `sign τ = (-1)^k * sign σ`. -/
theorem derivShuffleLeftFwd_sign
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (derivShuffleLeftFwd k σ) =
      (-1 : ℤˣ) ^ k.val * Equiv.Perm.sign σ := by
  simp only [derivShuffleLeftFwd, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
    if_true, one_mul, permFinOfSum]

/-- `decomposeFin.symm (0, ·)` is a group homomorphism. -/
private theorem decomposeFin_symm_zero_mul (e₁ e₂ : Equiv.Perm (Fin (m + n))) :
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁) *
      Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₂) =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁ * e₂) := by
  ext x; refine Fin.cases ?_ ?_ x
  · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  · intro i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply]

/-- `decomposeFin.symm (0, ·)` preserves inverses. -/
private theorem decomposeFin_symm_zero_inv (e : Equiv.Perm (Fin (m + n))) :
    (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e))⁻¹ =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, decomposeFin_symm_zero_mul, mul_inv_cancel]
  ext x; refine Fin.cases (by simp) (fun i => by simp [Equiv.swap_self]) x

/-- Helper: `(permCongr e a)⁻¹ * (permCongr e b) = permCongr e (a⁻¹ * b)`. -/
private theorem permCongr_inv_mul {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) (a b : Equiv.Perm α) :
    (e.permCongr a)⁻¹ * (e.permCongr b) = e.permCongr (a⁻¹ * b) := by
  have hinv : e.permCongr a⁻¹ = (e.permCongr a)⁻¹ := by
    ext x; simp [Equiv.Perm.inv_def, Equiv.permCongr]; rfl
  rw [← hinv, ← Equiv.permCongr_mul]

theorem derivShuffleLeftFwd_wd (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) σ₁ σ₂) :
    (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range)
      (derivShuffleLeftFwd k σ₁) (derivShuffleLeftFwd k σ₂) := by
  rw [QuotientGroup.leftRel_apply] at h ⊢
  obtain ⟨⟨τ_l, τ_r⟩, hblock⟩ := h
  have hratio : (derivShuffleLeftFwd k σ₁)⁻¹ * (derivShuffleLeftFwd k σ₂) =
      finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
    simp only [derivShuffleLeftFwd]
    rw [permCongr_inv_mul]; congr 1
    -- ((cycleRange k)⁻¹ * D(0, P(σ₁)))⁻¹ * ((cycleRange k)⁻¹ * D(0, P(σ₂)))
    rw [mul_inv_rev, inv_inv, mul_assoc (Equiv.Perm.decomposeFin.symm _ )⁻¹,
        ← mul_assoc (Fin.cycleRange k), mul_inv_cancel, one_mul,
        decomposeFin_symm_zero_inv, decomposeFin_symm_zero_mul]
    have : (permFinOfSum σ₁)⁻¹ * permFinOfSum σ₂ = permFinOfSum (σ₁⁻¹ * σ₂) :=
      permCongr_inv_mul finSumFinEquiv σ₁ σ₂
    rw [this]
  rw [hratio, ← hblock]
  -- Now: Φ.symm.permCongr (D(0, P(sumCongr τ_l τ_r))) maps inl to inl.
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  -- D(0, P(sumCongr τ_l τ_r)) fixes 0 and permutes {1,...,m} among themselves.
  -- After Φ.symm, inl maps to inl.
  refine Fin.cases ?_ (fun a' => ?_) a
  · -- a = 0: Φ(inl 0) = 0, D(0,_) fixes 0, Φ⁻¹(0) = inl 0.
    -- These are Fin arithmetic identities through the chain of equivs.
    unfold finSuccSumEquiv; aesop;
  · -- a = a'.succ: D(0, block_perm) maps succ-shifted left elements to
    -- succ-shifted left elements. After Φ.symm, inl maps to inl.
    simp +decide [ Equiv.Perm.decomposeFin, permFinOfSum ];
    simp +decide [ Fin.finAddFlipAssoc, finSuccEquiv ];
    simp +decide [ finSuccEquiv', finCongr ];
    simp +decide [ Fin.castLE, Fin.castLT, Fin.cons ];
    simp +decide [ Fin.cases, finSumFinEquiv ];
    simp +decide [ Fin.induction, Fin.addCases ];
    simp +decide [ Fin.induction.go ]

/-! ### Rank function and injectivity helpers -/

/-- The rank of derivative position `k` among the left positions of shuffle `σ`:
the number of left-block elements of `σ` (in `Fin (m + n)`) that lie below `k`.
This is the second component of the `derivShuffleEquivLeft` bijection. -/
noncomputable def derivShuffleJ (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i : Fin m =>
    (permFinOfSum σ (Fin.castAdd n i)).val < k.val)).card, by
    calc (Finset.univ.filter _).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = m := Finset.card_fin m
      _ < m + 1 := lt_add_one m⟩

/-- Key relation: changing the representative by `sumCongr τ_l τ_r` composes the left
block index with `τ_l`. -/
private theorem permFinOfSum_mul_sumCongr_castAdd (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (τ_l : Equiv.Perm (Fin m)) (τ_r : Equiv.Perm (Fin n)) (i : Fin m) :
    permFinOfSum (σ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i) =
      permFinOfSum σ (Fin.castAdd n (τ_l i)) := by
  simp only [permFinOfSum, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl]

/-- Filtering a `Finset.univ` by `P ∘ e` has the same cardinality as filtering by `P`,
for any equivalence `e`. -/
private theorem card_filter_comp_perm {n : ℕ} (e : Equiv.Perm (Fin n))
    (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (P ∘ ⇑e)).card = (Finset.univ.filter P).card := by
  have : Finset.univ.filter (P ∘ ⇑e) =
      (Finset.univ.filter P).map e.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Function.comp_apply]
    exact ⟨fun h => ⟨e i, h, by simp⟩, fun ⟨j, hj, hji⟩ => by simpa [← hji]⟩
  rw [this, Finset.card_map]

/-- The rank function `derivShuffleJ` is well-defined on `ModSumCongr` cosets. -/
theorem derivShuffleJ_wd (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂) :
    derivShuffleJ k σ₁ = derivShuffleJ k σ₂ := by
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨τ_l, τ_r⟩, hblock⟩ := h
  -- σ₁⁻¹ * σ₂ = sumCongr τ_l τ_r, so σ₂ = σ₁ * sumCongr τ_l τ_r
  have h_sc : Equiv.Perm.sumCongr τ_l τ_r = σ₁⁻¹ * σ₂ := by
    change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hblock
  have h_eq : σ₂ = σ₁ * Equiv.Perm.sumCongr τ_l τ_r := by rw [h_sc]; group
  subst h_eq
  simp only [derivShuffleJ, Fin.mk.injEq]
  -- After substitution, the filter predicate for σ₁ * sumCongr becomes P ∘ τ_l
  show (Finset.univ.filter (fun i =>
    (permFinOfSum σ₁ (Fin.castAdd n i)).val < k.val)).card =
    (Finset.univ.filter (fun i =>
    (permFinOfSum (σ₁ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i)).val < k.val)).card
  simp_rw [permFinOfSum_mul_sumCongr_castAdd]
  exact (card_filter_comp_perm τ_l _).symm

/-- `derivShuffleLeftFwd k` is injective on `ModSumCongr` cosets: if the images
land in the same `(m+1, n)`-coset, then the inputs were in the same `(m, n)`-coset.
This is the reverse direction of `derivShuffleLeftFwd_wd`. -/
theorem derivShuffleLeftFwd_coset_injective (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
      (derivShuffleLeftFwd k σ₁) (derivShuffleLeftFwd k σ₂)) :
    QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂ := by
  rw [QuotientGroup.leftRel_apply] at h ⊢
  -- The ratio simplifies via the same computation as derivShuffleLeftFwd_wd
  have hratio : (derivShuffleLeftFwd k σ₁)⁻¹ * (derivShuffleLeftFwd k σ₂) =
      finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
    simp only [derivShuffleLeftFwd]
    rw [permCongr_inv_mul]; congr 1
    rw [mul_inv_rev, inv_inv, mul_assoc (Equiv.Perm.decomposeFin.symm _ )⁻¹,
        ← mul_assoc (Fin.cycleRange k), mul_inv_cancel, one_mul,
        decomposeFin_symm_zero_inv, decomposeFin_symm_zero_mul]
    have : (permFinOfSum σ₁)⁻¹ * permFinOfSum σ₂ = permFinOfSum (σ₁⁻¹ * σ₂) :=
      permCongr_inv_mul finSumFinEquiv σ₁ σ₂
    rw [this]
  -- The ratio is a (m+1,n)-block perm
  rw [hratio] at h
  obtain ⟨⟨s_l, s_r⟩, hs⟩ := h
  -- Need to show σ₁⁻¹ * σ₂ is an (m,n)-block perm
  -- The (m+1,n)-block perm Φ.permCongr(D(0, P(σ₁⁻¹*σ₂))) maps inl to inl.
  -- D(0, e) fixes 0 and maps (i+1) ↦ (e(i))+1, so e maps {0,...,m-1} to itself.
  -- Hence σ₁⁻¹ * σ₂ maps inl to inl.
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  -- We know Φ.permCongr(D(0, P(σ₁⁻¹*σ₂))) maps inl to inl (it's a block perm)
  have h_block : ∀ i : Fin (m + 1),
      ∃ j, finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) (Sum.inl i) = Sum.inl j := by
    intro i
    have := Equiv.Perm.sumCongrHom_apply (Fin (m + 1)) (Fin n) (s_l, s_r)
    rw [this] at hs
    exact ⟨s_l i, by rw [← hs]; simp [Equiv.sumCongr_apply]⟩
  -- Use h_block at (Fin.succ a) and hs to derive a val-level contradiction.
  -- Strategy: hs says compound = sumCongr s_l s_r. Evaluating at inl(a.succ)
  -- gives a val-level equation linking P(g)(a) to s_l(a.succ).
  -- If g(inl a) = inr c then P(g)(a).val = m + c.val, forcing s_l(a.succ).val ≥ m+1,
  -- contradicting s_l(a.succ) : Fin(m+1).
  rcases hga : (σ₁⁻¹ * σ₂) (Sum.inl a) with b | c
  · exact ⟨b, rfl⟩
  · exfalso
    have h_sc : Equiv.Perm.sumCongr s_l s_r = finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
      rwa [Equiv.Perm.sumCongrHom_apply] at hs
    set e := permFinOfSum (σ₁⁻¹ * σ₂) with he
    set D := Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e) with hD_def
    -- Fin arithmetic: Φ(inl(a.succ)) = (castAdd n a).succ
    have hΦ : finSuccSumEquiv (Sum.inl (Fin.succ a)) = (Fin.castAdd n a).succ :=
      Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
    -- D(0, e) at a .succ position
    have hD : D (Fin.castAdd n a).succ = (e (Fin.castAdd n a)).succ := by
      simp [hD_def, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    -- P(g)(castAdd n a) = natAdd m c (from hga)
    have hP : e (Fin.castAdd n a) = Fin.natAdd m c := by
      simp only [he, permFinOfSum, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
        hga, finSumFinEquiv_apply_right]
    -- So the compound perm at inl(a.succ) = Φ⁻¹((natAdd m c).succ)
    have heval : (finSuccSumEquiv.symm.permCongr D) (Sum.inl (Fin.succ a)) =
        finSuccSumEquiv.symm ((Fin.natAdd m c).succ) := by
      simp only [Equiv.permCongr_apply, Equiv.symm_symm, hΦ, hD, hP]
    -- From h_sc: inl(s_l(a.succ)) = Φ⁻¹((natAdd m c).succ)
    have h1 := DFunLike.congr_fun h_sc (Sum.inl (Fin.succ a))
    rw [heval] at h1
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl] at h1
    -- h1: Sum.inl (s_l (a.succ)) = finSuccSumEquiv.symm ((natAdd m c).succ)
    -- Apply finSuccSumEquiv to both sides, then compare vals
    apply_fun finSuccSumEquiv at h1
    simp only [Equiv.apply_symm_apply] at h1
    apply_fun Fin.val at h1
    -- LHS val = (s_l(a.succ)).val (since Φ(inl i).val = i.val)
    -- RHS val = m + c.val + 1
    simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr, finSumFinEquiv_apply_left] at h1
    have := (s_l (Fin.succ a)).isLt
    omega

/-- Forward map at the quotient level:
`(k, [σ]) ↦ ([derivShuffleLeftFwd k σ], derivShuffleJ k σ)`. -/
private noncomputable def derivShuffleFwd :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) →
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  fun p => Quotient.liftOn p.2
    (fun σ => (Quotient.mk'' (derivShuffleLeftFwd p.1 σ), derivShuffleJ p.1 σ))
    (fun σ₁ σ₂ h => Prod.ext
      (Quotient.sound' (derivShuffleLeftFwd_wd p.1 σ₁ σ₂ h))
      (derivShuffleJ_wd p.1 σ₁ σ₂ h))

/-- `derivShuffleLeftFwd k σ` sends `inl 0` to `finSuccSumEquiv.symm k`, which depends
only on `k` and not on `σ`. -/
private theorem derivShuffleLeftFwd_inl_zero (k : Fin (m + n + 1))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleLeftFwd k σ (Sum.inl 0) = finSuccSumEquiv.symm k := by
  simp only [derivShuffleLeftFwd, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.Perm.mul_apply]
  congr 1
  have h1 : finSuccSumEquiv (Sum.inl (0 : Fin (m + 1))) =
      (0 : Fin (m + n + 1)) := Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
  rw [h1, Equiv.Perm.decomposeFin_symm_apply_zero]
  exact (Fin.cycleRange k).symm_apply_eq.mpr (Fin.cycleRange_self k).symm

/-- The forward map is injective. -/
private theorem derivShuffleFwd_injective :
    Function.Injective (@derivShuffleFwd m n) := by
  intro ⟨k₁, q₁⟩ ⟨k₂, q₂⟩ h
  refine Quotient.inductionOn₂ q₁ q₂ (fun σ₁ σ₂ (h : derivShuffleFwd (k₁, ⟦σ₁⟧) =
      derivShuffleFwd (k₂, ⟦σ₂⟧)) => ?_) h
  simp only [derivShuffleFwd, Quotient.liftOn_mk] at h
  have h_coset : Quotient.mk'' (derivShuffleLeftFwd k₁ σ₁) =
      Quotient.mk'' (derivShuffleLeftFwd k₂ σ₂) := congr_arg Prod.fst h
  have h_j : derivShuffleJ k₁ σ₁ = derivShuffleJ k₂ σ₂ := congr_arg Prod.snd h
  -- Step 1: Same coset means the ratio is a block perm
  have h_rel := Quotient.exact' h_coset
  -- Step 2: From the block perm at inl 0, extract info about k₁ vs k₂
  rw [QuotientGroup.leftRel_apply] at h_rel
  obtain ⟨⟨s_l, s_r⟩, hs⟩ := h_rel
  -- The ratio (fwd k₁ σ₁)⁻¹ * (fwd k₂ σ₂) = sumCongr s_l s_r
  -- At inl 0: (fwd k₁ σ₁)⁻¹(fwd k₂ σ₂(inl 0)) = inl(s_l 0)
  -- fwd k σ(inl 0) = Φ⁻¹(k), so Φ⁻¹(k₁) and Φ⁻¹(k₂) are in the same coset orbit
  -- Step 2a: Extract the key Fin equation from the block perm at inl 0.
  -- (fwd k₁ σ₁)(inl(s_l 0)) = (fwd k₂ σ₂)(inl 0) = Φ⁻¹(k₂)
  -- and (fwd k₁ σ₁)(inl 0) = Φ⁻¹(k₁)
  -- So Φ⁻¹(k₂) = (fwd k₁ σ₁)(inl(s_l 0))
  have h_ratio_at_zero : (derivShuffleLeftFwd k₁ σ₁) (Sum.inl (s_l 0)) =
      finSuccSumEquiv.symm k₂ := by
    have h_sc : Equiv.Perm.sumCongr s_l s_r = (derivShuffleLeftFwd k₁ σ₁)⁻¹ *
        (derivShuffleLeftFwd k₂ σ₂) := by
      rwa [Equiv.Perm.sumCongrHom_apply] at hs
    have h_eval := DFunLike.congr_fun h_sc (Sum.inl 0)
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, derivShuffleLeftFwd_inl_zero] at h_eval
    apply_fun (derivShuffleLeftFwd k₁ σ₁) at h_eval
    simpa only [Equiv.apply_symm_apply] using h_eval
  -- Step 2b: k₁ = k₂ by injectivity of Φ⁻¹ and fwd k₁ σ₁
  have h_k_eq : k₁ = k₂ := by
    -- If s_l 0 = 0, then (fwd k₁ σ₁)(inl 0) = Φ⁻¹(k₂), but also = Φ⁻¹(k₁),
    -- so k₁ = k₂ by injectivity of Φ⁻¹.
    -- If s_l 0 ≠ 0, we derive a contradiction from h_j (rank equality):
    -- The rank derivShuffleJ counts left positions below k.
    -- Since k₁ ∈ L' and k₂ ∈ L' (the shared left-position set),
    -- and k₁ ≠ k₂, the ranks must differ. This contradicts h_j.
    by_contra h_ne
    -- k₁ ≠ k₂ implies s_l 0 ≠ 0 (from the equations above)
    have h_sl_ne : s_l 0 ≠ 0 := by
      intro h_eq; apply h_ne
      have h1 := derivShuffleLeftFwd_inl_zero k₁ σ₁
      rw [h_eq] at h_ratio_at_zero
      rw [h1] at h_ratio_at_zero
      exact finSuccSumEquiv.symm.injective h_ratio_at_zero
    -- The rank equality h_j combined with k₁ ≠ k₂ in the same left-position
    -- set leads to a contradiction. Both k₁, k₂ ∈ L' (as Φ-images of inl 0
    -- under fwd k₁ σ₁ and fwd k₂ σ₂ resp.), and derivShuffleJ computes the
    -- rank of k in L'. Rank is injective on a finite set: if k₁ < k₂, then
    -- rank(k₂) > rank(k₁) since k₁ ∈ L' contributes an extra count below k₂.
    -- This is a counting argument on Finsets.
    sorry
  subst h_k_eq
  -- Step 3: Same k, same coset → same [σ] (coset injectivity)
  ext1
  · rfl
  · exact Quotient.sound' (derivShuffleLeftFwd_coset_injective k₁ σ₁ σ₂
      (Quotient.exact' h_coset))

/-- The assembled bijection. -/
noncomputable def derivShuffleEquivLeft :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) ≃
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  Equiv.ofBijective derivShuffleFwd
    ((Fintype.bijective_iff_injective_and_card derivShuffleFwd).mpr
      ⟨derivShuffleFwd_injective, by
        -- card(Fin(m+n+1) × Sh(m,n)) = (m+n+1)·C(m+n,m) = C(m+n+1,m+1)·(m+1)
        --   = card(Sh(m+1,n) × Fin(m+1))
        sorry⟩)

/-- Sign preservation for the assembled bijection.

The original (incorrect) version universally quantified over arbitrary independent
representatives `σ_rep` and `τ_rep`. This fails because changing representatives within
their cosets changes signs by independent block-permutation factors. The correct statement
uses the canonical `Quotient.out'` representatives, making this a concrete equation. -/
theorem derivShuffleEquivLeft_sign
    (p : Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) :
    ((-1 : ℤˣ) ^ p.1.val * Equiv.Perm.sign p.2.out : ℤˣ) =
      Equiv.Perm.sign (derivShuffleEquivLeft p).1.out *
        (-1) ^ (derivShuffleEquivLeft p).2.val :=
  sorry

end ContinuousAlternatingMap
