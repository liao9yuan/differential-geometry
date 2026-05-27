import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Polygonal-loop reduction for countability of the fundamental group

This file decomposes the classical Hatcher §1.3 / Spanier §2.4 polygonal
reduction into reusable sublemmas, culminating in a surjection from a
countable indexing set onto `FundamentalGroup X x` for second-countable
connected locally-path-connected semi-locally-simply-connected spaces.

The five declarations:

* `uc_pi1_countable_basis_refinement` — refine a countable basis to
  path-connected opens with null-homotopic ambient loops.
* `uc_pi1_countable_anchors` — choose an anchor point in each nonempty
  pairwise intersection.
* `uc_pi1_countable_lebesgue_subdivision` — Lebesgue-number subdivision
  of `[0,1]` adapted to a loop's pullback cover.
* `uc_pi1_countable_piece_homotopy` — homotopy uniqueness of paths
  inside a single basis element with matching endpoints.
* `uc_pi1_countable_polygonal_enumeration` — the headline countable
  surjection onto the fundamental group.
-/

open Set Function

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

/-- **Basis refinement.** Any second-countable, locally-path-connected,
semi-locally-simply-connected space admits a countable basis of
open path-connected sets each of whose ambient loops are null-homotopic
in the whole space.

The `[Nonempty X]` hypothesis is mathematically necessary: the conclusion
demands `∀ n, IsPathConnected (B n)`, which forces every `B n` to be
nonempty. Downstream consumers always have it (via `[ConnectedSpace X]`). -/
theorem uc_pi1_countable_basis_refinement
    (X : Type*) [TopologicalSpace X] [Nonempty X]
    [SecondCountableTopology X]
    [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X] :
    ∃ B : ℕ → Set X,
      (∀ n, IsOpen (B n)) ∧
      (∀ n, IsPathConnected (B n)) ∧
      (∀ n, ∀ (x : X) (_ : x ∈ B n) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ B n →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧) ∧
      TopologicalSpace.IsTopologicalBasis (Set.range B) := by
  classical
  -- Define the predicate selecting "good" basis sets: open, path-connected,
  -- and contained in a semi-local-simply-connected witness neighbourhood of
  -- some interior point. Such sets automatically have the all-basepoint
  -- null-homotopy property (proved via conjugation by an in-set path).
  let Good : Set (Set X) :=
    { V : Set X |
        IsOpen V ∧ IsPathConnected V ∧
        ∃ y ∈ V, ∃ Wy ∈ nhds y, V ⊆ Wy ∧
          (∀ γ : _root_.Path y y,
              Set.range γ.toContinuousMap ⊆ Wy →
                (⟦γ⟧ : _root_.Path.Homotopic.Quotient y y)
                  = ⟦_root_.Path.refl y⟧) }
  -- Key technical lemma: every `V ∈ Good` has the all-basepoint null-homotopy
  -- property. Argument: conjugate a loop at `x ∈ V` by a path in `V` from
  -- the distinguished base `y` to `x`.
  have hGood_null :
      ∀ V ∈ Good, ∀ (x : X) (_ : x ∈ V) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ V →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
    rintro V ⟨_hVopen, hVpc, y, hyV, Wy, _hWynhd, hVWy, hWynull⟩ x hxV γ hγV
    -- Pull the range condition back to a pointwise membership statement.
    have hγV' : ∀ t : unitInterval, γ t ∈ V := by
      intro t
      have ht : (γ t : X) ∈ Set.range γ.toContinuousMap :=
        ⟨t, by simp [Path.coe_toContinuousMap]⟩
      exact hγV ht
    -- Path `α : y → x` inside `V`, via path-connectedness of `V`.
    obtain ⟨α, hα⟩ : JoinedIn V y x := hVpc.joinedIn y hyV x hxV
    -- Conjugated loop `δ = α · γ · α.symm : Path y y` lies in `V ⊆ Wy`.
    set δ : _root_.Path y y := α.trans (γ.trans α.symm) with hδdef
    have hδRange : Set.range δ.toContinuousMap ⊆ Wy := by
      have hα_range : Set.range (α : unitInterval → X) ⊆ V := by
        rintro _ ⟨t, rfl⟩; exact hα t
      have hαsymm_range : Set.range (α.symm : unitInterval → X) ⊆ V := by
        rw [Path.symm_range]; exact hα_range
      have hγ_range : Set.range (γ : unitInterval → X) ⊆ V := by
        rintro _ ⟨t, rfl⟩; exact hγV' t
      have hinner : Set.range ((γ.trans α.symm) : unitInterval → X) ⊆ V := by
        rw [Path.trans_range]
        exact Set.union_subset hγ_range hαsymm_range
      have houter : Set.range (δ : unitInterval → X) ⊆ V := by
        change Set.range ((α.trans (γ.trans α.symm)) : unitInterval → X) ⊆ V
        rw [Path.trans_range]
        exact Set.union_subset hα_range hinner
      intro z hz
      rcases hz with ⟨t, ht⟩
      have hzV : z ∈ Set.range (δ : unitInterval → X) :=
        ⟨t, by simpa [Path.coe_toContinuousMap] using ht⟩
      exact hVWy (houter hzV)
    have hδnull :
        (⟦δ⟧ : _root_.Path.Homotopic.Quotient y y)
            = ⟦_root_.Path.refl y⟧ := hWynull δ hδRange
    -- Algebraic cancellation. Let A := ⟦α⟧, G := ⟦γ⟧, Asym := ⟦α.symm⟧ = A.symm.
    set A : _root_.Path.Homotopic.Quotient y x := ⟦α⟧ with hAdef
    set G : _root_.Path.Homotopic.Quotient x x := ⟦γ⟧ with hGdef
    set Asym : _root_.Path.Homotopic.Quotient x y :=
      _root_.Path.Homotopic.Quotient.symm A with hAsymdef
    have hδ_quot :
        (⟦δ⟧ : _root_.Path.Homotopic.Quotient y y)
          = _root_.Path.Homotopic.Quotient.trans A
              (_root_.Path.Homotopic.Quotient.trans G Asym) := by
      have e1 :
          (⟦α.trans (γ.trans α.symm)⟧ : _root_.Path.Homotopic.Quotient y y)
            = _root_.Path.Homotopic.Quotient.trans
                (⟦α⟧ : _root_.Path.Homotopic.Quotient y x)
                (⟦γ.trans α.symm⟧ : _root_.Path.Homotopic.Quotient x y) :=
        _root_.Path.Homotopic.Quotient.mk_trans α (γ.trans α.symm)
      have e2 :
          (⟦γ.trans α.symm⟧ : _root_.Path.Homotopic.Quotient x y)
            = _root_.Path.Homotopic.Quotient.trans
                (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x)
                (⟦α.symm⟧ : _root_.Path.Homotopic.Quotient x y) :=
        _root_.Path.Homotopic.Quotient.mk_trans γ α.symm
      have e3 :
          (⟦α.symm⟧ : _root_.Path.Homotopic.Quotient x y)
            = _root_.Path.Homotopic.Quotient.symm
                (⟦α⟧ : _root_.Path.Homotopic.Quotient y x) :=
        _root_.Path.Homotopic.Quotient.mk_symm α
      change (⟦α.trans (γ.trans α.symm)⟧ : _root_.Path.Homotopic.Quotient y y)
            = _root_.Path.Homotopic.Quotient.trans A
                (_root_.Path.Homotopic.Quotient.trans G
                  (_root_.Path.Homotopic.Quotient.symm A))
      rw [e1, e2, e3]
    have href :
        (⟦_root_.Path.refl y⟧ : _root_.Path.Homotopic.Quotient y y)
          = _root_.Path.Homotopic.Quotient.refl y :=
      _root_.Path.Homotopic.Quotient.mk_refl y
    have hconj :
        _root_.Path.Homotopic.Quotient.trans A
            (_root_.Path.Homotopic.Quotient.trans G Asym)
          = _root_.Path.Homotopic.Quotient.refl y := by
      rw [← hδ_quot, hδnull, href]
    have hAsymA :
        _root_.Path.Homotopic.Quotient.trans Asym A
          = _root_.Path.Homotopic.Quotient.refl x := by
      simp [hAsymdef, _root_.Path.Homotopic.Quotient.symm_trans]
    -- From `A · (G · Asym) = refl_y` derive `A · G = A`,
    -- then `G = Asym · A · G = Asym · A = refl_x`.
    have h_AG_eq_A :
        _root_.Path.Homotopic.Quotient.trans A G = A := by
      have hassoc :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans A G) Asym
            = _root_.Path.Homotopic.Quotient.trans A
                (_root_.Path.Homotopic.Quotient.trans G Asym) :=
        _root_.Path.Homotopic.Quotient.trans_assoc A G Asym
      have h_AGAsym_refl :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans A G) Asym
            = _root_.Path.Homotopic.Quotient.refl y := by
        rw [hassoc]; exact hconj
      have step :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.refl y) A := by
        rw [h_AGAsym_refl]
      have hAG_simpl :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans A G := by
        calc _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G)
                (_root_.Path.Homotopic.Quotient.trans Asym A) := by
              rw [_root_.Path.Homotopic.Quotient.trans_assoc]
          _ = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G)
                (_root_.Path.Homotopic.Quotient.refl x) := by rw [hAsymA]
          _ = _root_.Path.Homotopic.Quotient.trans A G :=
              _root_.Path.Homotopic.Quotient.trans_refl _
      have h_refl_A :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.refl y) A = A :=
        _root_.Path.Homotopic.Quotient.refl_trans A
      rw [← hAG_simpl, step, h_refl_A]
    have hG_eq :
        G = _root_.Path.Homotopic.Quotient.trans Asym
              (_root_.Path.Homotopic.Quotient.trans A G) := by
      calc G
          = _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.refl x) G :=
            (_root_.Path.Homotopic.Quotient.refl_trans G).symm
        _ = _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans Asym A) G := by rw [hAsymA]
        _ = _root_.Path.Homotopic.Quotient.trans Asym
              (_root_.Path.Homotopic.Quotient.trans A G) := by
            rw [_root_.Path.Homotopic.Quotient.trans_assoc]
    rw [hG_eq, h_AG_eq_A]; exact hAsymA
  -- `Good` is a topological basis.
  have hGood_basis : TopologicalSpace.IsTopologicalBasis Good := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · intro V hV; exact hV.1
    · intro x W hxW hWopen
      obtain ⟨Wx, hWxNhd, hWxNull⟩ :=
        DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace.out
          (X := X) x
      have hWxW : Wx ∩ W ∈ nhds x := Filter.inter_mem hWxNhd (hWopen.mem_nhds hxW)
      have hbasis := isOpen_isPathConnected_basis (x := x)
      obtain ⟨V, ⟨hVopen, hxV, hVpc⟩, hVsub⟩ := hbasis.mem_iff.mp hWxW
      refine ⟨V, ?_, hxV, hVsub.trans Set.inter_subset_right⟩
      refine ⟨hVopen, hVpc, x, hxV, Wx, hWxNhd, ?_, ?_⟩
      · exact fun z hz => (hVsub hz).1
      · intro γ hγ; exact hWxNull γ hγ
  -- Extract a countable basis `s ⊆ Good`.
  obtain ⟨s, hs_sub, hs_count, hs_basis⟩ := hGood_basis.exists_countable
  -- `s` is nonempty since `X` is nonempty (its sUnion equals `univ`).
  have hs_nonempty : s.Nonempty := by
    have huniv : (⋃₀ s) = (Set.univ : Set X) := hs_basis.sUnion_eq
    obtain ⟨x₀⟩ := ‹Nonempty X›
    have hx₀ : x₀ ∈ ⋃₀ s := by rw [huniv]; trivial
    rcases hx₀ with ⟨V, hVs, _⟩; exact ⟨V, hVs⟩
  obtain ⟨B, hBrange⟩ := hs_count.exists_eq_range hs_nonempty
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro n
    have : B n ∈ s := by rw [hBrange]; exact ⟨n, rfl⟩
    exact (hs_sub this).1
  · intro n
    have : B n ∈ s := by rw [hBrange]; exact ⟨n, rfl⟩
    exact (hs_sub this).2.1
  · intro n x hxBn γ hγ
    have hBnGood : B n ∈ Good := hs_sub (by rw [hBrange]; exact ⟨n, rfl⟩)
    exact hGood_null (B n) hBnGood x hxBn γ hγ
  · rw [← hBrange]; exact hs_basis

/-- **Countable anchors.** Given a countable basis `B`, choose, for every
ordered pair of indices `(m, n)` whose corresponding basis sets meet,
a point of `B m ∩ B n`. -/
theorem uc_pi1_countable_anchors
    (X : Type*) [TopologicalSpace X] [Nonempty X]
    (B : ℕ → Set X) :
    ∃ anchor : ℕ × ℕ → X,
      ∀ p : ℕ × ℕ, (B p.1 ∩ B p.2).Nonempty → anchor p ∈ B p.1 ∩ B p.2 := by
  classical
  refine ⟨fun p => if h : (B p.1 ∩ B p.2).Nonempty then h.choose
                   else Classical.arbitrary X, ?_⟩
  intro p hp
  simp only [hp, dif_pos]
  exact hp.choose_spec

/-- **Lebesgue subdivision for a loop.** Given a (continuous) loop
`γ : Path x x` in a space covered by `{B n}`, the pullback cover
`{γ⁻¹(B n)}` of `[0,1]` admits a finite subdivision `0 = t₀ < … < t_k = 1`
together with an index map `j : Fin k → ℕ` such that
`γ '' Icc tⱼ tⱼ₊₁ ⊆ B (j idx)`. -/
theorem uc_pi1_countable_lebesgue_subdivision
    (X : Type*) [TopologicalSpace X]
    (B : ℕ → Set X) (hBopen : ∀ n, IsOpen (B n))
    (hBcov : (⋃ n, B n) = Set.univ)
    {x : X} (γ : _root_.Path x x) :
    ∃ (k : ℕ) (t : Fin (k + 1) → unitInterval) (idx : Fin k → ℕ),
      t 0 = 0 ∧ t (Fin.last k) = 1 ∧
      (∀ i : Fin k, (t i.castSucc : ℝ) ≤ (t i.succ : ℝ)) ∧
      (∀ i : Fin k,
        ∀ s : unitInterval,
          (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
            γ s ∈ B (idx i)) := by
  classical
  -- Pullback cover of the unit interval by open sets.
  have hγ : Continuous (γ : unitInterval → X) := map_continuous γ
  have hUopen : ∀ n, IsOpen (γ ⁻¹' B n) := fun n => (hBopen n).preimage hγ
  have hUcov : (Set.univ : Set unitInterval) ⊆ ⋃ n, γ ⁻¹' B n := by
    intro s _
    have : (γ s : X) ∈ (⋃ n, B n) := by rw [hBcov]; trivial
    rcases Set.mem_iUnion.mp this with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  -- Apply the Lebesgue-number lemma on the compact metric space `unitInterval`.
  have hcpt : IsCompact (Set.univ : Set unitInterval) :=
    CompactSpace.isCompact_univ
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric hcpt hUopen hUcov
  -- Choose `k ≥ 1` such that `1/k < δ`.
  set k : ℕ := ⌊1 / δ⌋₊ + 1 with hkdef
  have hkpos : 0 < k := Nat.succ_pos _
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hkinv : 1 / (k : ℝ) < δ := by
    have hk_gt : (1 / δ : ℝ) < (k : ℝ) := by
      have := Nat.lt_floor_add_one (1 / δ)
      simpa [hkdef, Nat.cast_add, Nat.cast_one] using this
    have hδ_inv_pos : 0 < 1 / δ := by positivity
    have : 1 / (k : ℝ) < 1 / (1 / δ) := by
      apply one_div_lt_one_div_of_lt hδ_inv_pos hk_gt
    simpa using this
  -- Define the equispaced subdivision `t i = i / k ∈ [0,1]`.
  have hmem : ∀ i : Fin (k + 1), (i : ℝ) / k ∈ unitInterval := by
    intro i
    refine ⟨div_nonneg (by positivity) hkR.le, ?_⟩
    have hle : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
    have : ((i : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
    exact (div_le_one hkR).mpr this
  let t : Fin (k + 1) → unitInterval := fun i => ⟨(i : ℝ) / k, hmem i⟩
  -- For each segment, pick a witness basis index via the Lebesgue number.
  have hchoose : ∀ i : Fin k, ∃ n, ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
        γ s ∈ B n := by
    intro i
    have hmemU : t i.castSucc ∈ (Set.univ : Set unitInterval) := Set.mem_univ _
    obtain ⟨n, hn⟩ := hδ (t i.castSucc) hmemU
    refine ⟨n, ?_⟩
    intro s hs₁ hs₂
    -- Show `s ∈ Metric.ball (t i.castSucc) δ`.
    have hd : dist s (t i.castSucc) < δ := by
      rw [Subtype.dist_eq]
      have hcast :
          (t i.castSucc : ℝ) = ((i : ℕ) : ℝ) / k := by
        simp [t]
      have hsucc :
          (t i.succ : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) / k := by
        simp [t, Fin.val_succ]
      have hdiff : (t i.succ : ℝ) - (t i.castSucc : ℝ) = 1 / k := by
        rw [hcast, hsucc]
        push_cast
        field_simp
        ring
      have habs : |(s : ℝ) - (t i.castSucc : ℝ)| ≤ 1 / k := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith
        · have : (s : ℝ) ≤ (t i.castSucc : ℝ) + 1 / k := by linarith
          linarith
      have : |(s : ℝ) - (t i.castSucc : ℝ)| < δ := lt_of_le_of_lt habs hkinv
      simpa [Real.dist_eq] using this
    have hball : s ∈ Metric.ball (t i.castSucc) δ := hd
    exact hn hball
  -- Package the witness function.
  let idx : Fin k → ℕ := fun i => (hchoose i).choose
  have hidx : ∀ i : Fin k, ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
        γ s ∈ B (idx i) := fun i => (hchoose i).choose_spec
  refine ⟨k, t, idx, ?_, ?_, ?_, hidx⟩
  · -- `t 0 = 0`.
    apply Subtype.ext
    simp [t]
  · -- `t (Fin.last k) = 1`.
    apply Subtype.ext
    change ((Fin.last k : ℕ) : ℝ) / k = 1
    rw [Fin.val_last]
    exact div_self hkR.ne'
  · -- Monotonicity of `t`.
    intro i
    have hcast : (t i.castSucc : ℝ) = ((i : ℕ) : ℝ) / k := by
      simp [t]
    have hsucc : (t i.succ : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) / k := by
      simp [t, Fin.val_succ]
    rw [hcast, hsucc]
    apply div_le_div_of_nonneg_right _ hkR.le
    · exact_mod_cast Nat.le_succ _


/-- **Piece homotopy.** Two paths inside the same basis element `B n`
that share endpoints are homotopic in the ambient space, by the
semi-local condition refining the basis. -/
theorem uc_pi1_countable_piece_homotopy
    (X : Type*) [TopologicalSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (B : ℕ → Set X)
    (hBnull : ∀ n, ∀ (x : X) (_ : x ∈ B n) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ B n →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧)
    (n : ℕ) {a b : X} (γ₁ γ₂ : _root_.Path a b)
    (_h₁ : Set.range γ₁.toContinuousMap ⊆ B n)
    (_h₂ : Set.range γ₂.toContinuousMap ⊆ B n) :
    (⟦γ₁⟧ : _root_.Path.Homotopic.Quotient a b) = ⟦γ₂⟧ := by
  -- The two range hypotheses, transported through `coe_toContinuousMap`.
  have hr₁ : Set.range (γ₁ : unitInterval → X) ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    refine _h₁ ⟨t, ?_⟩
    simpa [Path.coe_toContinuousMap] using ht
  have hr₂ : Set.range (γ₂ : unitInterval → X) ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    refine _h₂ ⟨t, ?_⟩
    simpa [Path.coe_toContinuousMap] using ht
  -- `a ∈ B n` because `γ₁ 0 = a` and `γ₁ 0 ∈ range γ₁ ⊆ B n`.
  have haB : a ∈ B n := by
    have h0 : (γ₁ 0 : X) ∈ Set.range (γ₁ : unitInterval → X) := ⟨0, rfl⟩
    have : (γ₁ 0 : X) ∈ B n := hr₁ h0
    simpa using this
  -- The composed loop `γ₁ ⬝ γ₂.symm : Path a a` and its range bound.
  set δ : _root_.Path a a := γ₁.trans γ₂.symm with hδdef
  have hδrange : Set.range δ.toContinuousMap ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    have hy' : y ∈ Set.range (δ : unitInterval → X) :=
      ⟨t, by simpa [Path.coe_toContinuousMap] using ht⟩
    have hrange : Set.range (δ : unitInterval → X)
        = Set.range (γ₁ : unitInterval → X)
            ∪ Set.range (γ₂.symm : unitInterval → X) := by
      simpa [hδdef] using Path.trans_range γ₁ γ₂.symm
    rw [hrange] at hy'
    rcases hy' with hy₁ | hy₂
    · exact hr₁ hy₁
    · have : y ∈ Set.range (γ₂ : unitInterval → X) := by
        rwa [Path.symm_range] at hy₂
      exact hr₂ this
  -- Apply the null-homotopy hypothesis to the composed loop.
  have hnull :
      (⟦δ⟧ : _root_.Path.Homotopic.Quotient a a) = ⟦_root_.Path.refl a⟧ :=
    hBnull n a haB δ hδrange
  -- Group-theoretic cancellation in the quotient.
  -- Abbreviations for readability.
  let Trans : _root_.Path.Homotopic.Quotient a b →
              _root_.Path.Homotopic.Quotient b a →
              _root_.Path.Homotopic.Quotient a a :=
    _root_.Path.Homotopic.Quotient.trans
  -- We work directly with `⟦γ₁⟧` and `⟦γ₂⟧`.
  set A : _root_.Path.Homotopic.Quotient a b := ⟦γ₁⟧ with hAdef
  set Bq : _root_.Path.Homotopic.Quotient a b := ⟦γ₂⟧ with hBdef
  let Bsym : _root_.Path.Homotopic.Quotient b a :=
    _root_.Path.Homotopic.Quotient.symm Bq
  -- Rewrite the null homotopy in terms of `A` and `Bq`.
  -- `⟦γ₁ ⬝ γ₂.symm⟧ = trans A Bsym` and `⟦Path.refl a⟧ = Quotient.refl a`.
  have h1 :
      (⟦δ⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.trans A Bsym := by
    have eq₁ :
        (⟦γ₁.trans γ₂.symm⟧ : _root_.Path.Homotopic.Quotient a a)
          = _root_.Path.Homotopic.Quotient.trans
              (⟦γ₁⟧ : _root_.Path.Homotopic.Quotient a b)
              (⟦γ₂.symm⟧ : _root_.Path.Homotopic.Quotient b a) :=
      _root_.Path.Homotopic.Quotient.mk_trans γ₁ γ₂.symm
    have eq₂ :
        (⟦γ₂.symm⟧ : _root_.Path.Homotopic.Quotient b a)
          = _root_.Path.Homotopic.Quotient.symm
              (⟦γ₂⟧ : _root_.Path.Homotopic.Quotient a b) :=
      _root_.Path.Homotopic.Quotient.mk_symm γ₂
    change (⟦γ₁.trans γ₂.symm⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.trans A
            (_root_.Path.Homotopic.Quotient.symm Bq)
    rw [eq₁, eq₂]
  have h2 :
      (⟦_root_.Path.refl a⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.refl a :=
    _root_.Path.Homotopic.Quotient.mk_refl a
  -- Cancellation key: `trans A Bsym = refl a`.
  have hkey :
      _root_.Path.Homotopic.Quotient.trans A Bsym
        = _root_.Path.Homotopic.Quotient.refl a := by
    rw [← h1, ← h2]; exact hnull
  -- Algebraic chase: `A = A · refl b = A · (Bsym · Bq) = (A · Bsym) · Bq
  --                    = refl a · Bq = Bq`.
  have hsymm :
      _root_.Path.Homotopic.Quotient.trans Bsym Bq
        = _root_.Path.Homotopic.Quotient.refl b :=
    _root_.Path.Homotopic.Quotient.symm_trans Bq
  calc A
      = _root_.Path.Homotopic.Quotient.trans A
          (_root_.Path.Homotopic.Quotient.refl b) :=
        (_root_.Path.Homotopic.Quotient.trans_refl A).symm
    _ = _root_.Path.Homotopic.Quotient.trans A
          (_root_.Path.Homotopic.Quotient.trans Bsym Bq) := by rw [hsymm]
    _ = _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans A Bsym) Bq := by
        rw [_root_.Path.Homotopic.Quotient.trans_assoc]
    _ = _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.refl a) Bq := by rw [hkey]
    _ = Bq := _root_.Path.Homotopic.Quotient.refl_trans Bq

/-- **Polygonal enumeration.** The fundamental group of a second-countable,
connected, locally-path-connected, semi-locally-simply-connected space
admits a surjection from a countable indexing set.

Argument sketch: combine `uc_pi1_countable_basis_refinement`,
`uc_pi1_countable_anchors`, `uc_pi1_countable_lebesgue_subdivision`,
and `uc_pi1_countable_piece_homotopy` to replace any loop by a
polygonal loop indexed by a finite sequence of (basis-index, anchor-index)
pairs; the set of all such sequences is countable as `List (ℕ × ℕ)`. -/
theorem uc_pi1_countable_polygonal_enumeration
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X) :
    ∃ (S : Type) (_ : Countable S) (f : S → FundamentalGroup X x),
      Function.Surjective f := sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
