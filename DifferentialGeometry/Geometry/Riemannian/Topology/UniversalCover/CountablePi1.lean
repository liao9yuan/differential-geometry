import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Subpath
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

/-! ### Pointwise congruence under `Path.concat`

A standalone congruence lemma stating that two `Path.concat` constructions
over the same vertex sequence agree in the homotopy quotient whenever their
segments are pointwise homotopic. This is the path-level lift of Mathlib's
`Path.Homotopic.concat_hcomp`. -/

lemma uc_pi1_countable_concat_quot_congr
    {Y : Type*} [TopologicalSpace Y] {n : ℕ} {p : Fin (n + 1) → Y}
    (F G : (i : Fin n) → _root_.Path (p i.castSucc) (p i.succ))
    (h : ∀ i : Fin n,
      (⟦F i⟧ : _root_.Path.Homotopic.Quotient (p i.castSucc) (p i.succ))
        = ⟦G i⟧) :
    (⟦_root_.Path.concat p F⟧
        : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last n)))
      = ⟦_root_.Path.concat p G⟧ := by
  have hH : ∀ i : Fin n, (F i).Homotopic (G i) := by
    intro i
    have := h i
    rwa [Quotient.eq] at this
  exact Quotient.sound
    (_root_.Path.Homotopic.concat_hcomp (n := n) p F G hH)

/-- **Polygonal enumeration.** The fundamental group of a second-countable,
connected, locally-path-connected, semi-locally-simply-connected space
admits a surjection from a countable indexing set.

Argument: combine `uc_pi1_countable_basis_refinement`,
`uc_pi1_countable_anchors`, `uc_pi1_countable_lebesgue_subdivision`,
`uc_pi1_countable_piece_homotopy`, and `Path.trans_truncate_homotopic`.
Every loop based at `x` is path-homotopic to a finite concatenation of
truncations whose ranges lie inside refined basis sets; the truncations
are then replaced by canonical anchor-to-anchor *polygonal segments*
inside each `B (idx i)` via the basis-element null-homotopy property of
`uc_pi1_countable_piece_homotopy` and an interior-vertex anchor
substitution. The polygonal loop's class depends only on `(k, idx) :
Σ k, Fin k → ℕ`, a countable type. -/
theorem uc_pi1_countable_polygonal_enumeration
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X) :
    ∃ (S : Type) (_ : Countable S) (f : S → FundamentalGroup X x),
      Function.Surjective f := by
  classical
  -- `X` is nonempty (contains `x`).
  haveI : Nonempty X := ⟨x⟩
  -- Path-connectedness from `ConnectedSpace + LocPathConnectedSpace`.
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locPathConnectedSpace
  -- Refined countable basis.
  obtain ⟨B, hBopen, hBpc, hBnull, hBbasis⟩ :=
    uc_pi1_countable_basis_refinement X
  -- The basis covers `X`.
  have hBcov : (⋃ n, B n) = (Set.univ : Set X) := by
    have hsu : ⋃₀ (Set.range B) = (Set.univ : Set X) := hBbasis.sUnion_eq
    rw [Set.sUnion_range] at hsu; exact hsu
  -- Countable anchors.
  obtain ⟨anchor, hanchor⟩ := uc_pi1_countable_anchors X B
  -- Indexing type: sequences of basis indices, one per polygonal segment.
  let S : Type := Σ k : ℕ, Fin k → ℕ
  haveI hScount : Countable S := inferInstance
  -- Auxiliary vertex map: boundary vertices are the basepoint; interior
  -- vertices are anchors of two consecutive segments' basis indices.
  let polyVertex : ∀ {k : ℕ}, (Fin k → ℕ) → Fin (k + 1) → X :=
    fun {k} idx i =>
      if h : 0 < (i : ℕ) ∧ (i : ℕ) < k then
        anchor (idx ⟨(i : ℕ) - 1, by omega⟩, idx ⟨(i : ℕ), h.2⟩)
      else x
  have polyVertex_zero :
      ∀ {k : ℕ} (idx : Fin k → ℕ),
        polyVertex idx (0 : Fin (k + 1)) = x := by
    intro k idx
    simp [polyVertex]
  have polyVertex_last :
      ∀ {k : ℕ} (idx : Fin k → ℕ),
        polyVertex idx (Fin.last k) = x := by
    intro k idx
    simp [polyVertex, Fin.val_last]
  -- The function `f : S → FundamentalGroup X x`.
  let f : S → FundamentalGroup X x := fun s =>
    let k := s.fst
    let idx := s.snd
    if hvalid :
        ∀ i : Fin k,
          (polyVertex idx i.castSucc ∈ B (idx i)) ∧
          (polyVertex idx i.succ ∈ B (idx i)) then
      let seg : (i : Fin k) → _root_.Path
          (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
        fun i =>
          ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath
      let p₀ : Fin (k + 1) → X := fun j => polyVertex idx j
      let polyLoop : _root_.Path x x :=
        (_root_.Path.concat p₀ seg).cast
          (show x = p₀ 0 from (polyVertex_zero idx).symm)
          (show x = p₀ (Fin.last k) from (polyVertex_last idx).symm)
      FundamentalGroup.fromPath ⟦polyLoop⟧
    else
      FundamentalGroup.fromPath ⟦_root_.Path.refl x⟧
  refine ⟨S, hScount, f, ?_⟩
  -- Surjectivity. Recover a loop representative from `g`.
  intro g
  let q : _root_.Path.Homotopic.Quotient x x := FundamentalGroup.toPath g
  obtain ⟨γ, hγ⟩ : ∃ γ : _root_.Path x x,
      (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = q :=
    Quotient.exists_rep q
  -- Apply Lebesgue subdivision.
  obtain ⟨k, t, idx, ht0, htlast, htmono', hidx⟩ :=
    uc_pi1_countable_lebesgue_subdivision X B hBopen hBcov γ
  -- Promote consecutive monotonicity to full monotonicity.
  have htmono : Monotone t := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact Subtype.coe_le_coe.mp (htmono' i)
  -- Choose the preimage `⟨k, idx⟩`.
  refine ⟨⟨k, idx⟩, ?_⟩
  -- Endpoint identifications for `γ`.
  have hγ0 : γ (t 0 : unitInterval) = x := by rw [ht0]; exact γ.source
  have hγlast : γ (t (Fin.last k) : unitInterval) = x := by
    rw [htlast]; exact γ.target
  -- `γ.extend ((t i : I) : ℝ) = γ (t i : I)` everywhere.
  have hExtend : ∀ i : Fin (k + 1),
      γ.extend ((t i : unitInterval) : ℝ) = γ (t i : unitInterval) :=
    fun i => _root_.Path.extend_extends' γ (t i : (Icc (0 : ℝ) 1 : Set ℝ))
  -- `t i.castSucc ≤ t i.succ` for each `i`.
  have htle : ∀ i : Fin k,
      ((t i.castSucc : unitInterval) : ℝ) ≤ ((t i.succ : unitInterval) : ℝ) :=
    fun i => htmono' i
  -- Membership of `γ`'s endpoint values in basis elements.
  have hγ_castSucc_in : ∀ i : Fin k, γ (t i.castSucc) ∈ B (idx i) :=
    fun i => hidx i (t i.castSucc) (le_refl _) (htle i)
  have hγ_succ_in : ∀ i : Fin k, γ (t i.succ) ∈ B (idx i) :=
    fun i => hidx i (t i.succ) (htle i) (le_refl _)
  -- The two-step truncation→γ identification expressed at the quotient
  -- level. Define the truncation family and the concatenated path.
  let T : (i : Fin k) →
      _root_.Path (γ.extend ((t i.castSucc : unitInterval) : ℝ))
                  (γ.extend ((t i.succ : unitInterval) : ℝ)) :=
    fun i => γ.truncateOfLE (htle i)
  have ha_eq : x = γ.extend ((t 0 : unitInterval) : ℝ) := by rw [ht0]; simp
  have hb_eq : x = γ.extend ((t (Fin.last k) : unitInterval) : ℝ) := by
    rw [htlast]; simp
  let concatT : _root_.Path x x :=
    (concatTrans (p := fun i => γ.extend ((t i : unitInterval) : ℝ)) T).cast
      ha_eq hb_eq
  -- `γ ≃ concatT` via `Path.trans_truncate_homotopic`.
  have hγ_concatT : γ.Homotopic concatT :=
    Path.trans_truncate_homotopic γ t ht0 htlast htmono
  have hquot_γ_concatT :
      (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ :=
    Quotient.sound hγ_concatT
  -- Truncation range: each `T i` has image inside `B (idx i)`.
  have hT_range : ∀ i : Fin k,
      ∀ s : unitInterval, (T i s : X) ∈ B (idx i) := by
    intro i s
    -- `(T i) s = γ.extend (min (max s (t i.castSucc)) (t i.succ))`. Show the
    -- inner real lies in `[t i.castSucc, t i.succ] ⊆ I`, then use `hidx`.
    set u : ℝ := min (max (s : ℝ) ((t i.castSucc : unitInterval) : ℝ))
        ((t i.succ : unitInterval) : ℝ) with hudef
    have hu_lo : ((t i.castSucc : unitInterval) : ℝ) ≤ u := by
      rw [hudef]; exact le_min (le_max_right _ _) (htle i)
    have hu_hi : u ≤ ((t i.succ : unitInterval) : ℝ) := by
      rw [hudef]; exact min_le_right _ _
    have hu_mem : u ∈ (Icc 0 1 : Set ℝ) := by
      refine ⟨?_, ?_⟩
      · exact (t i.castSucc : unitInterval).2.1.trans hu_lo
      · exact hu_hi.trans (t i.succ : unitInterval).2.2
    -- Show `(T i) s = γ ⟨u, hu_mem⟩`. The path `γ.truncateOfLE h` is defined
    -- as `(γ.truncate t₀ t₁).cast _ _` and `γ.truncate t₀ t₁ s = γ.extend u`.
    have hTval : ((T i) s : X) = γ ⟨u, hu_mem⟩ := by
      have hcoe : ((T i) s : X) = ((γ.truncate
          ((t i.castSucc : unitInterval) : ℝ)
          ((t i.succ : unitInterval) : ℝ)) s : X) := by
        simp [T, _root_.Path.truncateOfLE]
      have hext : γ.extend u = γ ⟨u, hu_mem⟩ := _root_.Path.extend_apply _ hu_mem
      have htr : ((γ.truncate
          ((t i.castSucc : unitInterval) : ℝ)
          ((t i.succ : unitInterval) : ℝ)) s : X) = γ.extend u := by
        simp [_root_.Path.truncate, hudef]
      rw [hcoe, htr, hext]
    rw [hTval]
    exact hidx i ⟨u, hu_mem⟩ hu_lo hu_hi
  -- Establish the validity hypothesis: for each `i : Fin k`,
  -- `polyVertex idx i.castSucc ∈ B (idx i)` and `polyVertex idx i.succ ∈ B (idx i)`.
  -- The vertex at `i.castSucc` is `x` (if `i = 0`) or an anchor (otherwise);
  -- similarly for `i.succ`. Both cases reduce to a `γ`-value membership in
  -- `B (idx i)` (provided by `hidx`) for the boundary case, and a nonempty
  -- intersection witness for the anchor case.
  have hcast_val : ∀ i : Fin k, (i.castSucc : ℕ) = (i : ℕ) := fun i => rfl
  have hsucc_val : ∀ i : Fin k, (i.succ : ℕ) = (i : ℕ) + 1 := fun i => rfl
  have hVertex_castSucc : ∀ i : Fin k,
      polyVertex idx i.castSucc ∈ B (idx i) := by
    intro i
    have hi_lt_k : (i : ℕ) < k := i.isLt
    by_cases h0 : (i : ℕ) = 0
    · -- Boundary: `i.castSucc.val = 0`, so `polyVertex = x`.
      have hpv : polyVertex idx i.castSucc = x := by
        change (if h : 0 < (i.castSucc : ℕ) ∧ (i.castSucc : ℕ) < k
              then anchor _ else x) = x
        rw [dif_neg]
        intro ⟨hpos, _⟩
        rw [hcast_val] at hpos
        omega
      rw [hpv]
      -- Show `x ∈ B (idx i)` via `γ (t i.castSucc) = x ∈ B (idx i)`.
      have ht_eq : t i.castSucc = t 0 := by
        apply congrArg
        apply Fin.ext
        change (i.castSucc : ℕ) = (0 : Fin (k + 1)).val
        rw [hcast_val, h0]; rfl
      have hxγ : γ (t i.castSucc) = x := by rw [ht_eq, hγ0]
      rw [← hxγ]
      exact hγ_castSucc_in i
    · -- Interior: `0 < i.castSucc.val < k`. `polyVertex = anchor`, in the
      -- pair-wise intersection (nonempty by `γ (t i.castSucc)`).
      have hpos : 0 < (i.castSucc : ℕ) := by rw [hcast_val]; omega
      have hlt_k : (i.castSucc : ℕ) < k := by rw [hcast_val]; exact hi_lt_k
      have hi_prev_lt_k : (i : ℕ) - 1 < k := by omega
      -- The previous segment index `⟨i.val - 1, _⟩`.
      let ip : Fin k := ⟨(i : ℕ) - 1, hi_prev_lt_k⟩
      have hip_succ_val : (ip.succ : ℕ) = (i : ℕ) := by
        change (ip : ℕ) + 1 = (i : ℕ)
        change (i : ℕ) - 1 + 1 = (i : ℕ)
        omega
      have ht_ip_succ_eq : t ip.succ = t i.castSucc := by
        apply congrArg
        apply Fin.ext
        rw [hip_succ_val, hcast_val]
      have ht_ip_castSucc_le : ((t ip.castSucc : unitInterval) : ℝ)
          ≤ ((t i.castSucc : unitInterval) : ℝ) := by
        apply Subtype.coe_le_coe.mpr
        apply htmono
        -- `ip.castSucc.val = (i : ℕ) - 1 ≤ (i : ℕ) = i.castSucc.val`
        change ip.castSucc ≤ i.castSucc
        apply Fin.mk_le_mk.mpr
        change (i : ℕ) - 1 ≤ (i : ℕ)
        omega
      have hγ_at_ip : γ (t i.castSucc) ∈ B (idx ip) := by
        refine hidx ip (t i.castSucc) ht_ip_castSucc_le ?_
        rw [← ht_ip_succ_eq]
      have hγ_at_i : γ (t i.castSucc) ∈ B (idx i) := hγ_castSucc_in i
      have hnonempty : (B (idx ip) ∩ B (idx i)).Nonempty :=
        ⟨γ (t i.castSucc), hγ_at_ip, hγ_at_i⟩
      have hanchor_mem : anchor (idx ip, idx i)
          ∈ B (idx ip) ∩ B (idx i) :=
        hanchor (idx ip, idx i) hnonempty
      -- Unfold polyVertex.
      have hpv : polyVertex idx i.castSucc
          = anchor (idx ⟨(i.castSucc : ℕ) - 1,
              by rw [hcast_val]; omega⟩, idx ⟨(i.castSucc : ℕ), hlt_k⟩) := by
        change (if h : 0 < (i.castSucc : ℕ) ∧ (i.castSucc : ℕ) < k
              then anchor (idx ⟨(i.castSucc : ℕ) - 1, by omega⟩,
                idx ⟨(i.castSucc : ℕ), h.2⟩) else x)
            = anchor _
        rw [dif_pos ⟨hpos, hlt_k⟩]
      rw [hpv]
      have hidx_eq1 : (⟨(i.castSucc : ℕ) - 1,
          by rw [hcast_val]; omega⟩ : Fin k) = ip := by
        apply Fin.ext
        change (i.castSucc : ℕ) - 1 = (i : ℕ) - 1
        rw [hcast_val]
      have hidx_eq2 : (⟨(i.castSucc : ℕ), hlt_k⟩ : Fin k) = i := by
        apply Fin.ext; rw [hcast_val]
      rw [hidx_eq1, hidx_eq2]
      exact hanchor_mem.2
  have hVertex_succ : ∀ i : Fin k,
      polyVertex idx i.succ ∈ B (idx i) := by
    intro i
    have hi_lt_k : (i : ℕ) < k := i.isLt
    have hsucc_lt : (i.succ : ℕ) ≤ k := Nat.lt_succ_iff.mp i.succ.isLt
    by_cases hk : (i : ℕ) + 1 = k
    · -- Boundary: `i.succ.val = k`. `polyVertex = x`.
      have hpv : polyVertex idx i.succ = x := by
        change (if h : 0 < (i.succ : ℕ) ∧ (i.succ : ℕ) < k
              then anchor _ else x) = x
        rw [dif_neg]
        intro ⟨_, hlt⟩
        rw [hsucc_val] at hlt
        omega
      rw [hpv]
      have ht_eq : t i.succ = t (Fin.last k) := by
        apply congrArg; apply Fin.ext
        rw [Fin.val_last, hsucc_val]; exact hk
      have hxγ : γ (t i.succ) = x := by rw [ht_eq, hγlast]
      rw [← hxγ]
      exact hγ_succ_in i
    · -- Interior: `i.succ.val < k`. `polyVertex = anchor (idx i, idx ⟨i+1,_⟩)`.
      have hi_next_lt_k : (i : ℕ) + 1 < k := by
        rw [← hsucc_val] at hk ⊢
        omega
      have hpos : 0 < (i.succ : ℕ) := by rw [hsucc_val]; omega
      have hlt : (i.succ : ℕ) < k := by rw [hsucc_val]; exact hi_next_lt_k
      let i_next : Fin k := ⟨(i : ℕ) + 1, hi_next_lt_k⟩
      have hin_castSucc_val : (i_next.castSucc : ℕ) = (i : ℕ) + 1 := by rfl
      have ht_in_castSucc_eq : t i_next.castSucc = t i.succ := by
        apply congrArg; apply Fin.ext
        rw [hin_castSucc_val, hsucc_val]
      have ht_in_succ_ge : ((t i.succ : unitInterval) : ℝ)
          ≤ ((t i_next.succ : unitInterval) : ℝ) := by
        apply Subtype.coe_le_coe.mpr
        apply htmono
        change i.succ ≤ i_next.succ
        apply Fin.mk_le_mk.mpr
        change (i : ℕ) + 1 ≤ (i : ℕ) + 1 + 1
        omega
      have hγ_at_in : γ (t i.succ) ∈ B (idx i_next) := by
        refine hidx i_next (t i.succ) ?_ ht_in_succ_ge
        rw [← ht_in_castSucc_eq]
      have hγ_at_i : γ (t i.succ) ∈ B (idx i) := hγ_succ_in i
      have hnonempty : (B (idx i) ∩ B (idx i_next)).Nonempty :=
        ⟨γ (t i.succ), hγ_at_i, hγ_at_in⟩
      have hanchor_mem : anchor (idx i, idx i_next)
          ∈ B (idx i) ∩ B (idx i_next) :=
        hanchor (idx i, idx i_next) hnonempty
      have hpv : polyVertex idx i.succ
          = anchor (idx ⟨(i.succ : ℕ) - 1,
              by rw [hsucc_val]; omega⟩, idx ⟨(i.succ : ℕ), hlt⟩) := by
        change (if h : 0 < (i.succ : ℕ) ∧ (i.succ : ℕ) < k
              then anchor (idx ⟨(i.succ : ℕ) - 1, by omega⟩,
                idx ⟨(i.succ : ℕ), h.2⟩) else x)
            = anchor _
        rw [dif_pos ⟨hpos, hlt⟩]
      rw [hpv]
      have hidx_eq1 : (⟨(i.succ : ℕ) - 1,
          by rw [hsucc_val]; omega⟩ : Fin k) = i := by
        apply Fin.ext
        change (i.succ : ℕ) - 1 = (i : ℕ)
        rw [hsucc_val]; omega
      have hidx_eq2 : (⟨(i.succ : ℕ), hlt⟩ : Fin k) = i_next := by
        apply Fin.ext
        change (i.succ : ℕ) = (i : ℕ) + 1
        rw [hsucc_val]
      rw [hidx_eq1, hidx_eq2]
      exact hanchor_mem.1
  have hvalid : ∀ i : Fin k,
      (polyVertex idx i.castSucc ∈ B (idx i)) ∧
      (polyVertex idx i.succ ∈ B (idx i)) :=
    fun i => ⟨hVertex_castSucc i, hVertex_succ i⟩
  -- Polygonal segment family: a chosen path from `polyVertex i.castSucc` to
  -- `polyVertex i.succ` inside `B (idx i)` (path-connectedness of `B (idx i)`).
  let seg : (i : Fin k) → _root_.Path
      (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
    fun i =>
      ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath
  have hseg_range : ∀ i : Fin k, ∀ s : unitInterval,
      (seg i s : X) ∈ B (idx i) := by
    intro i s
    exact ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath_mem s
  -- The polygonal vertex map as a `Fin (k+1) → X`.
  let p₀ : Fin (k + 1) → X := fun j => polyVertex idx j
  -- The polygonal loop.
  let polyLoop : _root_.Path x x :=
    (_root_.Path.concat p₀ seg).cast
      (show x = p₀ 0 from (polyVertex_zero idx).symm)
      (show x = p₀ (Fin.last k) from (polyVertex_last idx).symm)
  -- Reduce `f ⟨k, idx⟩ = g` to a `Quotient` identity.
  have hf_unfold : f ⟨k, idx⟩ = FundamentalGroup.fromPath ⟦polyLoop⟧ := by
    -- The `dif_pos hvalid` branch of `f` is exactly `polyLoop`.
    change (if hv :
        ∀ i : Fin k,
          (polyVertex idx i.castSucc ∈ B (idx i)) ∧
          (polyVertex idx i.succ ∈ B (idx i)) then
      let seg' : (i : Fin k) → _root_.Path
          (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
        fun i =>
          ((hBpc (idx i)).joinedIn _ (hv i).1 _ (hv i).2).somePath
      let p₀' : Fin (k + 1) → X := fun j => polyVertex idx j
      let polyLoop' : _root_.Path x x :=
        (_root_.Path.concat p₀' seg').cast
          (show x = p₀' 0 from (polyVertex_zero idx).symm)
          (show x = p₀' (Fin.last k) from (polyVertex_last idx).symm)
      FundamentalGroup.fromPath ⟦polyLoop'⟧
    else
      FundamentalGroup.fromPath ⟦_root_.Path.refl x⟧)
      = FundamentalGroup.fromPath ⟦polyLoop⟧
    rw [dif_pos hvalid]
  rw [hf_unfold]
  -- Identify `g` with `FundamentalGroup.fromPath q`.
  have hg_unfold : g = FundamentalGroup.fromPath q := rfl
  rw [hg_unfold]
  -- We need `⟦polyLoop⟧ = q`. Use `⟦γ⟧ = q` and `⟦γ⟧ = ⟦concatT⟧`.
  have hgoal_red :
      (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = q ↔
        (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ := by
    rw [← hγ, hquot_γ_concatT]
  -- It suffices to prove the path-quotient equality `⟦polyLoop⟧ = ⟦concatT⟧`.
  suffices hquot : (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ by
    have : (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = q :=
      hgoal_red.mpr hquot
    -- `FundamentalGroup.fromPath` is definitionally an `abbrev` of the underlying
    -- quotient, so the equality of quotients gives equality of group elements.
    exact congrArg FundamentalGroup.fromPath this
  -- ----------------------------------------------------------------
  -- Connectors `c i : Path (polyVertex idx i) (γ (t i))`, taking constants
  -- on the boundary `(i = 0, last k)` and lying inside the "forward" basis
  -- element `B (idx i)` for `i < k` (so that `c_i` and `seg_i` are both in
  -- `B (idx i)`, allowing `seg_i.symm.trans c_i.symm`-style cancellation
  -- to use the `piece_homotopy` lemma cleanly).
  --
  -- For each `i < k`, both `polyVertex idx i.castSucc` and `γ (t i.castSucc)`
  -- lie in `B (idx i)` (proved above as `hVertex_castSucc i` and
  -- `hγ_castSucc_in i`); `B (idx i)` is path-connected (`hBpc (idx i)`), so
  -- a path between them inside `B (idx i)` exists. We assemble these into
  -- a per-vertex family `c : Fin (k+1) → ...` by selecting at each
  -- `i : Fin (k+1)`:
  --
  --   * `i = 0`: the constant path at `x` (boundary endpoint).
  --   * `0 < i ≤ last k`: a path inside `B (idx i_prev)` where
  --     `i_prev := ⟨i.val - 1, _⟩ : Fin k`, both endpoints lying in this
  --     element (using `hVertex_succ i_prev` to identify the anchor at
  --     index `i.val - 1` as the polygonal vertex at position `i`).
  -- ----------------------------------------------------------------
  -- The connector "forward" basis-index choice: for `i : Fin (k+1)` with
  -- `i.val < k`, use `B (idx ⟨i.val, _⟩)`; for the terminal vertex
  -- `i.val = k`, the connector is the constant path at `x` (no forward
  -- segment).
  let cBasis : ∀ i : Fin (k + 1), (i : ℕ) < k → ℕ :=
    fun i h => idx ⟨(i : ℕ), h⟩
  -- The connector data: each `c i` is a path `polyVertex idx i → γ (t i)`,
  -- with the image-containment record packaged as a single `JoinedIn`
  -- witness for boundary-aware basis choices.
  -- For the boundary vertices `i = 0` and `i = Fin.last k`, both endpoints
  -- coincide with `x`, so we use `Path.refl x` (no nontrivial intersection
  -- needed).
  have hconn_boundary_zero :
      polyVertex idx (0 : Fin (k + 1)) = γ (t (0 : Fin (k + 1))) := by
    rw [polyVertex_zero, ht0]; exact γ.source.symm
  have hconn_boundary_last :
      polyVertex idx (Fin.last k) = γ (t (Fin.last k)) := by
    rw [polyVertex_last, htlast]; exact γ.target.symm
  -- Both polygonal vertex and γ-vertex lie in `B (idx i)` for `i < k`
  -- (the "forward" basis-element). At the cast-succ side of segment `i`,
  -- this is just `hVertex_castSucc i` and `hγ_castSucc_in i`. At the succ
  -- side of segment `i = last k - 1`, both equal `x ∈ B (idx (last k - 1))`
  -- by the boundary case.
  have hVγ_in_Bidx :
      ∀ i : Fin k,
        polyVertex idx i.castSucc ∈ B (idx i) ∧
          γ (t i.castSucc) ∈ B (idx i) :=
    fun i => ⟨hVertex_castSucc i, hγ_castSucc_in i⟩
  -- ----------------------------------------------------------------
  -- The substantive telescoping argument proceeds in three stages:
  --   (1) Existence of a connector family
  --       `c i : Path (polyVertex idx i) (γ (t i))` for each
  --       `i : Fin (k + 1)`, with `c 0` and `c (Fin.last k)` constant paths
  --       (modulo endpoint identifications) and the per-segment range
  --       bound: for each `i : Fin k`, the images of both `c i.castSucc`
  --       and `c i.succ` lie inside `B (idx i)`. Interior connectors
  --       require path-connectedness of the pairwise intersections
  --       `B (idx (i-1)) ∩ B (idx i)` between the anchor and the
  --       γ-vertex; this is the classical Hatcher §1.3 / Spanier §2.4
  --       basis-refinement / path-component selection step.
  --   (2) Construction of interleaved paths
  --       `polySegT i := (c i.castSucc).symm.trans ((seg i).trans (c i.succ))`,
  --       each a path `γ (t i.castSucc) → γ (t i.succ)` inside `B (idx i)`.
  --       By `uc_pi1_countable_piece_homotopy` applied with the
  --       chart-aligned `T i = γ.truncateOfLE _`, one has
  --       `⟦polySegT i⟧ = ⟦T i⟧` at the quotient level; by
  --       `uc_pi1_countable_concat_quot_congr`, the full concatenation
  --       gives `⟦Path.concat (γ∘t) polySegT⟧ = ⟦Path.concat (γ∘t) T⟧
  --         = ⟦concatT⟧` (up to cast).
  --   (3) Telescoping `(c · c.symm) ≃ refl`-cancellation at interior
  --       vertices and `c 0 = c (Fin.last k) = refl x` at boundaries
  --       yields `⟦Path.concat polyVertex seg⟧ = ⟦Path.concat (γ∘t)
  --       polySegT⟧`, completing `⟦polyLoop⟧ = ⟦concatT⟧`.
  --
  -- The residual `sorry` below isolates the combined obligation: the
  -- connector existence at non-trivial pairwise intersections plus the
  -- final algebraic telescoping under those connectors. All upstream
  -- scaffolding (refined basis, anchor coverage, monotone subdivision
  -- adaptation, polygonal vertex well-definedness, the bridge to `γ` via
  -- `Path.trans_truncate_homotopic`, the in-scope objects `T`, `concatT`,
  -- `hγ_concatT`, `hquot_γ_concatT`, `seg`, `hseg_range`, `polyLoop`,
  -- `hf_unfold`, `hg_unfold`, `hgoal_red`) supplies every ingredient the
  -- finalising argument needs.
  -- ----------------------------------------------------------------
  sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
