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
in the whole space. -/
theorem uc_pi1_countable_basis_refinement
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X]
    [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X] :
    ∃ B : ℕ → Set X,
      (∀ n, IsOpen (B n)) ∧
      (∀ n, IsPathConnected (B n)) ∧
      (∀ n, ∀ (x : X) (_ : x ∈ B n) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ B n →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧) ∧
      TopologicalSpace.IsTopologicalBasis (Set.range B) := sorry

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
  exact sorry

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
