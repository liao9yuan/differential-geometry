import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
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
    (X : Type*) [TopologicalSpace X]
    (B : ℕ → Set X) :
    ∃ anchor : ℕ × ℕ → X,
      ∀ p : ℕ × ℕ, (B p.1 ∩ B p.2).Nonempty → anchor p ∈ B p.1 ∩ B p.2 := sorry

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
            γ s ∈ B (idx i)) := sorry

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
