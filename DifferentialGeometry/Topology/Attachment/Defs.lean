import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions

namespace DifferentialGeometry.Topology

universe u

abbrev ClosedCell (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

abbrev CellBoundary (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}

abbrev CellInterior (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1}

def cellBoundaryInclusion (n : ℕ) : CellBoundary n → ClosedCell n :=
  fun x => ⟨x, le_of_eq x.2⟩

def cellInteriorInclusion (n : ℕ) : CellInterior n → ClosedCell n :=
  fun x => ⟨x, le_of_lt x.2⟩

def adjunctionRel {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    ClosedCell n ⊕ X → ClosedCell n ⊕ X → Prop :=
  fun a b =>
    ∃ x : CellBoundary n,
      (a = Sum.inl (cellBoundaryInclusion n x) ∧ b = Sum.inr (φ x)) ∨
        (b = Sum.inl (cellBoundaryInclusion n x) ∧ a = Sum.inr (φ x))

abbrev AdjunctionSpace {X : Type u} (n : ℕ) (φ : CellBoundary n → X) : Type u :=
  Quot (adjunctionRel n φ)

def adjunctionMk {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    ClosedCell n ⊕ X → AdjunctionSpace n φ :=
  Quot.mk (adjunctionRel n φ)

def adjunctionLower {X : Type u} (n : ℕ) (φ : CellBoundary n → X) : X → AdjunctionSpace n φ :=
  fun x => adjunctionMk n φ (Sum.inr x)

def adjunctionCell {X : Type u} (n : ℕ) (φ : CellBoundary n → X) :
    ClosedCell n → AdjunctionSpace n φ :=
  fun d => adjunctionMk n φ (Sum.inl d)

theorem adjunction_boundary_coherence {X : Type u} (n : ℕ) (φ : CellBoundary n → X)
    (x : CellBoundary n) :
    adjunctionCell n φ (cellBoundaryInclusion n x) = adjunctionLower n φ (φ x) :=
  Quot.sound ⟨x, Or.inl ⟨rfl, rfl⟩⟩

end DifferentialGeometry.Topology
