import DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic

namespace DifferentialGeometry.Topology

universe u v

open Filter Function Set

instance (n : ℕ) : CompactSpace (ClosedCell n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    convert (isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)) using 1
    ext x
    simp [Metric.closedBall, dist_zero_right]
  exact isCompact_iff_compactSpace.mp h

instance (n : ℕ) : CompactSpace (CellBoundary n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    convert (isCompact_sphere (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)) using 1
    ext x
    simp [Metric.sphere, dist_zero_right]
  exact isCompact_iff_compactSpace.mp h

section AdjunctionSpace

variable {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)

theorem continuous_adjunctionMk : Continuous (adjunctionMk n φ) :=
  continuous_quot_mk

theorem continuous_adjunctionLower : Continuous (adjunctionLower n φ) :=
  continuous_quot_mk.comp continuous_inr

theorem continuous_adjunctionCell : Continuous (adjunctionCell n φ) :=
  continuous_quot_mk.comp continuous_inl

theorem isQuotientMap_adjunctionMk : Topology.IsQuotientMap (adjunctionMk n φ) :=
  isQuotientMap_quot_mk

theorem continuous_adjunction_lift {Y : Type v} [TopologicalSpace Y] {f : ClosedCell n ⊕ X → Y}
    (hr : ∀ a b : ClosedCell n ⊕ X, adjunctionRel n φ a b → f a = f b) (hf : Continuous f) :
    Continuous (Quot.lift f hr : AdjunctionSpace n φ → Y) :=
  continuous_quot_lift hr hf

end AdjunctionSpace

end DifferentialGeometry.Topology
