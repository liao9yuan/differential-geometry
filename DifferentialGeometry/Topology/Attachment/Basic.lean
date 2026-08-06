import DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic

namespace DifferentialGeometry.Topology

universe u v w t

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

theorem continuous_cellBoundaryInclusion (n : ℕ) : Continuous (cellBoundaryInclusion n) := by
  exact continuous_subtype_val.subtype_mk (p := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ≤ 1)
    (fun x : CellBoundary n => le_of_eq x.2)

theorem injective_cellBoundaryInclusion (n : ℕ) : Function.Injective (cellBoundaryInclusion n) := by
  intro x y h
  have hval : (x : EuclideanSpace ℝ (Fin n)) = (y : EuclideanSpace ℝ (Fin n)) := by
    simpa using congrArg (fun z : ClosedCell n => (z : EuclideanSpace ℝ (Fin n))) h
  apply Subtype.ext
  exact hval

section AdjunctionSpace

variable {A : Type v} {B : Type w} [TopologicalSpace B] {X : Type u} [TopologicalSpace X]

theorem continuous_adjunctionMk (i : A → B) (φ : A → X) : Continuous (adjunctionMk i φ) :=
  continuous_quot_mk

theorem continuous_adjunctionLower (i : A → B) (φ : A → X) :
    Continuous (adjunctionLower (i := i) φ) :=
  continuous_quot_mk.comp continuous_inr

theorem continuous_adjunctionCell (i : A → B) (φ : A → X) : Continuous (adjunctionCell i φ) :=
  continuous_quot_mk.comp continuous_inl

theorem isQuotientMap_adjunctionMk (i : A → B) (φ : A → X) :
    Topology.IsQuotientMap (adjunctionMk i φ) :=
  isQuotientMap_quot_mk

theorem continuous_adjunction_lift (i : A → B) (φ : A → X) {Y : Type t} [TopologicalSpace Y]
    {f : B ⊕ X → Y}
    (hr : ∀ a b : B ⊕ X, adjunctionRel i φ a b → f a = f b) (hf : Continuous f) :
    Continuous (Quot.lift f hr : AdjunctionSpace i φ → Y) :=
  continuous_quot_lift hr hf

end AdjunctionSpace

end DifferentialGeometry.Topology
