import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth seams for Ricci-flow surgery

This file records the lowest geometric datum at one surgery time.  The
pre-surgery and post-surgery slices may be different manifold types.  A smooth
identification is supplied on open neighborhoods, while the retained region is
allowed to have boundary and is therefore stored as a subset of the old open
neighborhood.

Metrics, curvature, Ricci-flow equations, neck quality, and a global surgery
spacetime are deliberately separate later layers.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

/-- The smooth identification datum across one surgery event.

The retained set lives inside an open pre-surgery neighborhood, but need not
itself be open.  This distinction is essential for a retained codimension-zero
region with boundary. -/
structure SurgerySeam
    {Eold : Type*} [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
    {Hold : Type*} [TopologicalSpace Hold]
    (Iold : ModelWithCorners ℝ Eold Hold)
    (Mold : Type*) [TopologicalSpace Mold] [ChartedSpace Hold Mold]
    {Enew : Type*} [NormedAddCommGroup Enew] [NormedSpace ℝ Enew]
    {Hnew : Type*} [TopologicalSpace Hnew]
    (Inew : ModelWithCorners ℝ Enew Hnew)
    (Mnew : Type*) [TopologicalSpace Mnew] [ChartedSpace Hnew Mnew] where
  /-- Open neighborhood on the pre-surgery slice. -/
  oldOpen : Opens Mold
  /-- Open neighborhood on the post-surgery slice. -/
  newOpen : Opens Mnew
  /-- Smooth identification of the two event neighborhoods. -/
  identify : Diffeomorph Iold Inew oldOpen newOpen (∞ : WithTop ℕ∞)
  /-- Points retained through the event, expressed in the old open subtype. -/
  keep : Set oldOpen

namespace SurgerySeam

variable {Eold : Type*} [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
variable {Hold : Type*} [TopologicalSpace Hold]
variable {Iold : ModelWithCorners ℝ Eold Hold}
variable {Mold : Type*} [TopologicalSpace Mold] [ChartedSpace Hold Mold]
variable {Enew : Type*} [NormedAddCommGroup Enew] [NormedSpace ℝ Enew]
variable {Hnew : Type*} [TopologicalSpace Hnew]
variable {Inew : ModelWithCorners ℝ Enew Hnew}
variable {Mnew : Type*} [TopologicalSpace Mnew] [ChartedSpace Hnew Mnew]

variable (S : SurgerySeam Iold Mold Inew Mnew)

/-- The retained pre-surgery region as a subset of the ambient old slice. -/
def preKeep : Set Mold :=
  Subtype.val '' S.keep

/-- The ambient post-surgery point corresponding to a point of the old event
neighborhood. -/
def toPost (x : S.oldOpen) : Mnew :=
  S.identify x

/-- The ambient event-identification map is injective. -/
theorem toPost_injective : Function.Injective S.toPost := by
  intro x y hxy
  exact S.identify.injective (Subtype.ext hxy)

/-- The retained post-surgery region as a subset of the ambient new slice. -/
def postKeep : Set Mnew :=
  S.toPost '' S.keep

/-- Points of the old slice removed by this event. -/
def discarded : Set Mold :=
  S.preKeepᶜ

/-- Points of the new slice not inherited from the retained old region. -/
def created : Set Mnew :=
  S.postKeepᶜ

/-- The smooth seam identifies the retained old region bijectively with the
retained post-surgery region. -/
def keepEquiv : S.keep ≃ S.postKeep :=
  Equiv.Set.image S.toPost S.keep S.toPost_injective

/-- The retained old region lies in the ambient old event neighborhood. -/
theorem preKeep_subset : S.preKeep ⊆ S.oldOpen := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

/-- The retained new region lies in the ambient new event neighborhood. -/
theorem postKeep_subset : S.postKeep ⊆ S.newOpen := by
  rintro y ⟨x, _hx, rfl⟩
  exact (S.identify x).2

end SurgerySeam
end DifferentialGeometry.PDE.RicciFlow.Surgery
