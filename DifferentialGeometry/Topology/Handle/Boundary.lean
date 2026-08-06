import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Constructions

namespace DifferentialGeometry.Topology.Handle

open Set

theorem range_cellSet (n : ℕ) :
    Set.range (fun x : ClosedCell n => (x : EuclideanSpace ℝ (Fin n))) = cellSet n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [cellSet]
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem range_sphereSet (n : ℕ) :
    Set.range (fun x : CellBoundary n => (x : EuclideanSpace ℝ (Fin n))) = sphereSet n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [sphereSet]
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem closure_cellSet (n : ℕ) : closure (cellSet n) = cellSet n := by
  rw [closure_eq_iff_isClosed]
  simpa [cellSet] using
    (isClosed_Iic : IsClosed (Set.Iic (1 : ℝ))).preimage
      (continuous_norm : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖))

private theorem frontier_cellSet (n : ℕ) : frontier (cellSet n) = sphereSet n := by
  by_cases hn : n = 0
  · subst n
    have hcell : cellSet 0 = (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext x
      have hx0 : ‖x‖ = (0 : ℝ) := by
        have hxeq : x = 0 := Subsingleton.elim x 0
        rw [hxeq, norm_zero]
      simp [cellSet, hx0]
    have hsphere : sphereSet 0 = (∅ : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext x
      constructor
      · intro hx
        have hx1 : ‖x‖ = (1 : ℝ) := by simpa [sphereSet] using hx
        have hx0 : ‖x‖ = (0 : ℝ) := by
          have hxeq : x = 0 := Subsingleton.elim x 0
          rw [hxeq, norm_zero]
        linarith
      · intro hx
        exact False.elim hx
    rw [hcell, hsphere]
    exact frontier_univ
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
      haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      infer_instance
    have hcell : cellSet n = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext x
      simp [cellSet, Metric.closedBall, dist_zero_right]
    have hsphere : sphereSet n = Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext x
      simp [sphereSet, Metric.sphere, dist_zero_right]
    rw [hcell, hsphere]
    exact frontier_closedBall' (0 : EuclideanSpace ℝ (Fin n)) 1

theorem frontier_handleSet (k l : ℕ) :
    frontier (handleSet k l) = attachingSet k l ∪ beltSet k l := by
  change frontier (cellSet k ×ˢ cellSet l) = attachingSet k l ∪ beltSet k l
  rw [frontier_prod_eq]
  rw [closure_cellSet, frontier_cellSet, frontier_cellSet, closure_cellSet]
  rw [Set.union_comm]
  simp [attachingSet, beltSet]

theorem range_toAmbient (k l : ℕ) :
    Set.range (toAmbient : StandardHandle k l →
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) = handleSet k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp [toAmbient, handleSet, cellSet]
  · intro hp
    rcases (show ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 from by simpa [handleSet, mem_prod] using hp)
      with ⟨h1, h2⟩
    refine ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), ?_⟩
    ext <;> rfl

theorem toAmbient_attachingRegion (k l : ℕ) :
    toAmbient '' attachingRegion k l = attachingSet k l := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [show attachingSet k l = sphereSet k ×ˢ cellSet l by rfl]
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simpa [sphereSet] using hq, q.2.2⟩
  · intro hp
    rcases (show ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 1 from by simpa [attachingSet, mem_prod] using hp)
      with ⟨hp1, hp2⟩
    refine ⟨(⟨p.1, le_of_eq hp1⟩, ⟨p.2, hp2⟩), ?_, ?_⟩
    · simpa [attachingRegion]
    · ext <;> rfl

theorem toAmbient_beltRegion (k l : ℕ) :
    toAmbient '' beltRegion k l = beltSet k l := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [show beltSet k l = cellSet k ×ˢ sphereSet l by rfl]
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨q.1.2, by simpa [sphereSet] using hq⟩
  · intro hp
    rcases (show ‖p.1‖ ≤ 1 ∧ ‖p.2‖ = 1 from by simpa [beltSet, mem_prod] using hp)
      with ⟨hp1, hp2⟩
    refine ⟨(⟨p.1, hp1⟩, ⟨p.2, le_of_eq hp2⟩), ?_, ?_⟩
    · simpa [beltRegion]
    · ext <;> rfl

theorem toAmbient_corner (k l : ℕ) :
    toAmbient '' corner k l = cornerSet k l := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [show cornerSet k l = sphereSet k ×ˢ sphereSet l by rfl]
    rw [show toAmbient q =
      ((q.1 : EuclideanSpace ℝ (Fin k)), (q.2 : EuclideanSpace ℝ (Fin l))) by rfl]
    exact mem_prod.mpr ⟨by simpa [sphereSet] using hq.1, by simpa [sphereSet] using hq.2⟩
  · intro hp
    rcases (show ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 from by simpa [cornerSet, mem_prod] using hp)
      with ⟨hp1, hp2⟩
    refine ⟨(⟨p.1, le_of_eq hp1⟩, ⟨p.2, le_of_eq hp2⟩), ?_, ?_⟩
    · simpa [corner]
    · ext <;> rfl

theorem attachingSet_inter_beltSet (k l : ℕ) :
    attachingSet k l ∩ beltSet k l = cornerSet k l := by
  ext p
  constructor
  · intro hp
    rcases (show ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 1 from by simpa [attachingSet, mem_prod] using hp.1)
      with ⟨hp1, _⟩
    rcases (show ‖p.1‖ ≤ 1 ∧ ‖p.2‖ = 1 from by simpa [beltSet, mem_prod] using hp.2)
      with ⟨_, hp2⟩
    simpa [cornerSet, sphereSet] using And.intro hp1 hp2
  · intro hp
    rcases (show ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 from by simpa [cornerSet, mem_prod] using hp)
      with ⟨hp1, hp2⟩
    constructor
    · simpa [attachingSet, sphereSet, cellSet, mem_prod] using And.intro hp1 (le_of_eq hp2)
    · simpa [beltSet, sphereSet, cellSet, mem_prod] using And.intro (le_of_eq hp1) hp2

theorem frontier_range_toAmbient (k l : ℕ) :
    frontier (Set.range (toAmbient : StandardHandle k l →
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) =
      toAmbient '' attachingRegion k l ∪ toAmbient '' beltRegion k l := by
  rw [range_toAmbient, toAmbient_attachingRegion, toAmbient_beltRegion, frontier_handleSet]

@[simp]
theorem mem_cellSet {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} : x ∈ cellSet n ↔ ‖x‖ ≤ 1 := by
  rfl

@[simp]
theorem mem_sphereSet {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} : x ∈ sphereSet n ↔ ‖x‖ = 1 := by
  rfl

@[simp]
theorem mem_handleSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ handleSet k l ↔ ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := by
  simp [handleSet, cellSet]

@[simp]
theorem mem_attachingSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ attachingSet k l ↔ ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 1 := by
  simp [attachingSet, sphereSet, cellSet]

@[simp]
theorem mem_beltSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ beltSet k l ↔ ‖p.1‖ ≤ 1 ∧ ‖p.2‖ = 1 := by
  simp [beltSet, sphereSet, cellSet]

@[simp]
theorem mem_cornerSet {k l : ℕ} {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)} :
    p ∈ cornerSet k l ↔ ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 := by
  simp [cornerSet, sphereSet]

end DifferentialGeometry.Topology.Handle
