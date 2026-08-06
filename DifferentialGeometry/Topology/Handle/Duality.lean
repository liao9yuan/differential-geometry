import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Topology.Constructions

namespace DifferentialGeometry.Topology.Handle

def swap (k l : ℕ) : StandardHandle k l ≃ₜ StandardHandle l k :=
  Homeomorph.prodComm (X := ClosedCell k) (Y := ClosedCell l)

@[simp]
theorem swap_apply {k l : ℕ} (p : StandardHandle k l) : swap k l p = (p.2, p.1) := by
  simp [swap, Prod.swap]

@[simp]
theorem swap_swap {k l : ℕ} (p : StandardHandle k l) : swap l k (swap k l p) = p := by
  simp [swap]

@[simp]
theorem swap_symm {k l : ℕ} : (swap k l).symm = swap l k := by
  simp [swap]

theorem swap_attachingRegion (k l : ℕ) : swap k l '' attachingRegion k l = beltRegion l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, attachingRegion, beltRegion] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, attachingRegion, beltRegion] using hp
    · simp [swap]

theorem swap_beltRegion (k l : ℕ) : swap k l '' beltRegion k l = attachingRegion l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, beltRegion, attachingRegion] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, beltRegion, attachingRegion] using hp
    · simp [swap]

theorem swap_corner (k l : ℕ) : swap k l '' corner k l = corner l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, corner] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, corner] using And.intro hp.2 hp.1
    · simp [swap]

theorem swap_coreDisk (k l : ℕ) : swap k l '' coreDisk k l = cocoreDisk l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, coreDisk, cocoreDisk] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, coreDisk, cocoreDisk] using hp
    · simp [swap]

theorem swap_cocoreDisk (k l : ℕ) : swap k l '' cocoreDisk k l = coreDisk l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, cocoreDisk, coreDisk] using hq
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, cocoreDisk, coreDisk] using hp
    · simp [swap]

theorem swap_attachingSphere (k l : ℕ) : swap k l '' attachingSphere k l = beltSphere l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, attachingSphere, beltSphere] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, attachingSphere, beltSphere] using And.intro hp.2 hp.1
    · simp [swap]

theorem swap_beltSphere (k l : ℕ) : swap k l '' beltSphere k l = attachingSphere l k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [swap, beltSphere, attachingSphere] using And.intro hq.2 hq.1
  · intro hp
    refine ⟨Prod.swap p, ?_, ?_⟩
    · simpa [swap, beltSphere, attachingSphere] using And.intro hp.2 hp.1
    · simp [swap]

theorem swap_attachingInclusion {k l : ℕ} (a : AttachingRegion k l) :
    swap k l (attachingInclusion k l a) = beltInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, attachingInclusion, beltInclusion]

theorem swap_beltInclusion {k l : ℕ} (a : BeltRegion k l) :
    swap k l (beltInclusion k l a) = attachingInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, beltInclusion, attachingInclusion]

theorem swap_cornerInclusion {k l : ℕ} (a : Corner k l) :
    swap k l (cornerInclusion k l a) = cornerInclusion l k (Prod.swap a) := by
  rcases a with ⟨a₁, a₂⟩
  simp [swap, cornerInclusion]

theorem swap_coreDiskInclusion {k l : ℕ} (x : ClosedCell k) :
    swap k l (coreDiskInclusion k l x) = cocoreDiskInclusion l k x := by
  simp [swap, coreDiskInclusion, cocoreDiskInclusion]

theorem swap_cocoreDiskInclusion {k l : ℕ} (y : ClosedCell l) :
    swap k l (cocoreDiskInclusion k l y) = coreDiskInclusion l k y := by
  simp [swap, cocoreDiskInclusion, coreDiskInclusion]

theorem swap_attachingSphereInclusion {k l : ℕ} (x : CellBoundary k) :
    swap k l (attachingSphereInclusion k l x) = beltSphereInclusion l k x := by
  simp [swap, attachingSphereInclusion, beltSphereInclusion]

theorem swap_beltSphereInclusion {k l : ℕ} (y : CellBoundary l) :
    swap k l (beltSphereInclusion k l y) = attachingSphereInclusion l k y := by
  simp [swap, beltSphereInclusion, attachingSphereInclusion]

end DifferentialGeometry.Topology.Handle
