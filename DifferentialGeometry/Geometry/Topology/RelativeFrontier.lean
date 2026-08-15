import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

open Topology
open scoped Set.Notation

namespace Set

variable {X : Type*} [TopologicalSpace X]

def interiorIn (A C : Set X) : Set X :=
  ((↑) : A → X) '' (interior (A ↓∩ C) : Set A)

def frontierIn (A C : Set X) : Set X :=
  ((↑) : A → X) '' (frontier (A ↓∩ C) : Set A)

def closureIn (A C : Set X) : Set X :=
  ((↑) : A → X) '' (closure (A ↓∩ C) : Set A)

theorem interiorIn_carrier {A C : Set X} : interiorIn A C ⊆ A := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem frontierIn_carrier {A C : Set X} : frontierIn A C ⊆ A := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem closureIn_carrier {A C : Set X} : closureIn A C ⊆ A := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem interiorIn_subset {A C : Set X} : interiorIn A C ⊆ C := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ A ↓∩ C := interior_subset hx
  exact hx'

theorem frontierIn_subset {A C : Set X} (hC : IsClosed (A ↓∩ C)) :
    frontierIn A C ⊆ C := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ closure (A ↓∩ C) := frontier_subset_closure hx
  rw [hC.closure_eq] at hx'
  exact hx'

theorem closureIn_subset {A C : Set X} (hC : IsClosed (A ↓∩ C)) :
    closureIn A C ⊆ C := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hC.closure_eq] at hx
  exact hx

theorem dense_iff_closureIn {A C : Set X} :
    Dense (A ↓∩ C) ↔ closureIn A C = A := by
  constructor
  · intro h
    rw [closureIn, h.closure_eq, image_univ, Subtype.range_val]
  · intro h
    rw [dense_iff_closure_eq]
    apply eq_univ_of_forall
    intro x
    have hx : (x : X) ∈ closureIn A C := h.ge x.property
    obtain ⟨y, hy, hxy⟩ := hx
    have heq : y = x := Subtype.ext hxy
    simpa only [heq] using hy

theorem frontierIn_eq_sdiff {A C : Set X}
    (hopen : IsOpen (A ↓∩ C)) (hclosure : closureIn A C = A) :
    frontierIn A C = A \ C := by
  have hdense : Dense (A ↓∩ C) := dense_iff_closureIn.mpr hclosure
  rw [frontierIn, hopen.frontier_eq, hdense.closure_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : X) ∉ C := by
      simpa only [mem_diff, mem_univ, true_and, mem_preimage] using hy
    exact ⟨y.property, hy'⟩
  · rintro ⟨hxA, hxC⟩
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    simpa only [mem_diff, mem_univ, true_and, mem_preimage] using hxC

theorem frontierIn_isCompact {A C : Set X} (hA : IsCompact A) :
    IsCompact (frontierIn A C) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  exact isClosed_frontier.isCompact.image continuous_subtype_val

@[simp] theorem interiorIn_self (A : Set X) : interiorIn A A = A := by
  have hself : A ↓∩ A = (Set.univ : Set A) := by
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  simp only [interiorIn, hself, interior_univ, image_univ, Subtype.range_val]

@[simp] theorem frontierIn_self (A : Set X) : frontierIn A A = ∅ := by
  have hself : A ↓∩ A = (Set.univ : Set A) := by
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  simp only [frontierIn, hself, frontier_univ, image_empty]

@[simp] theorem closureIn_self (A : Set X) : closureIn A A = A := by
  have hself : A ↓∩ A = (Set.univ : Set A) := by
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  simp only [closureIn, hself, closure_univ, image_univ, Subtype.range_val]

end Set
