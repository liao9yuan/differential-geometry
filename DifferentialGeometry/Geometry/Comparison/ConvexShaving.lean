import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Topology.RelativeFrontier
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal Set.Notation

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

section Metric

variable {X : Type*} [PseudoMetricSpace X]

def innerParallel (C B : Set X) (r : ℝ) : Set X :=
  C ∩ {x | r ≤ Metric.infDist x B}

namespace innerParallel

variable {C B : Set X} {r s : ℝ}

@[simp] theorem mem {x : X} :
    x ∈ innerParallel C B r ↔ x ∈ C ∧ r ≤ Metric.infDist x B :=
  Iff.rfl

theorem mono (hrs : r ≤ s) : innerParallel C B s ⊆ innerParallel C B r := by
  rintro x ⟨hxC, hxs⟩
  exact ⟨hxC, hrs.trans hxs⟩

theorem nonempty_of_mem {x : X} (hxC : x ∈ C)
    (hxr : r ≤ Metric.infDist x B) : (innerParallel C B r).Nonempty :=
  ⟨x, hxC, hxr⟩

theorem isClosed (hC : IsClosed C) : IsClosed (innerParallel C B r) :=
  hC.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt B))

theorem isCompact (hC : IsCompact C) : IsCompact (innerParallel C B r) :=
  hC.inter_right (isClosed_le continuous_const (Metric.continuous_infDist_pt B))

end innerParallel

def deepestSet (C B : Set X) : Set X :=
  {x | x ∈ C ∧ IsMaxOn (fun y => Metric.infDist y B) C x}

namespace deepestSet

variable {C B : Set X}

@[simp] theorem mem {x : X} :
    x ∈ deepestSet C B ↔
      x ∈ C ∧ IsMaxOn (fun y => Metric.infDist y B) C x :=
  Iff.rfl

theorem nonempty (hC : IsCompact C) (hne : C.Nonempty) :
    (deepestSet C B).Nonempty := by
  obtain ⟨x, hxC, hx⟩ :=
    hC.exists_isMaxOn hne (Metric.continuous_infDist_pt B).continuousOn
  exact ⟨x, hxC, hx⟩

theorem subset : deepestSet C B ⊆ C := fun _ hx => hx.1

theorem eq_innerParallel {x : X} (hx : x ∈ deepestSet C B) :
    deepestSet C B = innerParallel C B (Metric.infDist x B) := by
  ext y
  constructor
  · intro hy
    have hxy := hy.2 hx.1
    change Metric.infDist x B ≤ Metric.infDist y B at hxy
    exact ⟨hy.1, hxy⟩
  · intro hy
    refine ⟨hy.1, ?_⟩
    intro z hzC
    have hzx := hx.2 hzC
    change Metric.infDist z B ≤ Metric.infDist x B at hzx
    exact hzx.trans hy.2

theorem isCompact (hC : IsCompact C) : IsCompact (deepestSet C B) := by
  by_cases hne : C.Nonempty
  · obtain ⟨x, hx⟩ := nonempty (B := B) hC hne
    rw [eq_innerParallel hx]
    exact innerParallel.isCompact hC
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp only [deepestSet, mem_empty_iff_false, false_and, setOf_false]
    exact isCompact_empty

theorem disjoint (hpos : ∃ x ∈ C, 0 < Metric.infDist x B) :
    Disjoint (deepestSet C B) B := by
  rw [Set.disjoint_left]
  rintro x hx hxB
  obtain ⟨y, hyC, hy⟩ := hpos
  have hle := hx.2 hyC
  change Metric.infDist y B ≤ Metric.infDist x B at hle
  rw [Metric.infDist_zero_of_mem hxB] at hle
  exact (not_le_of_gt hy) hle

end deepestSet

theorem exists_frontier_dist [T2Space X] {A N : Set X}
    (hA : IsCompact A) (hopen : IsOpen (A ↓∩ N))
    (hN : (A ∩ N).Nonempty)
    (hfrontier : (Set.frontierIn A N).Nonempty) :
    ∃ x ∈ A, 0 < Metric.infDist x (Set.frontierIn A N) := by
  obtain ⟨x, hxA, hxN⟩ := hN
  refine ⟨x, hxA, ?_⟩
  have hclosed : IsClosed (Set.frontierIn A N) :=
    (Set.frontierIn_isCompact hA).isClosed
  apply (hclosed.notMem_iff_infDist_pos hfrontier).mp
  rintro ⟨y, hyfrontier, hyx⟩
  have hyN : y ∈ A ↓∩ N := by
    simpa only [Set.mem_preimage, hyx] using hxN
  exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hopen)
    hyfrontier hyN

theorem frontier_shave_data [T2Space X] {C N : Set X}
    (hC : IsCompact C) (hNne : N.Nonempty) (hNC : N ⊆ C)
    (hopen : IsOpen (C ↓∩ N)) (hdense : Set.closureIn C N = C)
    (hBne : (C \ N).Nonempty) :
    Set.frontierIn C N = C \ N ∧
      IsCompact (C \ N) ∧
      (∃ x ∈ C, 0 < Metric.infDist x (C \ N)) ∧
      (deepestSet C (C \ N)).Nonempty ∧
      IsCompact (deepestSet C (C \ N)) ∧
      deepestSet C (C \ N) ⊆ N ∧
      Disjoint (deepestSet C (C \ N)) (C \ N) := by
  have hfront : Set.frontierIn C N = C \ N :=
    Set.frontierIn_eq_sdiff hopen hdense
  have hBcompact : IsCompact (C \ N) := by
    rw [← hfront]
    exact Set.frontierIn_isCompact hC
  have hCN : (C ∩ N).Nonempty := by
    obtain ⟨x, hxN⟩ := hNne
    exact ⟨x, hNC hxN, hxN⟩
  have hfrontne : (Set.frontierIn C N).Nonempty := by
    simpa only [hfront] using hBne
  have hpos : ∃ x ∈ C, 0 < Metric.infDist x (C \ N) := by
    have h := exists_frontier_dist hC hopen hCN hfrontne
    simpa only [hfront] using h
  have hCne : C.Nonempty := hNne.mono hNC
  have hDne : (deepestSet C (C \ N)).Nonempty :=
    deepestSet.nonempty hC hCne
  have hDcompact : IsCompact (deepestSet C (C \ N)) :=
    deepestSet.isCompact hC
  have hDdisjoint : Disjoint (deepestSet C (C \ N)) (C \ N) :=
    deepestSet.disjoint hpos
  have hDsub : deepestSet C (C \ N) ⊆ N := by
    intro x hxD
    have hxC : x ∈ C := deepestSet.subset hxD
    by_contra hxN
    exact Set.disjoint_left.mp hDdisjoint hxD ⟨hxC, hxN⟩
  exact ⟨hfront, hBcompact, hpos, hDne, hDcompact, hDsub, hDdisjoint⟩

end Metric

section Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PseudoMetricSpace M]

namespace innerParallel

variable {g : SmoothRiemannianMetric I M} {C B : Set M} {r : ℝ}

theorem totallyConvex (hC : IsTotallyConvex (I := I) g C)
    (hd : IsGeodesicConcaveOn (I := I) g C
      (fun x => Metric.infDist x B)) :
    IsTotallyConvex (I := I) g (innerParallel C B r) := by
  simpa only [innerParallel] using hd.superlevel hC r

end innerParallel

namespace deepestSet

variable {g : SmoothRiemannianMetric I M} {C B : Set M}

theorem totallyConvex (hC : IsTotallyConvex (I := I) g C)
    (hd : IsGeodesicConcaveOn (I := I) g C
      (fun x => Metric.infDist x B)) :
    IsTotallyConvex (I := I) g (deepestSet C B) := by
  intro γ a b hab hγ hcont ha hb
  have hmaps := hC hab hγ hcont ha.1 hb.1
  intro t ht
  refine ⟨hmaps ht, ?_⟩
  intro y hyC
  have ht' : t ∈ segment ℝ a b := by
    rw [segment_eq_Icc hab]
    exact ht
  have hbound := (hd hab hγ hcont hmaps).ge_on_segment
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) ht'
  exact (le_min (ha.2 hyC) (hb.2 hyC)).trans hbound

end deepestSet

end Geodesic

end Riemannian
end Geometry
end DifferentialGeometry
