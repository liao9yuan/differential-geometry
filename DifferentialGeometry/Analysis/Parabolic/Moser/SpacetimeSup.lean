import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M] [CompactSpace M]

def localizedSpacetimeSup
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) (a b : ℝ) : ℝ :=
  sSup ((fun z : ℝ × M ↦ u z.1 z.2) ''
    (Icc a b ×ˢ Function.support cutoff.toFun))

omit [Module.Finite ℝ E] [T2Space M] in
theorem bddAbove_localizedSpacetimeValues
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M ↦ u z.1 z.2)) (a b : ℝ) :
    BddAbove ((fun z : ℝ × M ↦ u z.1 z.2) ''
      (Icc a b ×ˢ Function.support cutoff.toFun)) := by
  apply (isCompact_Icc.prod isCompact_univ).image hu |>.bddAbove.mono
  exact image_mono (prod_mono_right (subset_univ _))

omit [Module.Finite ℝ E] [T2Space M] in
theorem le_localizedSpacetimeSup
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M ↦ u z.1 z.2))
    {a b t : ℝ} (ht : t ∈ Icc a b) {x : M} (hx : cutoff.toFun x ≠ 0) :
    u t x ≤ localizedSpacetimeSup (I := I) cutoff u a b := by
  apply le_csSup (bddAbove_localizedSpacetimeValues cutoff u hu a b)
  exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩

omit [Module.Finite ℝ E] [T2Space M] [CompactSpace M] in
theorem localizedSpacetimeSup_le
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ) {a b C : ℝ}
    (hab : a ≤ b) (hcutoff : ∃ x, cutoff.toFun x ≠ 0)
    (hbound : ∀ t ∈ Icc a b, ∀ x, cutoff.toFun x ≠ 0 → u t x ≤ C) :
    localizedSpacetimeSup (I := I) cutoff u a b ≤ C := by
  unfold localizedSpacetimeSup
  apply csSup_le
  · obtain ⟨x, hx⟩ := hcutoff
    exact ⟨u a x, ⟨(a, x), ⟨⟨le_rfl, hab⟩, hx⟩, rfl⟩⟩
  · intro y hy
    obtain ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩ := hy
    exact hbound t ht x hx

omit [Module.Finite ℝ E] [T2Space M] in
theorem localizedSpacetimeSup_pos
    {g : SmoothRiemannianMetric I M} (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : Continuous (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) {a b : ℝ} (hab : a ≤ b)
    (hcutoff : ∃ x, cutoff.toFun x ≠ 0) :
    0 < localizedSpacetimeSup (I := I) cutoff u a b := by
  obtain ⟨x, hx⟩ := hcutoff
  exact (hpos a x).trans_le
    (le_localizedSpacetimeSup cutoff u hu ⟨le_rfl, hab⟩ hx)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
