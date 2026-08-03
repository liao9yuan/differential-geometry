import DifferentialGeometry.Analysis.Schauder.Composition
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

open Set Metric
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem exists_norm_bound_of_continuousOn_isCompact
    {s : Set V} (hs : IsCompact s) {f : V → F}
    (hf : ContinuousOn f s) :
    ∃ C : NNReal, ∀ x ∈ s, ‖f x‖ ≤ C := by
  rcases hs.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

theorem exists_holderWith_restrict_of_contDiffOn_isCompact
    {s : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    {f : V → F} (hf : ContDiffOn Real 1 f s)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C : NNReal, HolderWith C alpha (s.restrict f) := by
  rcases hf.exists_lipschitzOnWith one_ne_zero hsconv hs with ⟨L, hL⟩
  let D : NNReal := (ediam s).toNNReal
  refine ⟨L * D ^ ((1 : Real) - (alpha : Real)), ?_⟩
  apply HolderOnWith.holderWith
  apply hL.holderOnWith.of_le (D := D) _ halpha
  intro x hx y hy
  rw [ENNReal.coe_toNNReal hs.isBounded.ediam_ne_top]
  exact edist_le_ediam_of_mem hx hy

theorem exists_norm_bound_and_holderWith_restrict_of_contDiffOn_isCompact
    {s : Set V} (hs : IsCompact s) (hsconv : Convex Real s)
    {f : V → F} (hf : ContDiffOn Real 1 f s)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ x ∈ s, ‖f x‖ ≤ C₀) ∧ HolderWith Cα alpha (s.restrict f) := by
  rcases exists_norm_bound_of_continuousOn_isCompact hs hf.continuousOn with ⟨C₀, hC₀⟩
  rcases exists_holderWith_restrict_of_contDiffOn_isCompact hs hsconv hf halpha with ⟨Cα, hCα⟩
  exact ⟨C₀, Cα, hC₀, hCα⟩

theorem isCompact_parabolicCylinder_Icc
    {X : Type*} [TopologicalSpace X]
    (a b : Real) {K : Set X} (hK : IsCompact K) :
    IsCompact (parabolicCylinder (Set.Icc a b) K) := by
  rw [show parabolicCylinder (Set.Icc a b) K =
      (Metric.Snowflaking.toSnowflaking '' Set.Icc a b) ×ˢ K by
    ext p
    rw [Metric.Snowflaking.image_toSnowflaking_eq_preimage]
    rfl]
  exact (isCompact_Icc.image Metric.Snowflaking.continuous_toSnowflaking).prod hK

theorem exists_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
    (a b : Real) {K : Set V} (hK : IsCompact K) (hKconv : Convex Real K)
    {f : Real × V → F} (hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C : NNReal, HolderWith C alpha
      ((parabolicCylinder (Set.Icc a b) K).restrict
        (f ∘ parabolicToProduct)) := by
  rcases hf.exists_lipschitzOnWith one_ne_zero
      (convex_Icc a b |>.prod hKconv) (isCompact_Icc.prod hK) with ⟨L, hL⟩
  let Q := parabolicCylinder (Set.Icc a b) K
  have hmaps : MapsTo parabolicToProduct Q (Set.Icc a b ×ˢ K) := by
    intro p hp
    exact hp
  have hcomp : LipschitzOnWith
      (L * parabolicTimeSlabLipschitzConst a b)
      (f ∘ parabolicToProduct) Q :=
    hL.comp (lipschitzOnWith_parabolicToProduct_Icc a b K) hmaps
  have hQ : IsCompact Q := isCompact_parabolicCylinder_Icc a b hK
  let D : NNReal := (ediam Q).toNNReal
  refine ⟨(L * parabolicTimeSlabLipschitzConst a b) *
      D ^ ((1 : Real) - (alpha : Real)), ?_⟩
  apply HolderOnWith.holderWith
  apply hcomp.holderOnWith.of_le (D := D) _ halpha
  intro p hp q hq
  rw [ENNReal.coe_toNNReal hQ.isBounded.ediam_ne_top]
  exact edist_le_ediam_of_mem hp hq

theorem exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
    (a b : Real) {K : Set V} (hK : IsCompact K) (hKconv : Convex Real K)
    {f : Real × V → F} (hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖f (parabolicToProduct p)‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (f ∘ parabolicToProduct)) := by
  rcases exists_norm_bound_of_continuousOn_isCompact
      (isCompact_Icc.prod hK) hf.continuousOn with ⟨C₀, hC₀⟩
  rcases exists_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha with ⟨Cα, hCα⟩
  refine ⟨C₀, Cα, ?_, hCα⟩
  intro p hp
  exact hC₀ (parabolicToProduct p) hp

end DifferentialGeometry.Analysis.Schauder

end
