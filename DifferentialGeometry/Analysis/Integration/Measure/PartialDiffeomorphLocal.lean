import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation

set_option autoImplicit false

/-!
# Finite localization under a partial diffeomorphism

This file gives the measure-theoretic finite localization used after pulling a
measure back through the inverse of a partial diffeomorphism.  The local pieces
need not be disjoint; a pointwise finite decomposition is enough.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Integral.Measure

universe u uA uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

omit [FiniteDimensional Real E] in
/-- Pulling a measure back through a partial diffeomorphism sends the
complement of a captured source set into the complement of the captured target
set. -/
theorem map_inv_tail_le
    {M N : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace H N]
    [MeasurableSpace N] [OpensMeasurableSpace N]
    {n : WithTop ℕ∞} (e : PartialDiffeomorph I I M N n) (mu : Measure N)
    {K : Set M} (hK : MeasurableSet K) (hKsrc : K ⊆ e.source)
    {B : Set N} (hcap : B ⊆ e '' K) :
    Measure.map e.symm (mu.restrict e.target) Kᶜ ≤ mu Bᶜ := by
  have htarget : MeasurableSet e.target := e.open_target.measurableSet
  have hinv : AEMeasurable e.symm (mu.restrict e.target) :=
    e.contMDiffOn_invFun.continuousOn.aemeasurable htarget
  rw [Measure.map_apply_of_aemeasurable hinv hK.compl,
    Measure.restrict_apply' htarget]
  apply measure_mono
  rintro y ⟨hyK, _hyt⟩ hyB
  obtain ⟨x, hxK, hxy⟩ := hcap hyB
  apply hyK
  have hback : e.symm y = x := by
    rw [← hxy]
    exact e.left_inv (hKsrc hxK)
  rw [hback]
  exact hxK

omit [FiniteDimensional Real E] in
/-- A finite nonnegative decomposition localizes after pulling a measure back
through the inverse of a partial diffeomorphism.  Each summand is integrated
only over the image of a set containing its support. -/
theorem lint_map_fin_loc
    {A : Type uA}
    {M N : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
    [MeasurableSpace N] [OpensMeasurableSpace N]
    (e : PartialDiffeomorph I I M N 1) (mu : Measure N)
    (s : Finset A) (F : M → ENNReal) (G : A → M → ENNReal)
    (K : A → Set M)
    (hF : Measurable F) (hG : ∀ a ∈ s, Measurable (G a))
    (hsum : ∀ x, F x = ∑ a ∈ s, G a x)
    (hKsrc : ∀ a ∈ s, K a ⊆ e.source)
    (hSupp : ∀ a ∈ s, Function.support (G a) ⊆ K a)
    (hKimg : ∀ a ∈ s, MeasurableSet (e '' K a)) :
    ∫⁻ x, F x ∂Measure.map e.symm (mu.restrict e.target) =
      ∑ a ∈ s, ∫⁻ y in e '' K a, G a (e.symm y) ∂mu := by
  classical
  have htarget : MeasurableSet e.target := e.open_target.measurableSet
  have hinv : AEMeasurable e.symm (mu.restrict e.target) :=
    e.contMDiffOn_invFun.continuousOn.aemeasurable htarget
  rw [MeasureTheory.lintegral_map' hF.aemeasurable hinv]
  calc
    ∫⁻ y in e.target, F (e.symm y) ∂mu =
        ∫⁻ y in e.target, ∑ a ∈ s, G a (e.symm y) ∂mu := by
      apply MeasureTheory.lintegral_congr
      intro y
      exact hsum (e.symm y)
    _ = ∑ a ∈ s, ∫⁻ y in e.target, G a (e.symm y) ∂mu := by
      rw [MeasureTheory.lintegral_finset_sum']
      intro a ha
      exact (hG a ha).aemeasurable.comp_aemeasurable hinv
    _ = ∑ a ∈ s, ∫⁻ y in e '' K a, G a (e.symm y) ∂mu := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← MeasureTheory.lintegral_indicator htarget,
        ← MeasureTheory.lintegral_indicator (hKimg a ha)]
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hyK : y ∈ e '' K a
      · have hyt : y ∈ e.target := by
          rcases hyK with ⟨x, hxK, rfl⟩
          exact e.map_source (hKsrc a ha hxK)
        simp only [Set.indicator_of_mem hyK, Set.indicator_of_mem hyt]
      · rw [Set.indicator_of_notMem hyK]
        by_cases hyt : y ∈ e.target
        · rw [Set.indicator_of_mem hyt]
          have hzero : G a (e.symm y) = 0 := by
            by_contra hne
            have hxK : e.symm y ∈ K a := hSupp a ha hne
            exact hyK ⟨e.symm y, hxK, e.right_inv hyt⟩
          exact hzero
        · rw [Set.indicator_of_notMem hyt]

end DifferentialGeometry.Integral.Measure
