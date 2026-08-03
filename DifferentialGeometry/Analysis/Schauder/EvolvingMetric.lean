import DifferentialGeometry.Analysis.Schauder.CompactRegularity
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

theorem exists_chartInvGramOnE_parabolic_schauder_bounds
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (a b : Real) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    (i j : Fin (Module.finrank Real E))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖chartInvGramOnE (I := I) (G.metric p.time) chartCenter i j p.space‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartInvGramOnE (I := I)
            (G.metric p.time) chartCenter i j p.space)) := by
  let f : Real × E → Real := fun p =>
    chartInvGramOnE (I := I) (G.metric p.1) chartCenter i j p.2
  have hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K) :=
    ((chartInvGramOnE_contDiffOn (I := I) hG habreg chartCenter i j).mono
      (Set.prod_mono Subset.rfl hKchart)).of_le (by simp)
  simpa only [f, Function.comp_apply, parabolicToProduct] using
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha

theorem exists_chartInvGramOnE_parabolic_schauder_coefficient_bounds
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (a b : Real) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ A Ka : Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → NNReal,
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b) K →
        ‖chartInvGramOnE (I := I) (G.metric p.time)
          chartCenter i j p.space‖ ≤ A i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartInvGramOnE (I := I)
            (G.metric p.time) chartCenter i j p.space))) ∧
      ∀ p, p ∈ parabolicCylinder (Set.Icc a b) K →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          chartInvGramOnE (I := I) (G.metric p.time)
            chartCenter i j p.space).PosDef := by
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ∃ C₀ Cα : NNReal,
        (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
          ‖chartInvGramOnE (I := I) (G.metric p.time)
            chartCenter i j p.space‖ ≤ C₀) ∧
        HolderWith Cα alpha
          ((parabolicCylinder (Set.Icc a b) K).restrict
            (fun p => chartInvGramOnE (I := I)
              (G.metric p.time) chartCenter i j p.space)) := by
    intro i j
    exact exists_chartInvGramOnE_parabolic_schauder_bounds
      hG a b habreg chartCenter hK hKconv hKchart i j halpha
  choose A Ka hbounds using hentry
  refine ⟨A, Ka, ?_, ?_, ?_⟩
  · intro i j p hp
    exact (hbounds i j).1 p hp
  · intro i j
    exact (hbounds i j).2
  · intro p hp
    exact chartInvGramOnE_posDef (I := I) (G.metric p.time) chartCenter
      (interior_subset (hKchart hp.2))

theorem exists_chartChristoffelOnE_parabolic_schauder_bounds
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) {K : Set E} (hK : IsCompact K)
    (hKconv : Convex Real K)
    (hKchart : K ⊆ interior (extChartAt I chartCenter).target)
    (i j k : Fin (Module.finrank Real E))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ C₀ Cα : NNReal,
      (∀ p ∈ parabolicCylinder (Set.Icc a b) K,
        ‖chartChristoffel (I := I) (G.metric p.time)
          chartCenter i j k p.space‖ ≤ C₀) ∧
      HolderWith Cα alpha
        ((parabolicCylinder (Set.Icc a b) K).restrict
          (fun p => chartChristoffel (I := I) (G.metric p.time)
            chartCenter i j k p.space)) := by
  let f : Real × E → Real := fun p =>
    chartChristoffel (I := I) (G.metric p.1) chartCenter i j k p.2
  have hf : ContDiffOn Real 1 f (Set.Icc a b ×ˢ K) :=
    ((chartChristoffelOnE_contDiffOn (I := I) hG habreg
      (uniqueDiffOn_Icc hab) chartCenter i j k).mono
      (Set.prod_mono Subset.rfl hKchart)).of_le (by simp)
  simpa only [f, Function.comp_apply, parabolicToProduct] using
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hf halpha

end DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn

end
