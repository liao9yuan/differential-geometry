import DifferentialGeometry.Analysis.Schauder.EvolvingMetric
import DifferentialGeometry.Analysis.Schauder.ParabolicBallExtension

noncomputable section

open Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Schauder

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclN (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

omit [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
theorem exists_parabolicChartPotentialCoefficient_schauder_bounds
    (V : Real → M → Real) (a b : Real) (chartCenter : M)
    {K : Set E} (hK : IsCompact K) (hKconv : Convex Real K)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ K))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Bc Kc : NNReal,
      (∀ p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K) →
        ‖parabolicChartPotentialCoefficient (I := I) V chartCenter p‖ ≤ Bc) ∧
      HolderWith Kc alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) K)).restrict
            (parabolicChartPotentialCoefficient (I := I) V chartCenter)) := by
  obtain ⟨Bc, Kc, hnorm, hholder⟩ :=
    exists_norm_bound_and_holderWith_restrict_parabolicCylinder_Icc_of_contDiffOn
      a b hK hKconv hV halpha
  let L := ((toEuclidean (E := E)).symm : EuclN E →L[Real] E)
  let Kc' : NNReal := Kc * (max 1 ‖L‖₊) ^ (alpha : Real)
  refine ⟨Bc, Kc', ?_, ?_⟩
  · intro p hp
    have h := hnorm (parabolicLinearMap L p) hp
    simpa only [L, parabolicChartPotentialCoefficient,
      euclideanChartPoint, Function.comp_apply, parabolicLinearMap_time,
      parabolicLinearMap_space, parabolicToProduct] using h
  · have h := parabolicHolder_linearMap L hholder
    simpa only [L, Kc', parabolicChartPotentialCoefficient,
      euclideanChartPoint, Function.comp_apply, parabolicLinearMap_time,
      parabolicLinearMap_space, parabolicToProduct] using h

end DifferentialGeometry.Analysis.Schauder

namespace DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder

universe v vE vH

variable {E : Type vE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type vH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclM (E : Type vE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem exists_uniform_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_of_finite
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    {Achart : Type*} [Finite Achart]
    (chartCenter : Achart → M) (K : Achart → Set E)
    (hK : ∀ r, IsCompact (K r))
    (hKconv : ∀ r, Convex Real (K r))
    (hKchart : ∀ r, K r ⊆ interior (extChartAt I (chartCenter r)).target)
    (V : Real → M → Real)
    (hV : ∀ r, ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I (chartCenter r)).symm p.2))
      (Set.Icc a b ×ˢ K r))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Apr Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      ∃ Bc Kc : NNReal,
      (∀ r i j p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          (chartCenter r) i j p‖ ≤ Apr i j) ∧
      (∀ r i j, HolderWith (Ka i j) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              (chartCenter r) i j))) ∧
      (∀ r p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            (chartCenter r) i j p).PosDef) ∧
      (∀ r k p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          (chartCenter r) k p‖ ≤ Bb k) ∧
      (∀ r k, HolderWith (Kb k) alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              (chartCenter r) k))) ∧
      (∀ r p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          (chartCenter r) p‖ ≤ Bc) ∧
      ∀ r, HolderWith Kc alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPotentialCoefficient (I := I) V
              (chartCenter r))) := by
  classical
  letI := Fintype.ofFinite Achart
  obtain ⟨Apr, Ka, Bb, Kb, hAnorm, ha, hpos, hbnorm, hb⟩ :=
    exists_uniform_parabolic_chart_operator_coefficient_schauder_bounds_of_finite
      hG hab habreg chartCenter K hK hKconv hKchart halpha
  have hpotential : ∀ r : Achart, ∃ Bcr Kcr : NNReal,
      (∀ p, p ∈ parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r)) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          (chartCenter r) p‖ ≤ Bcr) ∧
      HolderWith Kcr alpha
        ((parabolicLinearPreimage
          ((toEuclidean (E := E)).symm : EuclM E →L[Real] E)
          (parabolicCylinder (Set.Icc a b) (K r))).restrict
            (parabolicChartPotentialCoefficient (I := I) V
              (chartCenter r))) := by
    intro r
    exact DifferentialGeometry.Analysis.Schauder.exists_parabolicChartPotentialCoefficient_schauder_bounds
      V a b (chartCenter r) (hK r) (hKconv r) (hV r) halpha
  choose Bcr Kcr hpotential using hpotential
  let Bc : NNReal := ∑ r, Bcr r
  let Kc : NNReal := ∑ r, Kcr r
  refine ⟨Apr, Ka, Bb, Kb, Bc, Kc, hAnorm, ha, hpos, hbnorm, hb, ?_, ?_⟩
  · intro r p hp
    exact (hpotential r).1 p hp |>.trans
      (Finset.single_le_sum (fun s _ ↦ zero_le (Bcr s)) (Finset.mem_univ r))
  · intro r
    exact (hpotential r).2.mono
      (Finset.single_le_sum (fun s _ ↦ zero_le (Kcr s)) (Finset.mem_univ r))

theorem exists_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_on_closedBall
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) (center : EuclM E) (R : Real)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center R ⊆ interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center R)))
    {alpha : NNReal} (halpha : alpha ≤ 1) :
    ∃ Apr Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      ∃ Bc Kc : NNReal,
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartPrincipalCoefficient (I := I) G.metric
          chartCenter i j p‖ ≤ Apr i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartPrincipalCoefficient (I := I) G.metric
              chartCenter i j))) ∧
      (∀ p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        (Matrix.of fun i j : Fin (Module.finrank Real E) =>
          parabolicChartPrincipalCoefficient (I := I) G.metric
            chartCenter i j p).PosDef) ∧
      (∀ k p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartDriftCoefficient (I := I) G.metric
          chartCenter k p‖ ≤ Bb k) ∧
      (∀ k, HolderWith (Kb k) alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartDriftCoefficient (I := I) G.metric
              chartCenter k))) ∧
      (∀ p, p ∈ parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R) →
        ‖parabolicChartPotentialCoefficient (I := I) V
          chartCenter p‖ ≤ Bc) ∧
      HolderWith Kc alpha
        ((parabolicCylinder (Set.Icc a b)
          (Metric.closedBall center R)).restrict
            (parabolicChartPotentialCoefficient (I := I) V chartCenter)) := by
  let e := (toEuclidean (E := E)).symm
  let K := e '' Metric.closedBall center R
  have hK : IsCompact K := (isCompact_closedBall center R).image e.continuous
  have hKconv : Convex Real K :=
    (convex_closedBall center R).linear_image e.toLinearEquiv.toLinearMap
  have hpreimage : parabolicLinearPreimage
      (e : EuclM E →L[Real] E)
      (parabolicCylinder (Set.Icc a b) K) =
        parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) := by
    ext p
    constructor
    · intro hp
      rcases hp.2 with ⟨x, hx, hxp⟩
      have hxp' : e x = e p.space := hxp
      exact ⟨hp.1, e.injective hxp' ▸ hx⟩
    · intro hp
      exact ⟨hp.1, ⟨p.space, hp.2, rfl⟩⟩
  obtain ⟨Apr, Ka, hAnorm, ha, hpos⟩ :=
    exists_parabolicChartPrincipalCoefficient_schauder_bounds
      hG a b habreg chartCenter hK hKconv (by simpa only [K, e] using hchart)
        halpha
  obtain ⟨Bb, Kb, hbnorm, hb⟩ :=
    exists_parabolicChartDriftCoefficient_schauder_bounds
      hG hab habreg chartCenter hK hKconv (by simpa only [K, e] using hchart)
        halpha
  obtain ⟨Bc, Kc, hcnorm, hc⟩ :=
    DifferentialGeometry.Analysis.Schauder.exists_parabolicChartPotentialCoefficient_schauder_bounds
      V a b chartCenter hK hKconv (by simpa only [K, e] using hV) halpha
  refine ⟨Apr, Ka, Bb, Kb, Bc, Kc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [e, hpreimage] using hAnorm
  · intro i j
    rw [← hpreimage]
    simpa only [e] using ha i j
  · simpa only [e, hpreimage] using hpos
  · simpa only [e, hpreimage] using hbnorm
  · intro k
    rw [← hpreimage]
    simpa only [e] using hb k
  · simpa only [e, hpreimage] using hcnorm
  · rw [← hpreimage]
    simpa only [e] using hc

end DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn

end
