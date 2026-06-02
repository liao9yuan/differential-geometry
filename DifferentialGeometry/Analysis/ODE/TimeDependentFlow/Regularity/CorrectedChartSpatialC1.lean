import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge

/-!
# Spatial `C¹`-Lipschitz regularity of the corrected chart field

At a base chart `α`, the *corrected* chart field `y ↦ chartTrivRepr α (X t) y` (the
trivialised representation, the geometrically correct chart velocity) is jointly continuous
in `(t, y)` and uniformly-in-time Lipschitz on a ball around the chart centre.  This is
derived from the joint continuity of `X`, the continuity of the raw chart gradient, and the
continuity of the smooth moving-trivialization jet, via the convention bridge
`chartTrivRepr = chartMovingTriv · ∘ chartRawRepr` and the product rule for its Fréchet
derivative.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Metric
open scoped Manifold Topology ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- At base chart `α`, the corrected chart field `y ↦ chartTrivRepr α (X t) y` is jointly
continuous and uniformly-in-time `K`-Lipschitz on a ball around the chart centre, from the
continuity + chart-gradient data of `X` and the smooth moving-trivialization jet. -/
theorem corrected_chart_field_lipschitz_of_data
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hcont : ContinuousOn (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2)) (Set.univ : Set (ℝ × M)))
    (hgrad : ContinuousOn (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2)) (Set.univ : Set (ℝ × M)))
    (hmovtriv : ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α q.2)) (Prod.snd ⁻¹' (chartAt H α).source : Set (ℝ × M))) :
    ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        ContinuousOn (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.closedBall (I ((chartAt H α) α)) r)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K) (fun y : E => chartTrivRepr (I := I) α (X t) y) (Metric.ball (I ((chartAt H α) α)) r)) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
