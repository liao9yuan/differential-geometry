import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge

/-!
# Continuity of the moving-trivialization first jet

The moving-trivialization chart change `z ↦ chartMovingTriv α z = trivToE α (φ.symm z)` is a
smooth-structure object — the tangent-bundle coordinate change in chart `α` — and is `C∞` on
the chart target.  Consequently its Fréchet derivative `z ↦ fderiv ℝ (chartMovingTriv α) z`
is continuous.  The map is independent of the time variable, so the joint continuity on
`ℝ × M` reduces to continuity in the manifold variable.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The moving-trivialization first jet `z ↦ fderiv ℝ (chartMovingTriv α) z` is continuous
(jointly on `ℝ × M`, through the manifold variable only): a pure smooth-structure fact about
the tangent-bundle chart-transition Jacobian, independent of time. -/
theorem chartMovingTriv_jet_continuous
    (α : M) : ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α q.2)) (Prod.snd ⁻¹' (chartAt H α).source : Set (ℝ × M)) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
