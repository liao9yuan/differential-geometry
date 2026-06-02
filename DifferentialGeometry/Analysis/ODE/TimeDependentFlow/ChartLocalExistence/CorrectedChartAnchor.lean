import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The `t = 0`-anchored corrected chart flow on a uniform horizon

Assembling the per-chart corrected Picard solutions into a single `t = 0`-anchored manifold
flow `Φ0` on a uniform horizon `σ` (extracted from a finite subcover of the compact
manifold), with `Φ0 0 = id`, the bare manifold velocity on `(0, σ)`, the **trivialised**
chart integral identity
`extChartAt α (Φ0 s x) = extChartAt α x + ∫₀ˢ chartTrivRepr α (X r) (extChartAt α (Φ0 r x))`
on each orbit's right-half neighbourhood of `0` (carrying a per-orbit norm bound `C` on the
trivialised chart velocity), and right-continuity of each orbit `s ↦ Φ0 s x` at `0`.  Every
conclusion is stated through the corrected `chartTrivRepr` field or the intrinsic bare
velocity — never the raw chart value.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Assemble the per-chart corrected Picard solutions into a single `t = 0`-anchored manifold
flow `Φ0` on a uniform horizon `σ`, with `Φ0 0 = id`, bare velocity on `(0, σ)`, the
trivialised chart integral identity on each orbit's right-half neighbourhood of `0` (with a
per-orbit norm bound `C` on the trivialised chart velocity), and right-continuity of each
orbit at `0`. -/
theorem corrected_chart_anchor_flow_build
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2)) (Set.univ : Set (ℝ × M)))
    (hgrad : ∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2)) (Set.univ : Set (ℝ × M))) :
    ∃ (σ : ℝ) (_ : 0 < σ) (Φ0 : ℝ → M → M),
      (∀ x : M, Φ0 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) σ, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ioo (0 : ℝ) σ) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ0 t x)))) ∧
      (∀ x : M, ∃ α : M, ∃ δ : ℝ, ∃ C : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
        ∀ s ∈ Set.Ico (0 : ℝ) (min δ σ), Φ0 s x ∈ (chartAt H α).source ∧
          (extChartAt I α (Φ0 s x) = extChartAt I α x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X r) (extChartAt I α (Φ0 r x)))
          ∧ ‖chartTrivRepr (I := I) α (X s) (extChartAt I α (Φ0 s x))‖ ≤ C) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ0 s x) (Set.Ici (0 : ℝ)) 0) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
