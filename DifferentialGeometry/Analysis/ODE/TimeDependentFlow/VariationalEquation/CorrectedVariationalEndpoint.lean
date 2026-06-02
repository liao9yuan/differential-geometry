import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The trivialised variational integral equation at the `t = 0` endpoint

The genuine analytic core of the Jacobian right-continuity at `t = 0`.  For the anchored flow
`Φ`, the moving spatial Jacobian `s ↦ mfderiv I I (Φ s) x v` satisfies, on a right-half
neighbourhood of `0`, the **trivialised** variational integral equation

  `J s = J₀ + ∫₀ˢ fderiv ℝ (chartTrivRepr α (X_DT r)) (extChartAt α (Φ r x)) (J r) dr`,

with the geometrically correct covariant coefficient `fderiv (chartTrivRepr …)` — not the raw
`fderiv (chartRawRepr …)` — together with a near-`0` boundedness `‖J s‖ ≤ B`.  This is built
from the interior chart variational ODE as a continuity-only limit down to the endpoint.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The moving spatial Jacobian `s ↦ mfderiv I I (Φ s) x v` satisfies, near `0`, the
trivialised variational integral equation with covariant coefficient
`fderiv (chartTrivRepr α (X_DT r))`, together with a near-`0` norm bound. -/
theorem corrected_variational_endpoint_data
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T) (Φ : ℝ → M → M)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2)) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hmovtriv : ∀ α : M, ContinuousOn (fun q : ℝ × M => fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α q.2)) (Prod.snd ⁻¹' (chartAt H α).source : Set (ℝ × M)))
    (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦpic : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), Φ s x ∈ (chartAt H α).source ∧
        extChartAt I α (Φ s x) = extChartAt I α x + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x)))
    (hΦbare : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) :
    (∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        (mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT r) z) (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
    ∧ (∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
