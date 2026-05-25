import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Chart-α-local Picard initial-condition data for a time-dependent vector
field on a closed manifold, packaged in the same chart-coord form as
`time_dependent_vf_chart_local_picard_with_lipschitz`.

The conclusion provides a chart-coordinate flow `flow : E → ℝ → E` on a
closed model-space ball of radius `r'` around `(chartAt H α) α`, with
`flow y 0 = y` and the chart-coordinate ODE
`HasDerivWithinAt (flow y) (X t ((chartAt H α).symm (I.symm (flow y t)))) [0,T] t`
on the time interval `[0, T]`.

This is the chart-coord initial-condition slice of the chart-cover global
flow construction (paralleling `ChartLocalPicardData`). It is deliberately
stated in chart-α-coord form rather than as a manifold-level
`ContMDiffOn I I ∞ (φ t) U` smoothness statement: the manifold-level
`C^∞`-in-IC smoothness for Picard flows is not available from Mathlib's
`IsPicardLindelof` API (which provides only Lipschitz-in-IC), and the
downstream chart-cover assembly in `Glue` / `Bijective` consumes the
chart-α-coord form directly. The hypotheses
* `hCont`: `Function.uncurry X` is continuous on `ℝ × M`;
* `hLip`: there exist a positive horizon `L`, positive radius `r`, and
  non-negative Lipschitz constant `K` such that for each `t ∈ [0, L]`
  the chart pushforward `X t ∘ (chartAt H α).symm` is `K`-Lipschitz on
  the open ball of radius `r` in the model space
are the minimal separable continuity / Lipschitz data needed to invoke
Mathlib's `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`
through the chart `chartAt H α`. The proof is a thin re-export of
`time_dependent_vf_chart_local_picard_with_lipschitz` under this headline
name.
-/
theorem banach_flow_smooth_in_ic
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) :=
  time_dependent_vf_chart_local_picard_with_lipschitz X α hCont hLip

end DifferentialGeometry.PDE.RicciFlow.ODE
