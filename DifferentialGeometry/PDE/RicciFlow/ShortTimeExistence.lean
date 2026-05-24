import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.RicciFlow.DeTurckVFTimeFamily
import DifferentialGeometry.PDE.RicciFlow.DeTurckSolutionC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow
import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.LieNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

theorem ricci_flow_short_time_existence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t := sorry

end DifferentialGeometry.PDE.RicciFlow
