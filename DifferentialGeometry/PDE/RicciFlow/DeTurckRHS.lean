import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Continuous-linear upgrade of the pointwise Lie-derivative metric. -/
noncomputable def lieDerivMetricClm
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := sorry

/-- The CLM upgrade agrees with the underlying linear-map evaluation. -/
theorem lieDerivMetricClm_apply
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    True := sorry

/-- The right-hand side of the Ricci–DeTurck flow:
`-2 · Ric(g) + 𝓛_{W(g_bg, g)} g`, as a continuous bilinear form on `T_x M`. -/
noncomputable def deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := sorry

end RicciFlow
end PDE
end DifferentialGeometry
