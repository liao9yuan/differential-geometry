import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciPrincipalPart
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem deturck_ricci_rhs_linearization_at_g0
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
