import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.Integral.Connection.LeviCivita

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold ContDiff

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem cartan_formula_for_lie_deriv_metric
    (g : SmoothRiemannianMetric I M)
    (W : ∀ x : M, TangentSpace I x)
    (x : M) (v w : TangentSpace I x) :
    True := sorry

theorem chart_christoffel_expansion_of_nabla_on_vf
    (g : SmoothRiemannianMetric I M)
    (W : ∀ x : M, TangentSpace I x) :
    True := sorry

theorem metric_compat_coord_identity
    (g : SmoothRiemannianMetric I M) :
    True := sorry

theorem cartan_formula_chart_algebra
    (g : SmoothRiemannianMetric I M) :
    True := sorry

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
