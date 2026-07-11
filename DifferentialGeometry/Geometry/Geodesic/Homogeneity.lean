import DifferentialGeometry.Geometry.Geodesic.MaximalInterval

set_option linter.unusedSectionVars false


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section Homogeneity

variable [I.Boundaryless] [CompleteSpace E]

theorem maximalGeodesic_smul_zero_time
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (c : ℝ) :
    maximalGeodesic (I := I) g p (c • v) 0 = p :=
  maximalGeodesic_zero (I := I) g p (c • v)

theorem maximalGeodesic_one_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic (I := I) g p ((1 : ℝ) • v) t =
      maximalGeodesic (I := I) g p v t := by
  rw [one_smul]

end Homogeneity

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
