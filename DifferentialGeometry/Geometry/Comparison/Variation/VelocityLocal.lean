import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong

set_option autoImplicit false

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The velocity of a smooth curve is differentiable in the tangent
trivialization centered at the given parameter. -/
theorem velocity_rep_diffAt
    (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I ∞ gamma t) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) gamma
        (fun s ↦ (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s :
          ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t) t := by
  have hgamma2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t :=
    hgamma.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  simpa only [chartRepAt] using
    MFDerivAlongCurve.velocity_coord_diff (I := I) gamma t hgamma2

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
