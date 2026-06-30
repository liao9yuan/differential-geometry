import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Geometry.Curvature.PullbackNaturality

/-!
# The round sphere has constant positive sectional curvature

Combining the homogeneity of the round metric (the orthogonal group acts transitively
by isometries) with the naturality of the Riemann tensor under isometries, a curvature
identity proved at one point spreads to the whole sphere.  Here we record the
**curvature-invariance** half (Step 5A): the metric `(0,4)` Riemann tensor of the round
metric is invariant under `sphereDiffeo e`.

The remaining one-point computation (the explicit chart-Christoffel value at a pole) is
the `ConstPosSecMetric roundMetric` capstone, still ahead.

## Main result

* `metricRm04_round_invariant` — Riemann-tensor invariance under the orthogonal action.
-/

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

/-- **Curvature invariance under the orthogonal action.**  The metric `(0,4)` Riemann
tensor of the round metric at `x` equals its value at `sphereDiffeo e x` on the
pushed-forward vectors — because `sphereDiffeo e` is an isometry of the round metric
(`pullbackMetric_round_eq`) and the Riemann tensor is natural (`metricRm04Std_pullback`). -/
theorem metricRm04_round_invariant (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1)
    (X Y Z W : TangentSpace (𝓡 n) x) :
    metricRm04StdAt (roundMetric (E := E) (n := n)) x X Y Z W
      = metricRm04StdAt (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e x)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x X)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Y)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x Z)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x W) := by
  haveI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  haveI : IsManifold (𝓡 n) 1 (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  haveI : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have h := metricRm04Std_pullback (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e)
    x X Y Z W
  rwa [pullbackMetric_round_eq] at h

end Geometry
end DifferentialGeometry
