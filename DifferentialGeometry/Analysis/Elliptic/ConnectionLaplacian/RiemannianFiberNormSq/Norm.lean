import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[implicit_reducible]
noncomputable def riemannianFiberNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRS_riemannianBundle (I := I) (M := M) g r s
  let h : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) := inferInstance
  exact (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

noncomputable def riemannianFiberNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) : ℝ :=
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  ‖T‖

theorem riemannianFiberNorm_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    0 ≤ riemannianFiberNorm g r s b T := by
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_nonneg T

theorem riemannianFiberNorm_eq_sqrt (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s b T) := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRS_riemannianBundle (I := I) (M := M) g r s
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  rw [riemannianFiberNorm, norm_eq_sqrt_tensorInnerPointwise]
  rw [← riemannianFiberNormSq_eq_tensorInnerPointwise]

theorem riemannianFiberNorm_sq (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T ^ 2 = riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  rw [riemannianFiberNorm_eq_sqrt]
  exact Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s b T)

end Elliptic
end Analysis
end DifferentialGeometry
