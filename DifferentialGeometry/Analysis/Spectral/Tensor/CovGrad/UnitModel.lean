import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

/-!
# Unit evaluation of covariant tensor sections

This module provides the canonical unit `(0, 0)`-tensor and the corresponding
unit-evaluated model form of a smooth `(0, s)`-tensor section.
-/

noncomputable section

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The canonical unit `(0, 0)`-tensor used to evaluate a mixed tensor with no
contravariant slots. -/
def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))

/-- The model `(0, s)`-form obtained by evaluating a smooth `(0, s)`-tensor
section on the canonical unit `(0, 0)`-tensor. -/
def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

