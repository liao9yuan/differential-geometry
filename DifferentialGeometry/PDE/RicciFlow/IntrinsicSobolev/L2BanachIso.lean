import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.Integral.L2.Hilbert.Defs

/-!
# Banach equivalence: intrinsic `H^0` ≃L `TensorL2`

The intrinsic partition-of-unity-weighted Sobolev Hilbert space at regularity
order `k = 0` and the metric `L²` Hilbert space of mixed `(r, s)`-tensor
fields are canonically isomorphic as topological vector spaces over `ℝ`.

This file declares the continuous linear equivalence
`TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The canonical continuous linear equivalence between the intrinsic
partition-of-unity-weighted Sobolev Hilbert space at regularity order `0`
and the metric `L²` Hilbert space of mixed `(r, s)`-tensor fields. Both
arise as Hausdorff completions of pre-Hilbert structures on
`SmoothCcTensor g r s`, with equivalent norms at order `k = 0`. -/
noncomputable def TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g := sorry

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
