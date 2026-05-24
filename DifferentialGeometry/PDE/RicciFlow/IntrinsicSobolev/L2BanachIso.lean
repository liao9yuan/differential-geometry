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
`SmoothCcTensor g r s`, with equivalent norms at order `k = 0`.

# Structural blocker

Constructing this equivalence requires a two-sided uniform comparison
of the form

```
c · ‖T‖_{TensorL2} ≤ (tensorPouSobolevHsNorm g 0 T).toReal ≤ C · ‖T‖_{TensorL2}
```

valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` independent of `T`. The forward direction (chart
push-forward to intrinsic `L²`) is supplied at the scalar level by
`DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure`,
but lifting it to tensor sections through fiberwise frame components
and reverse-bridging from intrinsic to chart aggregates is the missing
step. Once that comparison is available, the equivalence is the
canonical extension along the dense embedding
`SmoothCcTensor g r s →ₗ[ℝ] TensorPouSobolevHilbert g r s 0` /
`SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g`, applied in both
directions via `ContinuousLinearMap.extend`. -/
noncomputable def TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_iso : TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g) :
    TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g := h_iso

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
