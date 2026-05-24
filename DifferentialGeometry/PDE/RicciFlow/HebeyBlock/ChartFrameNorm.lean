import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open Bundle Manifold
open scoped Manifold ContDiff

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Existence of a non-negative bound governing the chart-frame component
`H^k` seminorms of a tensor field in terms of its intrinsic Sobolev norm.

This is the skeleton-stage placeholder for the chart-frame component
norm-bound estimate: for each chart `α` of `M` and each tensor field in
`TensorPouSobolevHilbert g r s k`, the sum over component multi-indices of
the chart-frame component `H^k` seminorms is bounded by an absolute constant
times the intrinsic Hilbert-Schmidt partition-of-unity-weighted Sobolev
norm. The genuine inequality is stated once the underlying chart-frame and
intrinsic norm definitions are committed; at the skeleton stage we declare
the bound's existence. -/
theorem chart_frame_component_norm_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C := sorry

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry
