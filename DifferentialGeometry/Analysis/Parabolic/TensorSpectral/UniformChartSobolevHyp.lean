import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ComponentWkpNormBoundFromH1

/-!
# Uniform-in-`(S, α, Idx, Jdx)` chart-Sobolev `W^{1,2}` hypothesis Prop

This file packages the single conditional hypothesis consumed by the
downstream tensor-spectral pipeline: a uniform-in-`(S, α, Idx, Jdx)`
chart-Sobolev `W^{1,2}` envelope for the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`, with the
right-hand side controlled by the H¹ norm of `S`.

The shape mirrors the per-α headline produced in
`ComponentWkpNormBoundFromH1`, with the chart base point `α` additionally
universally quantified. The constant `C` is required to be nonnegative.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Uniform chart-Sobolev hypothesis.** There exists a nonnegative constant
`C` such that for every smooth compactly-supported H¹ tensor section `S`,
every chart base point `α : M`, and every chart-frame index pair
`(Idx, Jdx)`, the chart-based Sobolev `W^{1,2}` norm of the chart-frame
scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)`. -/
def uniformTensorChartSobolevBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (S : SmoothCcTensorH1 g r s) (α : M)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
