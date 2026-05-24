import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem nabla_equals_partial_plus_christoffel_on_tensors
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

theorem nabla_tensor_single_step_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M) :
    True := sorry

theorem nabla_tensor_iterated_Hk_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
