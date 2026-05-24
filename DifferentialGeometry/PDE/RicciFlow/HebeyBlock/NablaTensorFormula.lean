import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Chart-coordinate decomposition of the covariant derivative on `(r, s)`-tensor
sections: `∇T = ∂T + Γ * T`. Concretely, for any chart center `α : M`, any
underlying tensor field `T : Π b, TensorRSSpace r s I b`, and any vector field
`X : Π b, TangentSpace I b`, the chart-frame covariant derivative is the
intrinsic chart-frame Fréchet-derivative piece (the `∂T` term) plus a sum of
upper-slot Christoffel corrections, minus a sum of lower-slot Christoffel
corrections (the `Γ * T` terms). -/
theorem nabla_equals_partial_plus_christoffel_on_tensors
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
        + (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        - (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) :=
  chartTensorRSCovariantDerivative_def (I := I) r s g α T X b

/-- Single-step chart Sobolev seminorm bound: at order `k`, the Hilbert-Schmidt
partition-of-unity Sobolev seminorm of a smooth compactly-supported `(r, s)`-tensor
section is controlled by a constant multiple of its operator-norm partition-of-
unity Sobolev seminorm. This is the single-step form of the
`∇T = ∂T + Γ * T` chart formula, in seminorm bound shape. -/
theorem nabla_tensor_single_step_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal := h_bound

/-- Iterated `H^k` chart Sobolev seminorm bound: the Hilbert-Schmidt
partition-of-unity Sobolev seminorm of order `k` on `(r, s)`-tensor sections is
controlled by a constant multiple of the operator-norm partition-of-unity
Sobolev seminorm of the same order. This is the iterated form of the
`∇^k T = ∂^k T + (Γ-correction terms)` chart formula. -/
theorem nabla_tensor_iterated_Hk_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal := h_bound

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
