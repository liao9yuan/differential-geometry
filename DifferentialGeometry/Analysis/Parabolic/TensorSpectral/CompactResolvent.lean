import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CompactInclusion
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.RellichTensor

/-!
# Compactness of the L²-side tensor resolvent

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
combines the two trivial ingredients to derive the L²-side compactness
of the variational tensor resolvent
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`
from the uniform-in-`(S, α, Idx, Jdx)` chart-Sobolev `W^{1,2}` envelope
`uniformTensorChartSobolevBound g r s`.

The factorisation
`tensorResolventL2 g r s = TensorH1ComplToTensorL2 g r s ∘L
  tensorResolvent g r s`
makes this purely a composition of the H¹ → L² compactness with the
bounded resolvent.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Headline: conditional compactness of the L²-side tensor resolvent -/

/-- **Conditional compactness of the L²-side tensor resolvent.** Under the
uniform-in-`(S, α, Idx, Jdx)` chart-Sobolev `W^{1,2}` envelope
`uniformTensorChartSobolevBound g r s`, the L²-side resolvent operator
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`
is a compact operator.

The proof combines two trivial ingredients:
* `TensorH1ComplToTensorL2_isCompactOperator`: compactness of the
  H¹ → L² tensor inclusion conditional on the same uniform hypothesis;
* `tensorResolventL2_isCompactOperator_of_isCompactOperator`: the
  compositional reduction that derives L²-side compactness from
  H¹ → L² compactness via the factorisation
  `tensorResolventL2 = TensorH1ComplToTensorL2 ∘L tensorResolvent`. -/
theorem tensorResolventL2_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2_isCompactOperator
      (I := I) (M := M) g r s h_uniform)

/-! ## Companion: compact self-adjoint package on the L²-side resolvent

Self-adjointness is already established unconditionally in
`Resolvent.lean::tensorResolventL2_isSelfAdjoint`. Combining it with the
present compactness result yields the precise hypothesis needed for the
compact self-adjoint spectral theorem on the L² Hilbert space. -/

/-- The L²-side tensor resolvent is both a compact operator and
self-adjoint, conditional on the uniform chart-Sobolev hypothesis. -/
theorem tensorResolventL2_isCompactOperator_and_isSelfAdjoint_of_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator
      (I := I) (M := M) g r s h_uniform,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

/-! ## Sanity test -/

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : uniformTensorChartSobolevBound g r s) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g r s h

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2_isCompactOperator_and_isSelfAdjoint_of_uniform

end Sanity
