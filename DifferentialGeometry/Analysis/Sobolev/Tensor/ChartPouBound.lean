import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBoundChartPouEuclFderiv
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma tensorChartComponent_ae_eq_chartPushed_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2
        =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  filter_upwards [self_mem_ae_restrict (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
    with y hy
  rw [tensorChartComponent_def]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2) hy]
  unfold tensorChartComponentPou
  rfl

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry

