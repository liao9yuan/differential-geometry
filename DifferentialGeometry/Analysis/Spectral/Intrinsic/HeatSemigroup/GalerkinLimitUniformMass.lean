import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinForcingTimeL2Limit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

theorem fatou_weighted_sq_mass_le {ι : Type*} (S : ℕ → Finset ι)
    (hS : Tendsto S atTop atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, Tendsto (fun N => v N i) atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finset_sum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hKsub : K ⊆ S N := hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤ ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKsub
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact le_trans hmono (hbound N)
    exact le_of_tendsto hlim hev
  refine ⟨summable_of_sum_le hnn hpartial, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hpartial

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
