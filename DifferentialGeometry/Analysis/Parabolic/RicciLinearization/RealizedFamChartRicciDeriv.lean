import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory Bundle
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma hasDerivAt_of_shift {f : ℝ → ℝ} {f' s₀ : ℝ}
    (hshift : HasDerivAt (fun u => f (s₀ + u)) f' 0) : HasDerivAt f f' s₀ := by
  have hz : (s₀ : ℝ) - s₀ = 0 := by ring
  have hshift' : HasDerivAt (fun u => f (s₀ + u)) f' (s₀ - s₀) := by rw [hz]; exact hshift
  have hcomp := HasDerivAt.comp_sub_const s₀ s₀ hshift'
  have heq : (fun s : ℝ => f (s₀ + (s - s₀))) = f := by funext s; congr 1; ring
  rwa [heq] at hcomp

theorem hasDerivAt_realizedRicciChartSum_general (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (_hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (_hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (_hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1)
    (h₀ : ChartMetricPerturbation E)
    (hfam : IsMetricPerturbationFamily (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h₀
      (fun u => realizedFam (I := I) g₀ T T' hδ hδ' (s₀ + u))) :
    HasDerivAt (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          (chartRicciSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h₀ i k (extChartAt I x x) +
            ricciDerivFirstOrderRemainder (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h₀ i k (extChartAt I x x))) s₀ := by
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hbody : (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
            (extChartAt I x x)) := by
    funext s; rw [realizedRicciChartSum]
  rw [hbody]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  have hRic : HasDerivAt
      (fun s : ℝ => chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
        (extChartAt I x x))
      (chartRicciSecondOrderPart (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h₀ i k (extChartAt I x x) +
        ricciDerivFirstOrderRemainder (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h₀ i k (extChartAt I x x)) s₀ := by
    refine hasDerivAt_of_shift ?_
    exact hasDerivAt_chartRicciTensor (I := I) hfam i k hy
  exact hRic.const_mul _

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
