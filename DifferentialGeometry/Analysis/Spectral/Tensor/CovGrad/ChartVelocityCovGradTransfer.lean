import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def chartRoughLaplacianSymbol (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α j l y *
      partialDeriv (E := E) j (partialDeriv (E := E) l (h.toFun i k)) y

@[simp] lemma chartRoughLaplacianSymbol_def (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRoughLaplacianSymbol (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (partialDeriv (E := E) l (h.toFun i k)) y :=
  rfl

theorem chartRicciDeTurck_gaugeCancellation_principalSymbol
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    (-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y +
        chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i k y =
      chartRoughLaplacianSymbol (I := I) g α h i k y :=
  sorry

def chartRoughLaplacianLowerCorr (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (α : M) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g₁ α j l y *
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
          (covGrad (I := I) (M := M) g₀ 0 2 S) α j ![] ![l, i, k]
          (toEuclidean (E := E) y)
        + euclidPartial (E := E) j
            (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y')
            (toEuclidean (E := E) y))

theorem chartRoughLaplacianSymbol_eq_chartInvGram_iteratedCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    (hlink : ∀ a b : Fin (Module.finrank ℝ E),
      (fun y => h.toFun a b y) =ᶠ[nhds (extChartAt I α α)]
        (fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![a, b]
          ((extChartAt I α).symm y))) :
    chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) =
      (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
        - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α) :=
  sorry

theorem chartInvGram_iteratedCovGrad_trace_eq_unitModel_appCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v :=
  sorry

theorem chartRicciSecondOrderPrincipalSymbol_eq_appCc_iteratedCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (h : ChartMetricPerturbation E)
    (hlink : ∀ a b : Fin (Module.finrank ℝ E),
      (fun y => h.toFun a b y) =ᶠ[nhds (extChartAt I α α)]
        (fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![a, b]
          ((extChartAt I α).symm y)))
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          ((-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
            chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α))) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v
        - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
  classical
  have hyint : (extChartAt I α α) ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (mem_extChartAt_target α)
  have hgauge : ∀ i k : Fin (Module.finrank ℝ E),
      (-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
          chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α) =
        chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) :=
    fun i k => chartRicciDeTurck_gaugeCancellation_principalSymbol (I := I) g₁ g₁ α h i k hyint
  have hhessian : ∀ i k : Fin (Module.finrank ℝ E),
      chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) =
        (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
          - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α) := by
    intro i k
    have := chartRoughLaplacianSymbol_eq_chartInvGram_iteratedCovGrad
      (I := I) g₀ g₁ S α h i k hlink
    simpa using this
  calc
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          ((-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
            chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α)))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              ((∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
                - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [hgauge i k, hhessian i k]
      _ = (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α))
            - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                  chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v
          - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          rw [chartInvGram_iteratedCovGrad_trace_eq_unitModel_appCc (I := I) g₀ g₁ S α v]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
