import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem hasDerivAt_realizedFam_chartLieDeTurckComp (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y)
      (deriv (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y) s₀) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg x i j r.2)
      (s₀, y) :=
    gen_joint_chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG g_bg i j hs₀ hy
  have hcomp : (fun s : ℝ =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j y) =
      (fun r : ℝ × E =>
        chartLieDeTurckComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg x i j r.2)
        ∘ (fun s : ℝ => (s, y)) := by funext s; rfl
  rw [hcomp]
  exact ((hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
    (by simp)).hasDerivAt

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
