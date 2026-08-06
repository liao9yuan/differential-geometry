import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.QuasilinearAbstractShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSRepresentation

/-! # DeTurck–Ricci parabolic short-time existence and interior regularity

The single honest analytic input that both short-time-existence headlines consume:
existence of a short-time solution of the strictly-parabolic Ricci–DeTurck flow from
smooth initial data, bundled with the up-to-`t = 0` interior regularity that the
diffeomorphism pullback needs.

* the genuine Ricci-flow headline `ricci_flow_short_time_existence`
  (`Geometry/Flow/RicciFlow/ShortTimeExistence.lean`) consumes the full bundle
  (existence + DeTurck-vector-field / chart-Gram regularity for the pullback);
* the Ricci–DeTurck headline `deTurckRicci_shortTime_existence_of_closed`
  (`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`) consumes only its existence
  conjunct (`IsQuasilinearMetricParabolicSolution`).

This file lives upstream of both headlines, so both can cite the single bundle. The
chart-regularity tail of the headline (the six interior-regularity conjuncts) is
**derived sorry-free** from a single joint chart-Gram smoothness datum
`JointChartGramSmooth` by `deTurckRicci_chartRegularity_of_jointChartGramSmooth`
(`DeTurckChartRegularityFromJoint.lean`); the remaining classical analytic content is the
existence of a genuine smooth solution family carrying that datum,
`deTurckRicci_solution_with_jointReg`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS domDomCongrSection)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem deTurckRicci_solution_with_jointReg
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  have ha_super : 2 * Module.finrank ℝ E + 10 ≤ 4 * Module.finrank ℝ E + 10 := by omega
  exact quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence (I := I)
    (deTurckRicciRHS (I := I) g_bg) g₀ (4 * Module.finrank ℝ E + 10) ha_super
    (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg (4 * Module.finrank ℝ E + 10))
    (fun S {δ} hδ_lt hδ => deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
      (symmS (I := I) (M := M) g₀ S) hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ))
    (fun g x v w => deTurckRicciRHS_symm (I := I) g_bg g x v w)
    (deTurckRicciRHS_isStrictlyParabolic_at_self (I := I) g₀ g_bg)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      (4 * Module.finrank ℝ E + 10) ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) (4 * Module.finrank ℝ E + 10) ha_super)
    (deTurckRicciRHS_isSmoothQuasilinear (I := I) g_bg)
    (deTurck_rem_repr (I := I) (M := M) g₀ g_bg)
    (deTurckRicci_forcingBootstrap_symm (I := I) (M := M) g₀ g_bg
      (4 * Module.finrank ℝ E + 10) (by omega))

theorem deturck_ricci_flow_parabolic_short_time_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  obtain ⟨T, g_DT, hsol, hJ⟩ := deTurckRicci_solution_with_jointReg (I := I) g₀ g_bg
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g_bg T g_DT hJ
  exact ⟨T, g_DT, hsol, h2, h3, h4, h5, h6, h7⟩

end DifferentialGeometry.PDE.RicciFlow
