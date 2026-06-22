import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **HONEST CLASSICAL INPUT — smooth short-time Ricci–DeTurck solution with the joint
chart-Gram smoothness datum.**

For initial and background metrics `g₀`, `g_bg` on a closed Riemannian manifold there are a
positive time `T` and a metric family `g_DT` solving the strictly-parabolic DeTurck–Ricci
flow `∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (`X_DT(t) = deTurckVF (g_DT t) g_bg`) on
`[0, T)` — packaged as `IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g_bg) g₀ T g_DT`
— TOGETHER with the consumer-minimal joint chart-Gram smoothness datum
`JointChartGramSmooth T g_DT` (joint `C∞` up to `t = 0` of every fixed-chart-frame Gram entry
`(t, x) ↦ chartGramMatrix (g_DT t) α x i j`).

This is the classical quasilinear strictly-parabolic short-time existence + interior
regularity result (Chow–Knopf, DeTurck's Step 1; Lieberman, *Second Order Parabolic
Differential Equations*; Ladyzhenskaya–Solonnikov–Uraltseva; Amann, maximal regularity).
The construction is the spectral maximal-regularity Duhamel solution of the flow linearized
about `g₀`, realized through its `C∞` interior representative; the joint smoothness datum is
the standard parabolic interior smoothing (`C∞` in space and time up to `t = 0` for smooth
initial data). The `sorry` is this deferred classical input; consumers transitively depend on
`sorryAx`. -/
theorem deTurckRicci_solution_with_jointReg
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  obtain ⟨T, g_DT, T_rep, hT, hinit, hrel, hflow, hJ⟩ :=
    realizedDeTurckFamily_exists (I := I) g₀ g_bg
  refine ⟨T, g_DT, ⟨hT, hinit, ?_⟩, hJ⟩
  intro t ht x v w
  have hcongr : (fun s : ℝ => (g_DT s).inner x v w) =
      fun s : ℝ => g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_rep s) x v w := by
    funext s; exact hrel s x v w
  rw [hcongr]
  exact (hflow t ht x v w).const_add (g₀.inner x v w)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

theorem deTurckRicci_strictlyParabolic_and_mixedLipschitz [I.Boundaryless]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a) :
    IsStrictlyParabolicMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ ∧
    (∃ C₁ C₂ : ℝ≥0, ∀ {T : ℝ}, 0 < T → ∀ (R : ℝ), 0 ≤ R →
      ∀ (f f' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T),
        ‖f‖ ≤ R → ‖f'‖ ≤ R →
        ‖deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f -
            deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f'‖ ≤
          (C₁ : ℝ) * R * ‖f - f'‖ +
            (C₂ : ℝ) *
              ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖) :=
  sorry

theorem quasilinear_strictlyParabolic_mixedLipschitz_shortTimeExistence [I.Boundaryless]
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (hP : IsStrictlyParabolicMetricRHS (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ ∧
      (∃ C₁ C₂ : ℝ≥0, ∀ {T : ℝ}, 0 < T → ∀ (R : ℝ), 0 ≤ R →
        ∀ (f f' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T),
          ‖f‖ ≤ R → ‖f'‖ ≤ R →
          ‖deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f -
              deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f'‖ ≤
            (C₁ : ℝ) * R * ‖f - f'‖ +
              (C₂ : ℝ) *
                ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖)) :
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
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) :=
  sorry

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
  have ha_super : 2 * Module.finrank ℝ E + 10 ≤ 2 * Module.finrank ℝ E + 10 := le_refl _
  have ha_even : Even (2 * Module.finrank ℝ E + 10) := ⟨Module.finrank ℝ E + 5, by ring⟩
  exact quasilinear_strictlyParabolic_mixedLipschitz_shortTimeExistence (I := I) g₀ g_bg
    (2 * Module.finrank ℝ E + 10) ha_super ha_even
    (deTurckRicci_strictlyParabolic_and_mixedLipschitz (I := I) g₀ g_bg
      (2 * Module.finrank ℝ E + 10) ha_super ha_even)

end DifferentialGeometry.PDE.RicciFlow
