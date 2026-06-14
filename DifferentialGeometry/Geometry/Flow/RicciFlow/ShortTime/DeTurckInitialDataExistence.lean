import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRicciSolutionExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint

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

This file lives upstream of both headlines, so both can cite the single bundle. -/

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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **(POSITED — md0 interior-regularity core: joint chart-Gram smoothness of the
realized maximal-regularity DeTurck–Ricci solution family.)**

The realize-image family `t ↦ realizeMetricAt g₀ (timeH1.toFun u t)` of the time-`H¹`
maximal-regularity Duhamel mild solution `u` (pinned by `hduh`/`hforce` to the genuine
gauge-pinned linearized DeTurck–Ricci flow, exactly as in `deTurckRicci_realize_flowMatch`)
satisfies the consumer-minimal joint chart-Gram smoothness datum: joint `C∞` up to `t = 0`
of the chart-Gram entries `(t, x) ↦ chartGramMatrix (realizeMetricAt g₀ (u t)) α x i j` on
`Icc 0 T ×ˢ baseSet_α`.

This is the genuinely deep parabolic *maximal-regularity* interior-regularity input: the
mild solution of the strictly parabolic system is `C∞` in space and time up to `t = 0`
(standard parabolic smoothing for the maximal-regularity Duhamel solution), so its realized
metric components are jointly smooth.  The **solution-pinning hypotheses are required**: a
free time-`H¹` path is only `C^½`-in-time, for which `JointChartGramSmooth` would be FALSE;
binding `u` to the genuine maximal-regularity solution (same binders as
`deTurckRicci_realize_flowMatch`) is what makes the joint datum hold.  The `sorry` is this
deferred classical maximal-regularity input; consumers transitively depend on `sorryAx`. -/
theorem deTurckRicci_realizeFamily_jointChartGramSmooth
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g₀ 0 2)
    (hN_coeff : ∀ (u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      (N_cont u').coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i)
    (hNsec_eq : ∀ u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
      Nsec u' = deTurckRemainderSectionGauge (I := I) g_bg g₀ u')
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (a : ℝ) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => N_cont
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t))) :
    JointChartGramSmooth (I := I) T
      (fun t => realizeMetricAt (I := I) g₀ (timeH1.toFun u t)) := by
  sorry

/-- **DeTurck–Ricci short-time solution with the joint chart-Gram smoothness datum.**

Re-runs the existence construction of
`deTurckRicci_isQuasilinearParabolicSolution_exists` and additionally supplies the
consumer-minimal joint chart-Gram smoothness datum
`JointChartGramSmooth T g_DT` for the *same* realized solution family
`g_DT t = realizeMetricAt g₀ (timeH1.toFun u t)`, via
`deTurckRicci_realizeFamily_jointChartGramSmooth` applied to the same maximal-regularity
solution data.  This pairs the existence conjunct with the single joint regularity datum
from which the chart-regularity tail of the headline is derived
(`deTurckRicci_chartRegularity_of_jointChartGramSmooth`). -/
theorem deTurckRicci_solution_with_jointReg
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  classical
  set a : ℕ := deTurckRicciOrder (E := E) with ha_def
  have ha : Module.finrank ℝ E < 2 * (a - 2) := deTurckRicciOrder_spec (E := E)
  obtain ⟨N_cont, repr, Nsec, hN_coeff, hNsec_realize, hrepr_small, hNsec_lip, hNsec_eq⟩ :=
    deTurckRicci_engineConstructionData_exists (I := I) g₀ g_bg a
  obtain ⟨T, hT, hT1, u, gforce, _hcont, htrace, hduh, hforce⟩ :=
    deturck_mildsolution_timeh1 (I := I) (M := M) g₀ a ha
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      N_cont repr Nsec hN_coeff hNsec_realize hrepr_small hNsec_lip
  refine ⟨T, fun t => realizeMetricAt (I := I) g₀ (timeH1.toFun u t), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hT
  · change (realizeMetricAt (I := I) g₀ (timeH1.toFun u 0)) = g₀
    have h0 : timeH1.toFun u 0 = (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) := by
      rw [timeH1.toFun_zero]
      have htr : (timeH1.trace0 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) u
          = u.init := timeH1.trace0_apply u
      rw [← htr, htrace, map_zero]
    rw [h0, realizeMetricAt_zero]
  · exact deTurckRicci_realize_flowMatch (I := I) g₀ g_bg a hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      N_cont Nsec hN_coeff hNsec_eq gforce u hduh hforce
  · exact deTurckRicci_realizeFamily_jointChartGramSmooth (I := I) g₀ g_bg a hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      N_cont Nsec hN_coeff hNsec_eq gforce u hduh hforce

/-- **HONEST CLASSICAL INPUT — standard quasilinear strictly-parabolic short-time existence
+ interior regularity for the Ricci–DeTurck flow.**

For a closed Riemannian manifold the DeTurck-modified flow `∂ₜḡ = −2 Ric(ḡ) + 𝓛_W ḡ` is a
smooth-quasilinear, *strictly parabolic* system (principal symbol `σ[DQ](ζ) = |ζ|²·Id`,
cf. Chow–Knopf, *The Ricci Flow: An Introduction* (AMS), Ch. "Short time existence",
eq. (Q-is-elliptic)); by the standard quasilinear parabolic existence theory it has a smooth
short-time solution from smooth initial data, interior-regular up to `t = 0`. This is exactly
the classical analytic input Chow–Knopf INVOKE (do not re-prove) in DeTurck's Step 1 of the
proof of Thm [Hamilton] (ShortTimeExistenceTheorem): see Lieberman, *Second Order Parabolic
Differential Equations*, Ch. VIII (existence via fixed point) + interior regularity;
Ladyzhenskaya–Solonnikov–Uraltseva; Amann (maximal regularity).

Concretely: for initial and background metrics `g₀`, `g_bg` there exist a positive time `T`
and a metric family `g_DT` solving the strictly parabolic DeTurck–Ricci flow
`∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (with `X_DT(t) = deTurckVF (g_DT t) g_bg`) on
`[0, T)`, packaged as `IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g_bg) g₀ T g_DT`,
TOGETHER with the DeTurck-vector-field and metric regularity data the conjugating-
diffeomorphism construction consumes (interior joint-`C∞`, `C⁰`-up-to-`0`, joint chart-Gram
smoothness, and the `k ≤ 2` spatial jets). These constrain only the internal `g_DT`/`X_DT`,
never `g₀`/the headline statement, so the enrichment is non-leaking.

The closed-interval (`Icc 0 T`) regularity clauses are achievable because `T` is existential:
taking `T` strictly below the maximal existence time makes the smooth solution `C∞` on the
compact `[0,T] × M` (including both endpoints); the flow equation itself is only asserted on
`[0, T)`. The `sorry` is this deferred classical input; consumers transitively depend on
`sorryAx`. -/
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
  obtain ⟨T, g_DT, hex, hJ⟩ := deTurckRicci_solution_with_jointReg (I := I) g₀ g_bg
  exact ⟨T, g_DT, hex,
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g_bg T g_DT hJ⟩

end DifferentialGeometry.PDE.RicciFlow
