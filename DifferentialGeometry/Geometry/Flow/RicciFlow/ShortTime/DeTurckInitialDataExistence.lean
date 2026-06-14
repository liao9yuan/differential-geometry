import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence

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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) :=
  sorry

end DifferentialGeometry.PDE.RicciFlow
