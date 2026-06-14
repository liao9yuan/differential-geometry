import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckShortTime

/-! # DeTurck-Ricci-flow parabolic short-time existence and the metric PDE

The short-time-existence endpoint `deturck_ricci_flow_parabolic_short_time_existence`
for the DeTurck-Ricci flow on a closed manifold, together with the interior and
initial-time forms of the realized metric PDE `∂_t g = -2 Ric(g) + 𝓛_X g`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection
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

/-- **HONEST CLASSICAL INPUT — standard quasilinear strictly-parabolic short-time existence
+ interior regularity for the Ricci–DeTurck flow.**

For a closed Riemannian manifold the DeTurck-modified flow `∂ₜḡ = −2 Ric(ḡ) + 𝓛_W ḡ` is a
smooth-quasilinear, *strictly parabolic* system (principal symbol `σ[DQ](ζ) = |ζ|²·Id`,
cf. Chow–Knopf, *The Ricci Flow: An Introduction* (AMS GSM/MSM), Ch. "Short time existence",
eq. (Q-is-elliptic)); by the standard quasilinear parabolic existence theory it has a smooth
short-time solution from smooth initial data, interior-regular up to `t = 0`. This is exactly
the classical analytic input Chow–Knopf INVOKE (do not re-prove) in the proof of Thm
[Hamilton] (ShortTimeExistenceTheorem); see Lieberman, *Second Order Parabolic Differential
Equations*, Ch. VIII (existence via fixed point) + Ch. on interior regularity;
Ladyzhenskaya–Solonnikov–Uraltseva; Amann (maximal regularity).

Concretely: for initial and background metrics `g₀`, `g_bg` there exist a positive time `T`
and a metric family `g_DT` solving the strictly parabolic DeTurck–Ricci flow
`∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (with `X_DT(t) = deTurckVF (g_DT t) g_bg`) on
`[0, T)`, packaged as `IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g_bg) g₀ T g_DT`,
TOGETHER with the DeTurck-vector-field and metric regularity data the
conjugating-diffeomorphism construction consumes (interior joint-`C∞`, `C⁰`-up-to-`0`, joint
chart-Gram smoothness, and the `k ≤ 2` spatial jets).  These constrain only the internal
`g_DT`/`X_DT`, never `g₀`/the headline statement, so the enrichment is non-leaking.

The `sorry` is this deferred classical input (existence + interior regularity for the
strictly-parabolic smooth-quasilinear DeTurck–Ricci flow from smooth initial data); consumers
transitively depend on `sorryAx`. -/
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
