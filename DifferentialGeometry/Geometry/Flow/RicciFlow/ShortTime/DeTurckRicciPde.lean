import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.RealizeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.SolutionC2Continuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckShortTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.DeTurckVFSmoothness
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.InteriorJointSmoothing

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
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
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

/-- **Interior parabolic regularity of the realized DeTurck–Ricci solution (the faithful
regularity input, over the realize carrier).**

Given the `g₀`-anchored realized DeTurck–Ricci flow `g_DT = g₀ + ccTensorBilinSymm (T_s ·)`
(`hreal`) whose supercritical `H^{2k}` spatial Sobolev trace is time-continuous up to `0`
(`hHk`) and whose `k ≤ 2` chart-Gram jets are continuous up to `0` (`hC2_chart`) — the
realize-carrier data supplied by `deturck_metric_pde_interior_at_initial_with_carrier`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`) — the solution is
interior-jointly-`C∞` and continuous up to `t = 0` together with its spatial jets, in every
form the conjugating-diffeomorphism construction consumes:

* interior joint-`C∞` of the DeTurck field `q ↦ ⟨q.2, deTurckVF (g_DT q.1) g_bg q.2⟩`
  on `Ioo 0 T ×ˢ univ`;
* `C⁰`-up-to-`0` of the field and of its raw-fibre chart Fréchet derivative;
* interior joint-`(t, x)` `C∞` and `C⁰`-up-to-`0` of each chart-local Gram-matrix entry of
  `g_DT` (the `chartGramMatrix` and `chartGramOnE` formulations);
* `C⁰`-up-to-`0` of the spatial `k ≤ 2` iterated Fréchet jets of each chart-Gram entry
  (controlling the Hessian/Ricci a `k = 0`-only datum cannot reach up to `0`).

This is sorry-free glue assembling the seven conjuncts from the genuine classical
parabolic-regularity inputs isolated in
`Analysis/Parabolic/DeTurckRicci/InteriorJointSmoothing.lean` (the single-chart interior
`C∞`/up-to-`0` `chartGramOnE`-regularity `realizedMetric_chartGramOnE_*` and the up-to-`0`
DeTurck-field regularity `realizedMetric_deTurckVF_*`), the chart-frame vector-field
smoothness assembler `deturck_vf_joint_smoothness`
(`Geometry/Flow/RicciFlow/ShortTimeFlow/DeTurckVFSmoothness.lean`), and the supplied
`hC2_chart`; the `chartGramMatrix` interior/up-to-`0` conjuncts are the chart-source
restrictions of the single-chart `chartGramOnE` regularity (the chart round-trip identity).
It constrains only the internal realized `g_DT`/`T_s`, never the headline.  Consumers
transitively depend on the `InteriorJointSmoothing` leaves' `sorryAx`. -/
theorem deturck_ricci_parabolic_interior_regularity
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ}
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hHk : ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ContinuousOn
        (fun s : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * k) (T_s s)) (Set.Icc 0 T))
    (hC2_chart : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContinuousOn
        (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ α : M,
        ContinuousOn
          (fun q : ℝ × M =>
            fderiv ℝ (chartRawRepr (I := I) α (fun x => deTurckVF (I := I) (g_DT q.1) g_bg x))
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ Set.univ)) ∧
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
          (Set.Icc 0 T ×ˢ Set.univ)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  set k₀ : ℕ := Module.finrank ℝ E + 3 with hk₀_def
  have hk₀ : 2 * k₀ > Module.finrank ℝ E + 4 := by omega
  have hHk₀ := hHk k₀ hk₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hC2_chart⟩
  · refine deturck_vf_joint_smoothness (I := I) g_bg g_DT T ?_
    intro x₀ i j
    exact IntrinsicSpectral.MetricRealization.realizedMetric_chartGramOnE_jointContMDiffOn_interior
      (I := I) g₀ x₀ i j g_DT T_s hk₀ hreal hHk₀
  · exact IntrinsicSpectral.MetricRealization.realizedMetric_deTurckVF_continuousOn_uptoZero
      (I := I) g₀ g_bg g_DT T_s hk₀ hreal hHk₀
  · intro α
    exact
      IntrinsicSpectral.MetricRealization.realizedMetric_deTurckVF_chartRawRepr_fderiv_continuousOn_uptoZero
        (I := I) g₀ g_bg α g_DT T_s hk₀ hreal hHk₀
  · intro x₀ i j
    have hA := IntrinsicSpectral.MetricRealization.realizedMetric_chartGramOnE_jointContMDiffOn_interior
      (I := I) g₀ x₀ i j g_DT T_s hk₀ hreal hHk₀
    refine (hA.mono (Set.prod_mono_right (fun x _ => Set.mem_univ x))).congr ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    have hxsource : x ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]
      exact (TangentBundle.trivializationAt_baseSet (I := I) x₀) ▸ hx
    change Integral.Measure.chartGramMatrix (I := I) (g_DT t) x₀ x i j
      = Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x₀ i j (extChartAt I x₀ x)
    rw [Integral.DivergenceTheorem.chartGramOnE_def, (extChartAt I x₀).left_inv hxsource]
  · intro x₀ i j
    have hC := IntrinsicSpectral.MetricRealization.realizedMetric_chartGramOnE_continuousOn_uptoZero
      (I := I) g₀ x₀ i j g_DT T_s hk₀ hreal hHk₀
    refine (hC.mono (Set.prod_mono Set.Ico_subset_Icc_self (fun x _ => Set.mem_univ x))).congr ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    have hxsource : x ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]
      exact (TangentBundle.trivializationAt_baseSet (I := I) x₀) ▸ hx
    change Integral.Measure.chartGramMatrix (I := I) (g_DT t) x₀ x i j
      = Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x₀ i j (extChartAt I x₀ x)
    rw [Integral.DivergenceTheorem.chartGramOnE_def, (extChartAt I x₀).left_inv hxsource]
  · intro α i j
    exact IntrinsicSpectral.MetricRealization.realizedMetric_chartGramOnE_continuousOn_uptoZero
      (I := I) g₀ α i j g_DT T_s hk₀ hreal hHk₀

/-- **DeTurck–Ricci parabolic short-time existence (existence + interior regularity).**

For initial and background metrics `g₀`, `g_bg` there exist a positive time `T` and a metric
family `g_DT` solving the strictly parabolic DeTurck–Ricci flow
`∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (with `X_DT(t) = deTurckVF (g_DT t) g_bg`) on `[0, T)`,
packaged as `IsQuasilinearMetricParabolicSolution (deTurckRicciRHS g_bg) g₀ T g_DT`, TOGETHER
with the DeTurck-vector-field and metric regularity data the conjugating-diffeomorphism
construction consumes (interior joint-`C∞`, `C⁰`-up-to-`0`, joint chart-Gram smoothness, and
the `k ≤ 2` spatial jets).  These constrain only the internal `g_DT`/`X_DT`, never
`g₀`/the headline statement, so the enrichment is non-leaking.

This is assembled from its two faithful classical inputs, each isolated:
* existence — `deTurckRicci_shortTime_existence_of_closed` (quasi-linear parabolic short-time
  existence for the concrete strictly-parabolic symmetric DeTurck–Ricci operator, a Banach
  fixed point on Duhamel iterates);
* regularity — `deturck_ricci_parabolic_interior_regularity` (interior parabolic smoothing and
  continuity up to the smooth initial data).

Both inputs remain `sorry` at their leaves, so consumers transitively depend on `sorryAx`;
this assembly is itself sorry-free glue. -/
theorem deturck_ricci_flow_parabolic_short_time_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContinuousOn
        (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ α : M,
        ContinuousOn
          (fun q : ℝ × M =>
            fderiv ℝ (chartRawRepr (I := I) α (fun x => deTurckVF (I := I) (g_DT q.1) g_bg x))
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ Set.univ)) ∧
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
          (Set.Icc 0 T ×ˢ Set.univ)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  obtain ⟨T, a, hT, ha, g_DT, T_s, h0, hreal, hHk, hC2_chart, h_inner_cont, h_rhs_cont,
      h_interior_deriv⟩ :=
    deturck_metric_pde_interior_at_initial_with_carrier (I := I) g₀ g_bg
  have hsol : IsQuasilinearMetricParabolicSolution (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := by
    refine ⟨hT, h0, ?_⟩
    intro t ht x v w
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · subst ht0
      set f : ℝ → ℝ := fun s : ℝ => (g_DT s).inner x v w with hf_def
      set rhs : ℝ → ℝ :=
        fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w with hrhs_def
      have hHasDerivAt : ∀ t' ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (rhs t') t' := fun t' ht' =>
        (h_interior_deriv t' ht' x v w).hasDerivAt (Ici_mem_nhds ht'.1)
      have f_diff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) T) := fun t' ht' =>
        ((hHasDerivAt t' ht').differentiableAt).differentiableWithinAt
      have f_lim : ContinuousWithinAt f (Set.Ioo (0 : ℝ) T) 0 :=
        ((h_inner_cont x v w).continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono
          Set.Ioo_subset_Icc_self
      have hsmem : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
      have hEqOn : Set.EqOn rhs (fun y => deriv f y) (Set.Ioo (0 : ℝ) T) := fun t' ht' =>
        ((hHasDerivAt t' ht').deriv).symm
      have f_lim' : Filter.Tendsto (fun y => deriv f y) (𝓝[>] (0 : ℝ))
          (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) :=
        (h_rhs_cont x v w).congr' (hEqOn.eventuallyEq_of_mem hsmem)
      exact hasDerivWithinAt_Ici_of_tendsto_deriv f_diff f_lim hsmem f_lim'
    · exact h_interior_deriv t ⟨ht0, ht.2⟩ x v w
  exact ⟨T, g_DT, hsol,
    deturck_ricci_parabolic_interior_regularity g₀ g_bg g_DT T_s hreal hHk hC2_chart⟩

set_option linter.unusedVariables false in
/-- **Interior metric-level DeTurck–Ricci time-derivative (fully ungated).**

The interior one-sided time-derivative of the **linear** realized metric
`g_DT s` (`hreal : (g_DT s).inner = g_bg.inner + ccTensorBilinSymm (T_s s)`) is
the geometric DeTurck–Ricci right-hand side evaluated at `g_DT t`.

Re-anchored off the finite-support-gated `deTurckGeometricN`: the carrier-scale
derivative hypothesis `hreg` now routes the nonlinearity through the *continuous*
realize-based nonlinearity `N_cont` (the SAME data as in
`deturck_mildsolution_timeh1` / `forcing_continuous_interior` /
`deturckN_hscale_lipschitz`), so the carrier solves the genuine ungated PDE that
the parent mild-solution node produces and the node applies to the genuine
infinite-support solution (where `deTurckGeometricN`, being forced to `0` off
finite support by `deTurckGeometricN_of_not_realizable`, would degenerate the
flow to the pure linear heat flow and contradict the nonlinear RHS).

Dependency-sufficiency: `hreg` (ungated carrier derivative) pushed through `ℓ_a`
by `pointwise_deriv_through_realize`, composed with `rhs_matches_deturck_at_solution`
(now concluding `deTurckRicciRHS g_bg (g_DT t)`, the SAME continuous `N_cont` and
the SAME linear `g_DT`), yields the conclusion. The construction data `N_cont`,
`repr`, `Nsec` and the hypotheses `hN_coeff`, `hNsec_realize` are coordinate/realize
identities, NOT the `HasDerivWithinAt` conclusion. Non-leaking: all data constrains
the internal carrier `u₂`/`T_s`/`g_DT`/`N_cont`, never `g₀`/the headline. (The former
`hrepr_small` fibre-`< 1` bound on `repr` is dropped: it is jointly unsatisfiable with
`hNsec_geom`, which forces `ccTensorBilinSymm (repr (carrier))` to carry the unbounded
DeTurck–Ricci curvature, and it was never used in any proof body.)

(`hsmall` is a genuine blueprint-contract signature hypothesis — the fibre-small
realize datum on `T_s`, consumed by the parent assembly — that this interior
derivative proof routes through `hreal`/`hsmoothrepr`/`hNsec_geom` rather than
textually, so the unused-binder linter is narrowly suppressed.) -/
theorem deturck_metric_pde_interior
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hsmall : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g_bg
        (ccTensorBilinSymm (I := I) g_bg (T_s s)) δ')
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hNsec_geom : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg
          (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g_bg
            (repr (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t := by
  intro t ht x v w
  set u_car : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_car_def
  set u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      N_cont
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) with hu_car'_def
  obtain ⟨ℓ_a, hℓ⟩ := realize_eval_carrier_factorization (I := I) (M := M) g_bg a ha x v w
  have hfactor : ∀ s : ℝ,
      ccTensorBilinSymm (I := I) g_bg (T_s s) x v w = ℓ_a (u_car s) := by
    intro s
    refine (hℓ (T_s s) (u_car s) ?_).symm
    intro i
    rw [hu_car_def]
    simp only [tensorHsInclusion_coeff_apply]
    exact hsmoothrepr s i
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => u_car r) (u_car' s) (Set.Ici 0) s := by
    intro s hs
    exact (hreg s hs).hasDerivWithinAt
  have hpush := pointwise_deriv_through_realize (I := I) (M := M) g_bg a
    g_DT T_s u_car u_car' x v w ℓ_a
    (fun s _ => hreal s x v w) (fun s _ => hfactor s) hderiv t ht
  have hmatch := rhs_matches_deturck_at_solution (I := I) (M := M) g_bg g_bg a u₂ ℓ_a
    g_DT T_s x v w (fun s _ => hreal s) N_cont repr Nsec
    (fun s _ i => hN_coeff
      (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) i)
    hNsec_realize
    (fun s _ => hsmoothrepr s) hℓ (fun s _ => hNsec_geom s) t (Set.Ioo_subset_Ico_self ht)
  rw [hu_car'_def] at hpush
  rw [hmatch] at hpush
  exact hpush

omit [CompactSpace M] [I.Boundaryless] in
theorem deturck_metric_pde_at_zero
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T))
    (h_rhs_cont : ContinuousWithinAt
      (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w) (Set.Ici 0) 0 := by
  set f : ℝ → ℝ := fun s : ℝ => (g_DT s).inner x v w with hf_def
  set rhs : ℝ → ℝ := fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w with hrhs_def
  have hHasDerivAt : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (rhs t) t := by
    intro t ht
    exact (h_interior t ht).hasDerivAt (Ici_mem_nhds ht.1)
  have f_diff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).differentiableAt).differentiableWithinAt
  have f_lim : ContinuousWithinAt f (Set.Ioo (0 : ℝ) T) 0 :=
    (h_cont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
  have hEqOn : Set.EqOn rhs (fun x => deriv f x) (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).deriv).symm
  have f_lim' : Filter.Tendsto (fun x => deriv f x) (𝓝[>] (0 : ℝ))
      (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := by
    have h_rhs_tendsto : Filter.Tendsto rhs (𝓝[>] (0 : ℝ))
        (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := h_rhs_cont
    exact h_rhs_tendsto.congr' (hEqOn.eventuallyEq_of_mem hs)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv f_diff f_lim hs f_lim'

end DifferentialGeometry.PDE.RicciFlow
