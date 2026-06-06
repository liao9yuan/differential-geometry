import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialAnchorConstruction

/-! # `g₀`-anchored DeTurck–Ricci interior parabolic existence

This file isolates the genuine analytic input the concrete DeTurck–Ricci
short-time existence leaf `deTurckRicci_shortTime_existence_of_closed`
(`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`) consumes: existence of a
short-time DeTurck–Ricci flow whose spectral framework is anchored at the
*arbitrary* initial metric `g₀` (not at the flow background `g_bg`), so that the
flow starts exactly at `g₀` and is interior-regular up to the smooth initial
datum.

The interior-existence assembler `deturck_metric_pde_interior`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`) couples the spectral
anchor to the flow background through a single metric argument, so it produces a
solution only for the diagonal case *anchor = background*. The headline needs the
decoupled case *anchor `g₀` ≠ background `g_bg`*; this file posits that decoupled
existence statement as the genuinely-open node. It lives upstream of the
interior/at-zero assemblers (which import the headline file), hence cannot cite
them.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **`g₀`-anchored DeTurck–Ricci interior parabolic existence with the realize carrier
data (the carrier re-export).**

The same interior parabolic existence as `deturck_metric_pde_interior_at_initial`, but
additionally re-exporting the realize-carrier data the interior-regularity bundle
`deturck_ricci_parabolic_interior_regularity`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`) consumes to discharge its
chart-local regularity conjuncts: the realize order `a`, the smooth perturbation
representative `T_s`, the linear realize identity `hreal` (`g_DT = g₀ + ccTensorBilinSymm
(T_s ·)`), the supercritical `H^{2k}` Sobolev-trace time-continuity `hHk`, and the `k ≤ 2`
chart-Gram up-to-`0` continuity `hC2_chart`, together with the four interior-existence
conjuncts (continuity up to `0` of the components and the right-hand side, and the interior
one-sided derivative).

The single existential `g_DT` carries *both* the interior-existence data (consumed by the
short-time-existence leaf `deTurckRicci_shortTime_existence_of_closed`) and the realize-
carrier data (consumed by the interior-regularity bundle), so the two are about the *same*
flow.  This is sorry-free glue over the `g₀`-anchored realize data bundle
`deTurck_g0_realize_data` and the three derived interior-existence frontier nodes;
consumers transitively depend on their `sorryAx`. -/
theorem deturck_metric_pde_interior_at_initial_with_carrier
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (a : ℕ), 0 < T ∧ 2 * a > Module.finrank ℝ E + 4 ∧
      ∃ (g_DT : ℝ → SmoothRiemannianMetric I M)
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        g_DT 0 = g₀ ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
        (∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
          ContinuousOn
            (fun s : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
              (2 * k) (T_s s)) (Set.Icc 0 T)) ∧
        (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
          ContinuousOn
            (fun q : ℝ × M => iteratedFDeriv ℝ k
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
              (extChartAt I α q.2))
            (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) ∧
        (∀ (x : M) (v w : TangentSpace I x),
          ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T)) ∧
        (∀ (x : M) (v w : TangentSpace I x),
          ContinuousWithinAt
            (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
            (Set.Ioi 0) 0) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
            (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) := by
  classical
  set a : ℕ := Module.finrank ℝ E + 5 with ha_def
  have ha : 2 * a > Module.finrank ℝ E + 4 := by omega
  have ha2 : Module.finrank ℝ E < 2 * (a - 2) := by omega
  set Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2 :=
    deTurckRemainderRealizeSection (I := I) g₀ g_bg with hNsec_def
  set repr : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2 :=
    deTurckRemainderRealizeSection (I := I) g₀ g_bg with hrepr_def
  have hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
      (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g₀ (repr u) x v w := fun _ _ _ _ => rfl
  have hNsec_geom_univ := deTurckRemainderRealize_geomMatch (I := I) (M := M) g₀ g_bg a
  obtain ⟨P, K, R, hR, hctrl, hall, hcarrier⟩ :=
    exists_deTurckRemainderG0_synthesis_chartJet2Control (I := I) g₀ g_bg a ha
  obtain ⟨K', hN_cont, hLipBall⟩ :=
    deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control
      (I := I) g₀ g_bg a ha P K hR hctrl
  set N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun u => deTurckG0SpectralN (I := I) g₀ a (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))
    with hN_cont_def
  have hsynth : ∀ (v : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (N_cont v).coeff i =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P v))) i := by
    intro v i
    simp only [hN_cont_def, deTurckG0SpectralN_coeff]
  have hcoeff : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
      realizableAtGate (I := I) g₀ u →
      u ∈ Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          (N_cont u).coeff i =
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) i := by
    intro u hu hball i
    rw [hsynth u i, hcarrier u ⟨hu, hball⟩]
  have hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont R :=
    deTurckGenuineN_firstOrder_operatorLoss (I := I) g₀ g_bg a ha N_cont P K hR hctrl hall hsynth
  obtain ⟨T, g_DT, u₂, T_s, hT, h0, hreal, hcont, hreg, hsmall, hsmoothrepr, hcanon, hHk,
      hcarrier_inball⟩ :=
    deTurck_g0_carrier_realize_transport (I := I) g₀ a ha ha2 N_cont hR hN_cont hLipBall hloss
  have hC2_chart := deTurck_g0_chartGram_continuity (I := I) g₀ a ha hT g_DT u₂ T_s N_cont
    hreal hcont hreg h0 hcanon hHk
  have hgate : ∀ s ∈ Set.Ico (0 : ℝ) T,
      realizableAtGate (I := I) g₀
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) := by
    intro s hs
    refine realizableAtGate_carrierInclusion (I := I) g₀ a u₂ T_s
      (hsmoothrepr s (Set.Ico_subset_Icc_self hs)) ?_
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · refine ⟨0, by norm_num, ?_⟩
      intro x v w
      have hz : ccTensorBilinSymm (I := I) g₀ (T_s s) x v w = 0 := by
        have hre := hreal s (Set.Ico_subset_Icc_self hs) x v w
        have hg0 : (g_DT s).inner x v w = g₀.inner x v w := by rw [← hs0, h0]
        rw [hg0] at hre; linarith [hre]
      rw [hz]; simp
    · exact hsmall s ⟨hs0, hs.2⟩
  have hN_coeff : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2
            (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i := by
    intro s hs i
    exact hcoeff
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (hgate s hs)
      (hcarrier_inball s hs) i
  have hNsec_geom : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g₀
            (repr (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w' :=
    hNsec_geom_univ T g_DT u₂ T_s hgate
      (fun s hs => hreal s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hsmoothrepr s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hcanon s (Set.Ico_subset_Icc_self hs))
  refine ⟨T, a, hT, ha, g_DT, T_s, h0, hreal, hHk, hC2_chart, ?_, ?_, ?_⟩
  · exact deTurck_g0_inner_continuous_icc (I := I) g₀ a ha g_DT u₂ T_s hcont hreal
      hsmoothrepr hC2_chart
  · exact deTurck_g0_rhs_right_continuous_at_zero (I := I) g₀ g_bg hT a ha g_DT T_s u₂
      hreal hcont hsmoothrepr hC2_chart
  · exact deTurck_g0_interior_deriv_from_data (I := I) g₀ g_bg a ha g_DT u₂ T_s
      N_cont repr Nsec hreal hN_coeff hNsec_realize hreg hsmoothrepr hNsec_geom

/-- **`g₀`-anchored DeTurck–Ricci interior parabolic existence (genuine analytic input).**

For an arbitrary initial metric `g₀` and a flow background `g_bg` on a closed
manifold there exist a positive time `T` and a metric family `g_DT` such that:

* `g_DT 0 = g₀` (the spectral framework is anchored at `g₀`, so the perturbation
  carrier starts at zero and the flow begins exactly at the prescribed initial
  metric — this is what the realize framework anchored at `g_bg` cannot give for
  arbitrary `g₀`);
* every scalar component `s ↦ (g_DT s).inner x v w` is continuous on `[0, T]`
  (continuity up to the initial datum);
* the DeTurck–Ricci right-hand side `s ↦ deTurckRicciRHS g_bg (g_DT s) x v w`
  is continuous from the right at `t = 0`;
* on the open interior `(0, T)` the scalar components are one-sidedly
  differentiable with derivative the DeTurck–Ricci right-hand side at `g_DT t`.

This is the genuine, faithful interior parabolic-smoothing-plus-continuity input
for the strictly-parabolic, smooth-quasilinear DeTurck–Ricci flow from smooth
initial data, with the spectral framework anchored at `g₀`. It is the open node;
the body is `sorry`, so consumers transitively depend on `sorryAx`.

It is **not** the short-time-existence conclusion: that conclusion is the
*one-sided derivative on the closed interval* `Ico 0 T` (including the endpoint
`t = 0`) packaged as `IsQuasilinearMetricParabolicSolution`. Here only the *open
interior* `Ioo 0 T` derivative is asserted; the endpoint `t = 0` is closed in the
consumer from the continuity certificates by the standard one-sided
derivative-limit argument. -/
theorem deturck_metric_pde_interior_at_initial
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      g_DT 0 = g₀ ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T)) ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousWithinAt
          (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
          (Set.Ioi 0) 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) :=
  deturck_metric_pde_interior_at_initial_construction (I := I) g₀ g_bg

end DifferentialGeometry.PDE.RicciFlow
