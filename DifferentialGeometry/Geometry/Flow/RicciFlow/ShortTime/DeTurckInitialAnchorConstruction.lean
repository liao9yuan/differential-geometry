import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0RealizeFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0GenuineNonlinearity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.RealizeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.SolutionC2Continuous

/-! # The `g₀`-anchored DeTurck–Ricci realize construction

This file isolates, upstream of the headline assemblers
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`,
`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`), the genuine analytic content of
the interior parabolic existence of the DeTurck–Ricci flow whose spectral
framework is anchored at the *arbitrary* initial metric `g₀` rather than at the
flow background `g_bg`.  It supplies the proof feeding
`deturck_metric_pde_interior_at_initial` (`DeTurckInitialDataExistence.lean`).

The spectral realization machinery (`tensorHs`, `ccTensorBilinSymm`,
`tensorSectionRealizeMetric`, the maximal-regularity Duhamel engine
`deTurckRemainder_strong_shortTime_exists`) is **generic in the anchor metric**.
Anchoring it at `g := g₀` with perturbation carrier starting at zero makes the
realized flow begin exactly at `g₀` (`g_DT 0 = g₀`), which is precisely what the
`g_bg`-anchored construction cannot give for an arbitrary `g₀`.

## Why the genuine bridges are posited rather than reused

The generic carrier→pointwise transport lemmas of `RealizeTransport.lean` and the
`C²`-in-time continuity assembler `deturck_solution_c2_continuous_icc0`
(`SolutionC2Continuous.lean`) both transitively import the headline
(`… → HamiltonDeTurckPullbackFlat → HamiltonDeTurckPullback → DeTurckShortTime →
DeTurckInitialDataExistence`), so they sit **downstream** of this node and cannot
be cited here without an import cycle.  Their content is therefore isolated as the
genuinely-open frontier nodes of this file, each a precise, well-formed statement
about the realized `g₀`-anchored flow:

* `deTurck_g0_realize_data` — existence of the full realize data bundle anchored at
  `g₀` (Duhamel carrier `u₂`/`T_s`, realized metric family `g_DT`, continuous
  gauge-cancelled nonlinearity `N_cont`/`repr`/`Nsec`, carrier strong-derivative,
  carrier time-continuity, fibre-small certificates, and the *decoupled*
  principal-part match `hNsec_geom` reconciling the `g₀`-realize nonlinearity with
  `deTurckRicciRHS g_bg`);
* `deTurck_g0_interior_deriv_from_data` — the interior one-sided derivative of each
  scalar component, the carrier derivative pushed through the realize evaluation
  functional and matched to `deTurckRicciRHS g_bg` at the realized solution;
* `deTurck_g0_inner_continuous_icc` — continuity of each scalar component up to
  `t = 0`;
* `deTurck_g0_rhs_right_continuous_at_zero` — right-continuity at `t = 0` of the
  DeTurck–Ricci right-hand side along the realized flow.

On top of these the assembled interior existence
`deturck_metric_pde_interior_at_initial_construction` is sorry-free glue; consumers
transitively depend on the frontier nodes' `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
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

/-- **The `g₀`-anchored DeTurck–Ricci realize data bundle (genuine analytic input).**

For an arbitrary initial metric `g₀` and a flow background `g_bg` on a closed
manifold there exist a positive time `T`, a supercritical spectral Sobolev order
`a`, a Duhamel carrier `u₂ : ℝ → Hᵃ⁺²(g₀)` with realized symmetric perturbation
`T_s : ℝ → SmoothCcTensor g₀ 0 2`, a metric family `g_DT` realized off `g₀`, and a
continuous gauge-cancelled first-order nonlinearity `N_cont` (presented through its
`L²` extraction `Nsec`/`repr`), such that:

* `2 * a > dim M + 4` (supercriticality, so the realize evaluation functional and
  expansion are well-defined);
* `g_DT 0 = g₀` (the perturbation carrier starts at zero, anchoring the flow at the
  prescribed initial metric — the whole point of realizing off `g₀`);
* `hreal` — `g_DT s` is the linear realize `g₀ + ccTensorBilinSymm (T_s s)`;
* `hN_coeff`, `hNsec_realize`, `hsmoothrepr` — the coordinate/realize identities of
  the spectral construction data (`N_cont`'s coefficients are the `L²` coordinates of
  `Nsec`; `Nsec` and `repr` have equal bilinear extraction; `u₂`'s coordinates are the
  `L²` coordinates of `T_s`);
* `hcont` — the included carrier `s ↦ ι (u₂ s)` is continuous up to `t = 0`
  (the mild solution is time-continuous);
* `hreg` — the carrier `u₂` solves the genuine spectral PDE
  `∂_t (ι u₂) = Δ_∇ u₂ + N_cont(ι u₂)` on `(0, T)`;
* `hsmall` — the realized perturbation `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small;
* `hNsec_geom` — the **decoupled** principal-part match: the `g₀`-rough-Laplacian of
  `T_s` plus the `g₀`-realize of the gauge-cancelled nonlinearity equals
  `deTurckRicciRHS g_bg (g_DT s)`.  This is the decoupled (anchor `g₀` ≠ background
  `g_bg`) analogue of `deTurckNonlinearitySpectral_principalPart_cancels`: the
  second-order part of `deTurckRicciRHS g_bg` linearised at `g₀` is the
  `g₀`-rough-Laplacian regardless of `g_bg`, which only enters the lower-order
  DeTurck field;
* `hC2_chart` — the `k ≤ 2` chart-Gram continuity up to `t = 0` that the
  `C²`-in-time realize assembler consumes.

This is the genuine, faithful analytic content of the strictly-parabolic,
smooth-quasilinear DeTurck–Ricci flow from smooth initial data, with the spectral
framework anchored at `g₀`.  It constrains only the internal carrier
`u₂`/`T_s`/`g_DT`/`N_cont`, never `g₀`/the headline.  The body is the deferred
classical parabolic-existence input; it remains `sorry`, so consumers transitively
depend on `sorryAx`. -/
theorem deTurck_g0_realize_data
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (a : ℕ),
      0 < T ∧ 2 * a > Module.finrank ℝ E + 4 ∧
      ∃ (g_DT : ℝ → SmoothRiemannianMetric I M)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
        (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        (repr Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2),
        g_DT 0 = g₀ ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i =
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2
                (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i) ∧
        (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
            (x : M) (v w : TangentSpace I x),
          ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
            ccTensorBilinSymm (I := I) g₀ (repr u) x v w) ∧
        ContinuousOn
          (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T,
          HasDerivAt
            (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
            (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
              N_cont
                (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ') ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
          ccTensorBilinSymm (I := I) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
            + ccTensorBilinSymm (I := I) g₀
                (repr (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
            = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') ∧
        (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
          ContinuousOn
            (fun q : ℝ × M => iteratedFDeriv ℝ k
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
              (extChartAt I α q.2))
            (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  classical
  set a : ℕ := Module.finrank ℝ E + 5 with ha_def
  have ha : 2 * a > Module.finrank ℝ E + 4 := by omega
  have ha2 : Module.finrank ℝ E < 2 * (a - 2) := by omega
  -- The geometric gauge-cancelled section `repr = Nsec = deTurckRemainderRealizeSection`
  -- (used *concretely*, so the carrier-only coordinate tie below unifies) together with
  -- its `rfl` realize identity and the gate-conditioned decoupled principal-part match.
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
  -- The **genuine, un-gated** continuous DeTurck nonlinearity `N_cont`, obtained *concretely*
  -- as the coordinate-spectral synthesis `u ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf
  -- g₀ g_bg (P u))` of the perturbation synthesis `P`, so that its all-order first-order
  -- operator-loss leaf is pinned to the named geometric operator rather than to a free
  -- function.  The supercritical `H^{a+2}` chart-jet control `hctrl` of `P` and the bridge to
  -- the coordinate-spectral nonlinearity supply the engine-shaped ball-continuity `hN_cont`
  -- and local Lipschitz `hLipBall`; `hcarrier` is the gate-realizable agreement of `P`'s
  -- realized remainder with the honest gate gauge `deTurckRemainderRealizeSection g₀ g_bg`.
  obtain ⟨P, K, R, Q, hR, hQ, hctrl, hall, hcarrier⟩ :=
    exists_deTurckRemainderG0_synthesis_chartJet2Control (I := I) g₀ g_bg a ha
  obtain ⟨K', hN_cont, hLipBall⟩ :=
    deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control
      (I := I) g₀ g_bg a ha P K hR hctrl
  set N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun u => deTurckG0SpectralN (I := I) g₀ a (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))
    with hN_cont_def
  -- The all-order concrete-synthesis pin of `N_cont`: every coordinate of every input is the
  -- `L²` coordinate of the concrete realized DeTurck remainder of `P` (definitional via
  -- `deTurckG0SpectralN_coeff`).  This pins `N_cont` to the named geometric operator and
  -- discharges the strengthened hypothesis of the first-order operator-loss leaf.
  have hsynth : ∀ (v : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        (N_cont v).coeff i =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P v))) i := by
    intro v i
    simp only [hN_cont_def, deTurckG0SpectralN_coeff]
  -- The first-order operator-loss of the concrete gauge-cancelled geometric nonlinearity
  -- (`deTurckGenuineN_firstOrder_operatorLoss`, proven by composition over the all-order ball
  -- control `hall` and the per-order single-section remainder estimate), pinned to the named
  -- geometric operator by the all-order concrete-synthesis identity `hsynth`.
  have hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont R :=
    deTurckGenuineN_firstOrder_operatorLoss (I := I) g₀ g_bg a ha N_cont P K hR hctrl hall hsynth
  obtain ⟨T₀, g_DT, u₂, T_s, hT₀, h0, hreal₀, hcont₀, hreg₀, hsmall₀, hsmoothrepr₀, hcanon₀, hHk,
      hcarrier_inball₀, hTs0, hduhamel₀⟩ :=
    deTurck_g0_carrier_realize_transport (I := I) g₀ a ha ha2 N_cont hR hN_cont hLipBall hloss
  -- **Shrink to a horizon on which the carrier's order-`2a` Sobolev norm stays below the
  -- selector's positive slack `Q`.**  The smooth representative `T_s` vanishes at `t = 0`
  -- (`hTs0`) and its order-`2a` norm is continuous up to `0` (`hHk a ha`), so it tends to `0`
  -- as `t → 0⁺`; since `0 < Q`, it is `≤ Q` on a closed horizon `[0, T]` about `0`.
  have hTs0z : T_s 0 = 0 := by
    apply smoothCcTensor_toL2_injective (I := I) (M := M) g₀ 0 2
    rw [hTs0, map_zero]
  have hval0 : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
      (T_s 0)‖ = 0 := by
    rw [hTs0z]
    have hz : IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
        (0 : Integral.L2.SmoothCcTensor g₀ 0 2) = 0 := by
      simp only [IntrinsicSobolev.SmoothCcTensor.toHs]
      exact UniformSpace.Completion.coe_zero
    rw [hz, norm_zero]
  have hcontN : ContinuousOn
      (fun s : ℝ => ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * a) (T_s s)‖) (Set.Icc 0 T₀) := (hHk a ha).norm
  have htend : Filter.Tendsto
      (fun s : ℝ => ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * a) (T_s s)‖) (nhdsWithin 0 (Set.Icc 0 T₀)) (nhds 0) := by
    have hcw : Filter.Tendsto
        (fun s : ℝ => ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * a) (T_s s)‖) (nhdsWithin 0 (Set.Icc 0 T₀))
        (nhds (‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * a) (T_s 0)‖)) := hcontN 0 ⟨le_rfl, hT₀.le⟩
    rwa [hval0] at hcw
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Icc 0 T₀),
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * a) (T_s s)‖ ≤ Q :=
    htend.eventually (Iic_mem_nhds hQ)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη_pos, hη⟩ := hev
  -- The `Q`-shrunk horizon on which the carrier's order-`2a` Sobolev norm stays `≤ Q`.
  set Tmid : ℝ := min T₀ (η / 2) with hTmid_def
  have hTmid_pos : 0 < Tmid := lt_min hT₀ (by linarith)
  have hTmid_le : Tmid ≤ T₀ := min_le_left _ _
  -- On `[0, Tmid)` the carrier inclusion `ι (u₂ s)` is gate-realizable.
  have hgate_pre : ∀ s ∈ Set.Ico (0 : ℝ) Tmid,
      realizableAtGate (I := I) g₀
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T₀ :=
      ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hTmid_le)⟩
    refine realizableAtGate_carrierInclusion (I := I) g₀ a u₂ T_s
      (hsmoothrepr₀ s hsIcc) ?_
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · refine ⟨0, by norm_num, ?_⟩
      intro x v w
      have hz : ccTensorBilinSymm (I := I) g₀ (T_s s) x v w = 0 := by
        have hre := hreal₀ s hsIcc x v w
        have hg0 : (g_DT s).inner x v w = g₀.inner x v w := by rw [← hs0, h0]
        rw [hg0] at hre; linarith [hre]
      rw [hz]; simp
    · exact hsmall₀ s ⟨hs0, lt_of_lt_of_le hs.2 hTmid_le⟩
  -- On `[0, Tmid)` the gate representative's order-`2a` norm is `≤ Q` (it equals `‖T_s s‖_{2a}`).
  have hQ_pre : ∀ s (hs : s ∈ Set.Ico (0 : ℝ) Tmid),
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
          (gateRepOfWitness (I := I) g₀
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (hgate_pre s hs))‖ ≤ Q := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T₀ :=
      ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hTmid_le)⟩
    rw [gateRepOfWitness, gateSmoothRep_carrierInclusion_eq (I := I) g₀ a u₂ T_s
      (hsmoothrepr₀ s hsIcc) (hgate_pre s hs)]
    exact hη (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
        exact lt_of_lt_of_le hs.2 (le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith)))) hsIcc
  -- The per-curve gauge match on this curve supplies a sub-horizon `Tleaf ≤ Tmid` on which the
  -- realized DeTurck remainder of `P (ι (u₂ s))` reproduces the gate-based gauge's `L²` class.
  obtain ⟨Tleaf, hTleaf_pos, hTleaf_le, hmatch_leaf⟩ :=
    hcarrier Tmid hTmid_pos u₂ N_cont R _
      (hduhamel₀.mono hTmid_le hTmid_pos) hgate_pre hQ_pre
  set T : ℝ := min Tmid Tleaf with hT_def
  have hT : 0 < T := lt_min hTmid_pos hTleaf_pos
  have hT_le : T ≤ T₀ := le_trans (min_le_left _ _) hTmid_le
  have hT_le_leaf : T ≤ Tleaf := min_le_right _ _
  have hIcc_sub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) T₀ := Set.Icc_subset_Icc le_rfl hT_le
  have hIco_sub : Set.Ico (0 : ℝ) T ⊆ Set.Ico (0 : ℝ) T₀ := Set.Ico_subset_Ico le_rfl hT_le
  have hIoo_sub : Set.Ioo (0 : ℝ) T ⊆ Set.Ioo (0 : ℝ) T₀ := Set.Ioo_subset_Ioo le_rfl hT_le
  -- Restrict the carrier bundle facts to the shrunk horizon `[0, T]`.
  have hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w :=
    fun s hs => hreal₀ s (hIcc_sub hs)
  have hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T) :=
    hcont₀.mono hIcc_sub
  have hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s :=
    fun s hs => hreg₀ s (hIoo_sub hs)
  have hsmall : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ' :=
    fun s hs => hsmall₀ s (hIoo_sub hs)
  have hsmoothrepr : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i :=
    fun s hs => hsmoothrepr₀ s (hIcc_sub hs)
  have hcanon : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integral.L2.SmoothCcTensor.toL2 (T_s s) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s) :=
    fun s hs => hcanon₀ s (hIcc_sub hs)
  have hcarrier_inball : ∀ s ∈ Set.Ico (0 : ℝ) T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s) ∈
        Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R :=
    fun s hs => hcarrier_inball₀ s (hIco_sub hs)
  have hHk' : ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ContinuousOn
        (fun s : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * k) (T_s s))
        (Set.Icc 0 T) := fun k hk => (hHk k hk).mono hIcc_sub
  -- The carrier's order-`2a` Sobolev norm stays `≤ Q` on the shrunk horizon `[0, T]`.
  have hQcarrier : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a) (T_s s)‖ ≤ Q := by
    intro s hs
    exact hη (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
        exact lt_of_le_of_lt (le_trans hs.2 (le_trans (min_le_left _ _) (min_le_right _ _)))
          (by linarith))
      (hIcc_sub hs)
  -- Discharge the honest `realizableAtGate` membership of the carrier inclusion on the
  -- whole closed interval: `MemAllTensorHs` from the smooth representative `T_s s`, and
  -- the `g₀`-fibre-smallness from `hsmall` on the interior and from `hreal`/`h0`
  -- (`ccTensorBilinSymm g₀ (T_s 0) = 0`) at the initial time.
  have hgate : ∀ s ∈ Set.Ico (0 : ℝ) T,
      realizableAtGate (I := I) g₀
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) := by
    intro s hs
    refine realizableAtGate_carrierInclusion (I := I) g₀ a u₂ T_s
      (hsmoothrepr s (Set.Ico_subset_Icc_self hs)) ?_
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · -- `s = 0`: the perturbation vanishes (`g_DT 0 = g₀`), so it is `0`-fibre-small.
      refine ⟨0, by norm_num, ?_⟩
      intro x v w
      have hz : ccTensorBilinSymm (I := I) g₀ (T_s s) x v w = 0 := by
        have hre := hreal s (Set.Ico_subset_Icc_self hs) x v w
        have hg0 : (g_DT s).inner x v w = g₀.inner x v w := by
          rw [← hs0, h0]
        rw [hg0] at hre
        linarith [hre]
      rw [hz]
      simp
    · -- `s ∈ (0, T)`: the interior fibre-smallness from `hsmall`.
      exact hsmall s ⟨hs0, hs.2⟩
  -- The carrier-only coordinate tie: at each carrier inclusion `ι (u₂ s)` the genuine `N_cont`'s
  -- coordinates are the `L²` coordinates of the gauge `Nsec = deTurckRemainderRealizeSection g₀
  -- g_bg`, by the per-curve gauge match `hmatch_leaf` on `[0, Tleaf) ⊇ [0, T)` composed with the
  -- all-order concrete-synthesis identity `hsynth` — *not* a global `∀ u` tie.
  have hN_coeff : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2
            (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i := by
    intro s hs i
    rw [hsynth
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) i,
      hmatch_leaf s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le_leaf⟩]
  exact ⟨T, a, hT, ha, g_DT, u₂, T_s, N_cont, repr, Nsec, h0, hreal, hN_coeff,
    hNsec_realize, hcont, hreg, hsmall, hsmoothrepr,
    hNsec_geom_univ T g_DT u₂ T_s hgate
      (fun s hs => hreal s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hsmoothrepr s (Set.Ico_subset_Icc_self hs))
      (fun s hs => hcanon s (Set.Ico_subset_Icc_self hs)),
    deTurck_g0_chartGram_continuity (I := I) g₀ a ha hT g_DT u₂ T_s N_cont
      hreal hcont hreg h0 hcanon hHk'⟩

/-- **Interior one-sided time-derivative of the realized `g₀`-anchored flow
(genuine analytic input).**

For the realized `g₀`-anchored DeTurck data (the linear realize `hreal`, the
carrier strong-derivative `hreg`, the decoupled principal-part match `hNsec_geom`,
and the spectral-coordinate identities, all supplied by `deTurck_g0_realize_data`),
each scalar component `s ↦ (g_DT s).inner x v w` is one-sidedly differentiable on
the interior `(0, T)` with derivative the DeTurck–Ricci right-hand side
`deTurckRicciRHS g_bg (g_DT t)`.

The proof (downstream of this node, hence isolated here) pushes the carrier
derivative through the realize evaluation functional `ℓ_a`
(`pointwise_deriv_through_realize`) and reconciles the carrier-scale spectral
right-hand side with `deTurckRicciRHS g_bg` at the realized solution
(the decoupled analogue of `rhs_matches_deturck_at_solution`, using `hNsec_geom`).
All hypotheses are coordinate/realize identities or the carrier derivative; none is
the conclusion.  The body is `sorry`, so consumers transitively depend on `sorryAx`. -/
theorem deTurck_g0_interior_deriv_from_data
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (repr Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2)
    (hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hN_coeff : ∀ s ∈ Set.Ico (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2
            (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g₀ (repr u) x v w)
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hsmoothrepr : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hNsec_geom : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g₀
            (repr (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t := by
  intro t ht x v w
  set u_car : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun s => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_car_def
  set u_car' : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      N_cont
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) with hu_car'_def
  obtain ⟨ℓ_a, hℓ⟩ := realize_eval_carrier_factorization (I := I) (M := M) g₀ a ha x v w
  have hfactor : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ccTensorBilinSymm (I := I) g₀ (T_s s) x v w = ℓ_a (u_car s) := by
    intro s hs
    refine (hℓ (T_s s) (u_car s) ?_).symm
    intro i
    rw [hu_car_def]
    simp only [tensorHsInclusion_coeff_apply]
    exact hsmoothrepr s (Set.Ioo_subset_Icc_self hs) i
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => u_car r) (u_car' s) (Set.Ici 0) s := by
    intro s hs
    exact (hreg s hs).hasDerivWithinAt
  have hpush := pointwise_deriv_through_realize (I := I) (M := M) g₀ a
    g_DT T_s u_car u_car' x v w ℓ_a
    (fun s hs => hreal s (Set.Ioo_subset_Icc_self hs) x v w) hfactor hderiv t ht
  have hmatch := rhs_matches_deturck_at_solution (I := I) (M := M) g₀ g_bg a u₂ ℓ_a
    g_DT T_s x v w (fun s hs => hreal s (Set.Ico_subset_Icc_self hs))
    N_cont repr Nsec hN_coeff hNsec_realize
    (fun s hs => hsmoothrepr s (Set.Ico_subset_Icc_self hs)) hℓ
    hNsec_geom t (Set.Ioo_subset_Ico_self ht)
  rw [hu_car'_def] at hpush
  rw [hmatch] at hpush
  exact hpush

/-- **Continuity up to `t = 0` of the realized `g₀`-anchored flow components
(genuine analytic input).**

For the realized `g₀`-anchored DeTurck data (the linear realize `hreal`, the
spectral-coordinate identity `hsmoothrepr`, the carrier time-continuity `hcont`,
and the `k ≤ 2` chart-Gram continuity `hC2_chart`, all supplied by
`deTurck_g0_realize_data`), each scalar component `s ↦ (g_DT s).inner x v w` is
continuous on the closed interval `[0, T]`.

The proof (downstream of this node, hence isolated here) is the `C²`-in-time realize
assembler `deturck_solution_c2_continuous_icc0` specialised to the anchor `g₀`.  The
body is `sorry`, so consumers transitively depend on `sorryAx`. -/
theorem deTurck_g0_inner_continuous_icc
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hsmoothrepr : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hC2_chart : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) :
    ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T) := by
  have hC2_pt : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T) := by
    intro α y hy i j k hk
    have hjoint := hC2_chart α i j k hk
    have hmap : ContinuousOn (fun s : ℝ => (s, y))
        (Set.Icc 0 T) := (continuous_id.prodMk continuous_const).continuousOn
    have hsub : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Icc 0 T)
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro s hs
      exact Set.mk_mem_prod hs hy
    have hcomp := hjoint.comp hmap hsub
    simpa only [Function.comp_def] using hcomp
  exact (deturck_solution_c2_continuous_icc0 (I := I) g₀ a ha g_DT
    (fun s => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) T_s hcont hreal
    hsmoothrepr hC2_pt).1

/-- **Right-continuity at `t = 0` of the DeTurck–Ricci right-hand side along the
realized `g₀`-anchored flow (genuine analytic input).**

For the realized `g₀`-anchored DeTurck flow `g_DT` (linear realize `hreal` whose
carrier `u₂` is continuous up to `0`, supplied by `deTurck_g0_realize_data`), every
scalar component `s ↦ deTurckRicciRHS g_bg (g_DT s) x v w` is continuous from the
right at `t = 0`.

This is continuity up to the initial datum of the (quasi-linear, lower-order)
DeTurck–Ricci right-hand side along the realized flow — structurally distinct from
the interior derivative.  It constrains only the internal `g_DT`, never `g₀`/the
headline.  The body is `sorry`, so consumers transitively depend on `sorryAx`. -/
theorem deTurck_g0_rhs_right_continuous_at_zero
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hcont : ContinuousOn (fun s : ℝ =>
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hsmoothrepr : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hC2_chart : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) :
    ∀ (x : M) (v w : TangentSpace I x),
      ContinuousWithinAt
        (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
        (Set.Ioi 0) 0 := by
  have hC2_pt : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T) := by
    intro α y hy i j k hk
    have hjoint := hC2_chart α i j k hk
    have hmap : ContinuousOn (fun s : ℝ => (s, y))
        (Set.Icc 0 T) := (continuous_id.prodMk continuous_const).continuousOn
    have hsub : Set.MapsTo (fun s : ℝ => (s, y)) (Set.Icc 0 T)
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) :=
      fun s hs => Set.mk_mem_prod hs hy
    simpa only [Function.comp_def] using hjoint.comp hmap hsub
  have hval : ∀ (y : M) (p q : TangentSpace I y),
      ContinuousOn (fun s : ℝ => (g_DT s).inner y p q) (Set.Icc 0 T) :=
    deTurck_g0_inner_continuous_icc (I := I) g₀ a ha g_DT u₂ T_s hcont hreal
      hsmoothrepr hC2_chart
  intro x v w
  have hric : ContinuousOn
      (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T) :=
    ricci_continuous_in_metric_time (I := I) (M := M) g_DT T x v w hval hC2_pt
  have hlie : ContinuousOn
      (fun s : ℝ => DeTurck.lieDerivMetric (I := I) (g_DT s)
        (DeTurck.deTurckVF (I := I) (g_DT s) g_bg) x v w) (Set.Icc 0 T) :=
    lieDeriv_deTurckVF_continuous_in_metric_time (I := I) (M := M) g_DT g_bg T x v w hC2_pt
  have hrhs_eq : (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
      = fun s : ℝ => (-2 : ℝ) • ricciTensor (I := I) (g_DT s) x v w +
          DeTurck.lieDerivMetric (I := I) (g_DT s)
            (DeTurck.deTurckVF (I := I) (g_DT s) g_bg) x v w := by
    funext s
    rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      lieDerivMetricClm_apply]
    rfl
  rw [hrhs_eq]
  have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, le_of_lt hT⟩
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ioi 0)
      (IsOpen.mem_nhds isOpen_Iio (show (0 : ℝ) ∈ Set.Iio T from hT))) ?_
    rintro s ⟨hs1, hs2⟩
    exact ⟨le_of_lt hs1, le_of_lt hs2⟩
  have hricW : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Ioi 0) 0 :=
    (hric 0 hIcc0).mono_of_mem_nhdsWithin hmem
  have hlieW : ContinuousWithinAt
      (fun s : ℝ => DeTurck.lieDerivMetric (I := I) (g_DT s)
        (DeTurck.deTurckVF (I := I) (g_DT s) g_bg) x v w) (Set.Ioi 0) 0 :=
    (hlie 0 hIcc0).mono_of_mem_nhdsWithin hmem
  exact (hricW.const_smul (-2 : ℝ)).add hlieW

/-- **The `g₀`-anchored DeTurck–Ricci interior parabolic existence (assembled).**

The full four-conjunct interior existence statement consumed by
`deturck_metric_pde_interior_at_initial`, assembled from the `g₀`-anchored realize
data bundle (`deTurck_g0_realize_data`) and the three derived-property frontier
nodes (`deTurck_g0_inner_continuous_icc`, `deTurck_g0_rhs_right_continuous_at_zero`,
`deTurck_g0_interior_deriv_from_data`).

This is sorry-free glue over the frontier nodes; consumers transitively depend on
their `sorryAx`. -/
theorem deturck_metric_pde_interior_at_initial_construction
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
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) := by
  obtain ⟨T, a, hT, ha, g_DT, u₂, T_s, N_cont, repr, Nsec, h0, hreal, hN_coeff,
      hNsec_realize, hcont, hreg, hsmall, hsmoothrepr, hNsec_geom,
      hC2_chart⟩ :=
    deTurck_g0_realize_data (I := I) g₀ g_bg
  refine ⟨T, hT, g_DT, h0, ?_, ?_, ?_⟩
  · exact deTurck_g0_inner_continuous_icc (I := I) g₀ a ha g_DT u₂ T_s hcont hreal
      hsmoothrepr hC2_chart
  · exact deTurck_g0_rhs_right_continuous_at_zero (I := I) g₀ g_bg hT a ha g_DT T_s u₂
      hreal hcont hsmoothrepr hC2_chart
  · exact deTurck_g0_interior_deriv_from_data (I := I) g₀ g_bg a ha g_DT u₂ T_s
      N_cont repr Nsec hreal hN_coeff hNsec_realize hreg hsmoothrepr
      hNsec_geom

end DifferentialGeometry.PDE.RicciFlow
