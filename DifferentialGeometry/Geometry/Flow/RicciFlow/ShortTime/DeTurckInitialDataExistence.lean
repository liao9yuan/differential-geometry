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
representative `T_s`, the **spectral Duhamel carrier** `u₂` and its continuous gauge-cancelled
nonlinearity `N_cont`, the linear realize identity `hreal` (`g_DT = g₀ + ccTensorBilinSymm
(T_s ·)`), the supercritical `H^{2k}` Sobolev-trace time-continuity `hHk`, the carrier
time-continuity `hcont`, the **spectral parabolic PDE** `hreg`
(`∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)`, the heat-semigroup/Duhamel defining identity that
pins `u₂`/`T_s`/`g_DT` to the genuine parabolic trajectory and rejects any non-parabolic
free family), the carrier↔perturbation coordinate identity `hcanon`, and the `k ≤ 2`
chart-Gram up-to-`0` continuity `hC2_chart`, together with the four interior-existence
conjuncts (continuity up to `0` of the components and the right-hand side, and the interior
one-sided derivative).

The single existential `g_DT` (and its carrier `u₂`) carries *both* the interior-existence
data (consumed by the short-time-existence leaf `deTurckRicci_shortTime_existence_of_closed`)
and the realize-carrier/spectral-pinning data (consumed by the interior-regularity bundle),
so the two are about the *same* flow.  This is sorry-free glue over the `g₀`-anchored carrier
realize transport `deTurck_g0_carrier_realize_transport` and the three derived
interior-existence frontier nodes; consumers transitively depend on their `sorryAx`. -/
theorem deturck_metric_pde_interior_at_initial_with_carrier
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (a : ℕ), 0 < T ∧ 2 * a > Module.finrank ℝ E + 4 ∧
      ∃ (g_DT : ℝ → SmoothRiemannianMetric I M)
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) (R : ℝ),
        g_DT 0 = g₀ ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
        (∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
          ContinuousOn
            (fun s : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
              (2 * k) (T_s s)) (Set.Icc 0 T)) ∧
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
        (∀ s ∈ Set.Icc (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) ∧
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
            (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) ∧
        DuhamelMildSolutionData (I := I) (M := M) g₀ (a : ℝ) T u₂ N_cont R
          (fun s => deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s))) := by
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
  obtain ⟨P, K, R, Q, hR, hQ, hctrl, hall, hcarrier⟩ :=
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
  have hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont R :=
    deTurckGenuineN_firstOrder_operatorLoss (I := I) g₀ g_bg a ha N_cont P K hR hctrl hall hsynth
  obtain ⟨T₀, g_DT, u₂, T_s, hT₀, h0, hreal₀, hcont₀, hreg₀, hsmall₀, hsmoothrepr₀,
      hcanon₀, hHk, hcarrier_inball₀, hTs0, hduhamel₀⟩ :=
    deTurck_g0_carrier_realize_transport (I := I) g₀ a ha ha2 N_cont hR hN_cont hLipBall hloss
  -- **Shrink to a horizon on which the carrier's order-`2a` Sobolev norm stays below the
  -- selector's positive slack `Q`** (the smooth representative vanishes at `t = 0` and its
  -- order-`2a` norm is continuous up to `0`, hence tends to `0`; `0 < Q`).
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
  have hQcarrier : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a) (T_s s)‖ ≤ Q := by
    intro s hs
    exact hη (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
        exact lt_of_le_of_lt (le_trans hs.2 (le_trans (min_le_left _ _) (min_le_right _ _)))
          (by linarith))
      (hIcc_sub hs)
  have hC2_chart := deTurck_g0_chartGram_continuity (I := I) g₀ a ha hT g_DT u₂ T_s N_cont
    hreal hcont hreg h0 hcanon hHk'
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
    -- `N_cont (ι u₂ s)`'s coordinates are the `L²` coordinates of `deTurckRealizeRemainderOf P`,
    -- whose `L²` class equals that of the gate-based gauge `Nsec (ι u₂ s)` on `[0, Tleaf) ⊇ [0, T)`
    -- by the per-curve match `hmatch_leaf`.
    rw [hsynth
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) i,
      hmatch_leaf s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le_leaf⟩]
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
  refine ⟨T, a, hT, ha, g_DT, T_s, u₂, N_cont, R, h0, hreal, hHk', hcont, hreg, hsmoothrepr,
    hC2_chart, ?_, ?_, ?_, ?_⟩
  · exact deTurck_g0_inner_continuous_icc (I := I) g₀ a ha g_DT u₂ T_s hcont hreal
      hsmoothrepr hC2_chart
  · exact deTurck_g0_rhs_right_continuous_at_zero (I := I) g₀ g_bg hT a ha g_DT T_s u₂
      hreal hcont hsmoothrepr hC2_chart
  · exact deTurck_g0_interior_deriv_from_data (I := I) g₀ g_bg a ha g_DT u₂ T_s
      N_cont repr Nsec hreal hN_coeff hNsec_realize hreg hsmoothrepr hNsec_geom
  · -- The Duhamel datum on the carrier-transport horizon `T₀`, restricted to the shrunk `T ≤ T₀`,
    -- with the forcing trajectory `N_cont ∘ (ι_{a+1} u₂)` rewritten to the concrete realized-
    -- remainder spectral path `s ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg
    -- (T_s s))` via the gate gauge reconciliation (a.e. on `[0, T]`, off the null endpoint `{T}`).
    refine DuhamelMildSolutionData.congr_gtraj ?_ (hduhamel₀.mono hT_le hT)
    -- The two trajectories agree pointwise on `Ico 0 T` (hence a.e. on `Icc 0 T`).
    have hpt : ∀ s ∈ Set.Ico (0 : ℝ) T,
        N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
          = deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s)) := by
      intro s hs
      refine tensorHs.ext (funext (fun i => ?_))
      -- `Nsec (ι u₂ s)` and `deTurckRealizeRemainderOf g₀ g_bg (T_s s)` have the same `L²` class:
      -- the gate representative of `ι u₂ s` is `T_s s`, and the realized remainder of that gate
      -- representative is the gate-based gauge `Nsec (ι u₂ s)`.
      have hgateEq : gateRepOfWitness (I := I) g₀
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (hgate s hs)
          = T_s s :=
        gateSmoothRep_carrierInclusion_eq (I := I) g₀ a u₂ T_s
          (hsmoothrepr s (Set.Ico_subset_Icc_self hs)) (hgate s hs)
      have hsecEq : Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
          = deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s) :=
        calc Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
            = deTurckRealizeRemainderOf (I := I) g₀ g_bg
                (gateRepOfWitness (I := I) g₀
                  (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (hgate s hs)) :=
              (deTurckRealizeRemainderOf_gateRepOfWitness (I := I) g₀ g_bg
                (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (hgate s hs)).symm
          _ = deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s) :=
              congrArg (deTurckRealizeRemainderOf (I := I) g₀ g_bg) hgateEq
      calc (N_cont (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))).coeff i
          = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2
                (Nsec (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))) i :=
            hN_coeff s hs i
        _ = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2
                (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s))) i := by rw [hsecEq]
        _ = (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s))).coeff i :=
            (deTurckG0SpectralN_coeff (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s s)) i).symm
    -- Upgrade the `Ico`-pointwise equality to a.e. on `Icc 0 T` (the endpoint `{T}` is null,
    -- `Ico 0 T =ᵐ Icc 0 T`, so the two restrictions coincide).
    rw [show MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)
          = MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) T) from
        MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ico_ae_eq_Icc (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := T)).symm]
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ico (0 : ℝ) T, MeasureTheory.self_mem_ae_restrict measurableSet_Ico, hpt⟩

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
