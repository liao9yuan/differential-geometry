import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0AnalyticInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0RealizeSectionLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRemainderRealizeGauge

/-! # Open analytic frontier of the `g₀`-anchored DeTurck–Ricci realize construction

This file isolates, upstream of the assembler `DeTurckInitialAnchorConstruction.lean`,
the genuinely-open analytic data and properties of the interior parabolic existence
of the DeTurck–Ricci flow whose spectral framework is anchored at the *arbitrary*
initial metric `g₀` rather than at the flow background `g_bg`.

The whole spectral realization machinery (`tensorHs`, `ccTensorBilinSymm`,
`tensorSectionRealizeMetric`, the maximal-regularity Duhamel engine
`deTurckRemainder_strong_shortTime_exists`) is **generic in the anchor metric**.
Anchoring it at `g := g₀` with perturbation carrier starting at zero makes the
realized flow begin exactly at `g₀`, which is precisely what the `g_bg`-anchored
construction cannot give for an arbitrary `g₀`.

The pieces posited here are exactly those that either (i) are the project's open
continuous-nonlinearity / resolvent-smoothing / parabolic-regularity inputs, or
(ii) live strictly downstream of the headline (the `L²`-time → pointwise Duhamel
transport and the realize evaluation/expansion tower of `RealizeTransport.lean` /
`DeTurckInteriorTimeRegularity.lean`, which transitively import the headline) and so
cannot be cited at the anchor node without an import cycle.  Each is a precise,
well-formed, non-vacuous statement about the realized `g₀`-anchored flow; none is
the bundle existential of `deTurck_g0_realize_data`, and none packages its own
conclusion as a hypothesis.

* `deTurck_g0_decoupled_principal_match` — the *geometric gauge datum*: the
  realize-based gauge-cancelled section `repr`/`Nsec` together with the *decoupled*
  principal-part match `hNsec_geom` (anchor `g₀` ≠ background `g_bg`).  The
  second-order part of `deTurckRicciRHS g_bg` linearised at `g₀` is the
  `g₀`-rough-Laplacian regardless of `g_bg`, so this `repr` reconciles the realized
  flow's spectral data with `deTurckRicciRHS g_bg`.  It is sorry-free glue over the
  fully-proven gate-conditioned match `deTurckRemainderRealize_geomMatch`.
* `deTurck_g0_carrier_realize_transport` — the `L²`-time → pointwise Duhamel
  carrier transport: driven by the **genuine, un-gated** continuous nonlinearity
  `N_cont` and its engine-shaped local Lipschitz (supplied by
  `deTurck_g0_genuine_nonlinearity`, `DeTurckG0GenuineNonlinearity.lean` — *not* the
  discontinuous gated gauge), the engine's strong solution, realized off `g₀`, yields a
  genuine pointwise carrier `u₂`/`T_s` and metric family `g_DT` with the interior
  strong derivative, time-continuity, and fibre-small certificates.
* `deTurck_g0_chartGram_continuity` — the `k ≤ 2` chart-Gram continuity of the
  realized flow (the parabolic-regularity datum).

Each body is `sorry` or (for `deTurck_g0_decoupled_principal_match`) is sorry-free glue
over a proven gate-conditioned match, so consumers transitively depend on `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
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

/-- **The geometric gauge-cancelled section and decoupled principal-part match for
the `g₀`-anchored realize flow (open analytic datum).**

For the anchor metric `g₀` and a flow background `g_bg` there is a realize-based
gauge-cancelled `L²`-tensor section family `Nsec` together with its realize
representative `repr` such that:

* `hNsec_realize` — `Nsec u`'s symmetric bilinear extraction equals that of
  `repr u` (the realize identity tying `Nsec` to the linear realization program);
* `hNsec_geom` — for *every* metric family `g_DT` realized as the linear realize off
  `g₀` (`hreal`) of a *canonically realized* carrier `u₂`/`T_s` (`hsmoothrepr`: the
  carrier coordinates are the `L²` coordinates of `T_s`; `hcanon`: `T_s s` is the
  canonical smooth representative of the carrier, i.e. its `L²` class is the
  `tensorHsToL2`-realization of `u₂ s`) **whose carrier inclusion is `realizableAtGate`**,
  the `g₀`-rough-Laplacian of `T_s s` plus the `g₀`-realize of `repr` of the carrier
  equals `deTurckRicciRHS g_bg (g_DT s)`.

`hNsec_geom` is the *decoupled* (anchor `g₀` ≠ background `g_bg`) integrated analogue
of `deTurckNonlinearitySpectral_principalPart_cancels`: the second-order part of
`deTurckRicciRHS g_bg` linearised at `g₀` is the `g₀`-rough-Laplacian *regardless* of
`g_bg`, which only enters the lower-order DeTurck field carried by the *concrete*
DeTurck gauge `repr` (the `g_bg`-background, `g₀`-retagged Ricci–DeTurck remainder
section `deTurckRHSSection g_bg (realize) − Δ_∇` of the canonical smooth
representative).  The gauge is concrete (so `hNsec_realize`/`hNsec_geom` are *true*);
the `hcanon` premise pins the carrier to its canonical smooth representative, which is
exactly what makes the realize of `repr` reconcile with `deTurckRicciRHS g_bg (g_DT s)`
via the sorry-free bridge `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`.  The
engine's nonlinearity Lipschitz is **not** carried here (the gated gauge is
discontinuous): it is supplied separately, un-gated, by `deTurck_g0_genuine_nonlinearity`
(`DeTurckG0GenuineNonlinearity.lean`).

The earlier `hrepr_small` conjunct (a uniform `g₀`-fibre-`< 1` bound on
`ccTensorBilinSymm (repr u)`) is *dropped*: it is jointly *unsatisfiable* with
`hNsec_geom`.  On the round `S²` with `g_bg = g₀`, `hNsec_geom` at the `s → 0⁺` carrier
(`g_DT s → g₀`, `Δ_∇ (T_s s) → 0`) forces `ccTensorBilinSymm (repr (carrier))` to
approach `deTurckRicciRHS g₀ g₀ = -2 Ric(g₀) = -2 g₀` (Einstein, `Ric = g₀` in dim 2),
whose `g₀`-fibre operator norm is `2 > 1`, so no `δ' < 1` bound on `repr (carrier)` can
hold.  `hrepr_small` was a vestigial blueprint hypothesis never used in any downstream
proof body (`rhs_matches_deturck_at_solution`, `deturckN_hscale_lipschitz`), so removing
it is the correct, non-leaking decomposition.

The match is an honest geometric identity — the genuinely-open *decoupled DeTurck
principal-part* datum the realize program isolates, not a hypothesis-packaged conclusion
(the gauge is constructed, the match is not a fold of any other hypothesis).

The gauge `repr = Nsec` is the *concrete* section
`deTurckRemainderRealizeSection g₀ g_bg` (`DeTurckRemainderRealizeGauge.lean`); the
realize identity `hNsec_realize` is then `rfl`, and the `hNsec_geom` conjunct is the
fully proven gate-conditioned geometric match `deTurckRemainderRealize_geomMatch`.  This
node is therefore sorry-free glue (it carries no `sorry` of its own and routes through no
false-as-stated leaf). -/
theorem deTurck_g0_decoupled_principal_match
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ repr Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2,
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
          (x : M) (v w : TangentSpace I x),
        ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
          ccTensorBilinSymm (I := I) g₀ (repr u) x v w) ∧
      (∀ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
          (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ s ∈ Set.Ico (0 : ℝ) T,
          realizableAtGate (I := I) g₀
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) →
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) →
        (∀ s ∈ Set.Ico (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) →
        (∀ s ∈ Set.Ico (0 : ℝ) T,
          Integral.L2.SmoothCcTensor.toL2 (T_s s) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) →
        ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
          ccTensorBilinSymm (I := I) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
            + ccTensorBilinSymm (I := I) g₀
                (repr (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
            = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') := by
  exact ⟨deTurckRemainderRealizeSection (I := I) g₀ g_bg,
    deTurckRemainderRealizeSection (I := I) g₀ g_bg,
    fun _ _ _ _ => rfl,
    deTurckRemainderRealize_geomMatch (I := I) (M := M) g₀ g_bg a⟩

/-- **`L²`-time → pointwise Duhamel carrier transport for the `g₀`-anchored flow
(downstream-only analytic content).**

For the anchor `g₀`, a supercritical order `a` (`2a > dim M + 4` and the engine's
`dim M < 2(a − 2)`), and the genuine nonlinearity `N_cont` (ball-continuous via
`hN_cont`) together with its **un-gated local Lipschitz** `hLipBall`
(`LipschitzOnWith K N_cont` on the radius-`R > 0` ball about the included zero datum —
the genuine coordinate-spectral route, *not* the gated gauge), the maximal-regularity
Duhamel engine `deTurckRemainder_strong_shortTime_exists` driven with initial datum `0`
produces a strong solution which, realized off `g₀`, yields a genuine *pointwise* carrier
`u₂ : ℝ → Hᵃ⁺²(g₀)`, smooth representatives `T_s : ℝ → SmoothCcTensor g₀ 0 2`, and a
metric family `g_DT`, with:

* `g_DT 0 = g₀` (the carrier starts at `0`);
* `hreal` — `g_DT s` is the linear realize `g₀ + ccTensorBilinSymm (T_s s)`;
* `hcont` — the included carrier `s ↦ ι (u₂ s)` is continuous up to `t = 0`;
* `hreg` — the carrier solves `∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` on `(0, T)`;
* `hsmall` — `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small on `(0, T)`;
* `hsmoothrepr` — `u₂ s`'s coordinates are the `L²` coordinates of `T_s s`;
* `hcanon` — `T_s s` is the canonical smooth representative of the carrier (its `L²`
  class equals the `L²` realization `tensorHsToL2` of `u₂ s`);
* `hHk` — every supercritical `H^{2k}` Sobolev norm of `T_s s` is continuous up to
  `t = 0` (the parabolic-up-to-boundary regularity, established at the driver from the
  Duhamel data; the input the chart-`C²` joint-continuity bridge consumes);
* `hTs0` — the smooth representative vanishes at the initial time
  (`toL2 (T_s 0) = 0`, since the Duhamel carrier starts at `0`).  Combined with `hHk`
  this lets a consumer transport a quantitative `H^{2k}` control of `T_s s` to a
  shrunk horizon where it lies below any prescribed positive bound.

The engine outputs an `L²`-time/`H¹`-time object and its derivative *as an
`L²`-time element*; the conversion to the pointwise carrier function with the
pointwise strong derivative is the indefinite-Bochner-integral / FTC transport of
`DeTurckInteriorTimeRegularity.lean`, which transitively imports the headline and so
is isolated here.  The conclusion is the existence of the realized carrier bundle —
distinct from the supplied Lipschitz hypothesis; no packaging.  This thinly forwards
`deturck_g0_engine_carrier_extraction`. -/
theorem deTurck_g0_carrier_realize_transport
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (ha2 : Module.finrank ℝ E < 2 * (a - 2))
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    {K : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (hN_cont : ContinuousOn N_cont
      (Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R))
    (hLipBall : LipschitzOnWith K N_cont
      (Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R))
    (hloss : FirstOrderOperatorLoss (I := I) (M := M) g₀ a N_cont R) :
    ∃ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
      0 < T ∧
      g_DT 0 = g₀ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
        (g_DT s).inner x v w
          = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) ∧
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
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integral.L2.SmoothCcTensor.toL2 (T_s s) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) ∧
      (∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
        ContinuousOn
          (fun s : ℝ => SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s s))
          (Set.Icc 0 T)) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T,
        tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s) ∈
          Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R) ∧
      Integral.L2.SmoothCcTensor.toL2 (T_s 0) = 0 ∧
      DuhamelMildSolutionData (I := I) (M := M) g₀ (a : ℝ) T u₂ N_cont R :=
  deturck_g0_engine_carrier_extraction (I := I) (M := M) g₀ a ha ha2 N_cont hR
    hN_cont hLipBall hloss
    (gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm (I := I) (M := M) g₀)

/-- **`k ≤ 2` chart-Gram continuity of the `g₀`-anchored realize flow
(parabolic-regularity datum).**

For the realized `g₀`-anchored parabolic flow `g_DT` over `[0, T]` (the linear
realize `hreal` of a carrier `u₂`/`T_s` solving the interior spectral PDE `hreg`
and time-continuous up to `0` via `hcont`, with the smooth representative `T_s`
tied to the carrier by the canonical `L²` realization `hcanon`, and every
supercritical `H^{2k}` norm of `T_s s` continuous up to `0` via `hHk`), every
iterated chart-Gram derivative of order `k ≤ 2` is jointly continuous in
`(time, point)` on `[0, T] × chartLeviCivitaGoodSet α`.

This is the genuine parabolic-regularity continuity datum that the `C²`-in-time
realize assembler consumes; it lives strictly downstream of the headline (the
`C²`-realize tower) and is isolated here as an open node about the constructed
flow.  The `H^{2k}`-continuity input `hHk` is the parabolic-up-to-boundary datum
(established at the driver from the Duhamel data and threaded through the realize
bundle, supplied here from `deTurck_g0_carrier_realize_transport`).  The conclusion
is joint continuity of chart-Gram iterated derivatives, distinct from the carrier
hypotheses; no packaging.  This is sorry-free glue forwarding to
`deturck_g0_parabolic_chartGram_C2_upto_zero`; consumers transitively depend on
`sorryAx` through that node's chart-Gram Fréchet-jet transfer leaf. -/
theorem deTurck_g0_chartGram_continuity
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hreal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w)
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hg0 : g_DT 0 = g₀)
    (hcanon : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integral.L2.SmoothCcTensor.toL2 (T_s s) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s))
    (hHk : ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ContinuousOn
        (fun s : ℝ => SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s s))
        (Set.Icc 0 T)) :
    ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) :=
  deturck_g0_parabolic_chartGram_C2_upto_zero (I := I) (M := M) g₀ a ha hT g_DT u₂ T_s
    N_cont hreal hcont hreg hg0 hcanon hHk

end DifferentialGeometry.PDE.RicciFlow
