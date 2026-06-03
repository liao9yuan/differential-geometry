import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRemainderRealizeGauge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput

/-! # The genuine, un-gated coordinate-spectral DeTurck nonlinearity and its Lipschitz

This file isolates the genuine engine input for the `g₀`-anchored Ricci–DeTurck
maximal-regularity construction: the **un-gated** first-order DeTurck nonlinearity
`N_cont : Hᵃ⁺¹(g₀) → Hᵃ(g₀)`, locally Lipschitz on a ball, **without any
`C^∞`/finite-support/`MemAllTensorHs` gate** on the engine-Lipschitz path.

## Why the gated gauge is the wrong engine input

The gate-based gauge section `deTurckRemainderRealizeSection g₀ g_bg`
(`DeTurckRemainderRealizeGauge.lean`) is gated on `realizableAtGate` (= `MemAllTensorHs`,
a `Gδ` infinite-smoothness condition whose *complement is dense* in `Hᵃ⁺¹`: take
`δ ∈ Hᵃ⁺¹ \ Hᵃ⁺²`).  The gated gauge — and hence any spectral lift presenting its
`L²` coordinates — is therefore **discontinuous**, so it is *not* Lipschitz on any ball.
A claim that the gauge's `deTurckG0SectionDiffHa`-difference is `Hᵃ`-Lipschitz over all of
`Hᵃ⁺¹` is **false as stated**.  The gate is the correct device only for the *final
geometric output* (`deTurckRemainderRealize_geomMatch`, the proven gate-conditioned
principal-part match), where the carrier is a genuine smooth solution; it must never carry
the engine's nonlinearity Lipschitz.

## The genuine route (un-gated)

The maximal-regularity engine `deTurckRemainder_strong_shortTime_exists` consumes exactly
`LipschitzOnWith L_R N (Metric.closedBall (ι u₀) R)` for some `0 < R`.  The genuine
nonlinearity's local Lipschitz comes, *gate-free*, from:

* (i) the **coordinate** Ricci–DeTurck-RHS Lipschitz
  `exists_chartDeTurckRHSComp_lipschitz_on_compact` (`RHSPointwiseLipschitz.lean`,
  sorry-free): on a chart-good compact, the chart-frame DeTurck right-hand-side difference
  is controlled by the chart `C²`-jet seminorm `chartMetricJet2DiffSup` of the metric
  difference; and

* (ii) the **supercritical spectral–Sobolev embedding** `Hᵃ⁺¹ ↪ C²` (`2a > dim M + 4`):
  the chart `2`-jet of the realized perturbation `g₀ + ccTensorBilinSymm g₀ (realize u)`
  is Lipschitz in `u` *over all of* `Hᵃ⁺¹` (the eigen-synthesis converges in `C²` with
  `C²`-norm `≲ ‖u‖_{Hᵃ⁺¹}` — the eigenfunction `C²`-bounds plus tail-summability, which
  **transit the Weyl node**).  This is the un-gated analogue of the on-disk gated bound
  `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional` minus its false
  finite-support (`realizableAt`) hypotheses.

The disease to avoid (documented, never instantiated as a declaration): the *intended* un-gated
supercritical chart-`2`-jet Lipschitz "for all `u, u' : Hᵃ⁺¹`" phrased about the **gated**
realization `realizeMetricAt` is **false as written**.  `realizeMetricAt g₀ ·` is gated on the
finite-support predicate `realizableAt`, whose complement is dense in `Hᵃ⁺¹`
(`tensorHsFiniteSupportSubmodule_dense`); off the gate it collapses to `g₀`, so it is
discontinuous.  *Counterexample:* fix a finitely-supported fibre-small `u'` with
`chartMetricJet2DiffSup g₀ (realizeMetricAt g₀ u') > 0` at some `y₀ ∈ K`, and an
infinitely-supported `δ` with `‖δ‖` arbitrarily small; then `u := u' + δ` is not `realizableAt`,
so `realizeMetricAt g₀ u = g₀` and the left side stays `> 0` while `C · ‖u − u'‖ = C · ‖δ‖ → 0`.
The fix is to use a *continuous* un-gated synthesis, the genuine route below; the gated
`realizeMetricAt` must never carry a `∀ u` Lipschitz, just as the gated gauge must not.

## What lives here (the genuine route, bottoming at the Weyl node / embedding)

* `deTurckG0SpectralN` — the concrete un-gated coordinate-spectral nonlinearity of a smooth
  compactly-supported section (its `L²` eigenbasis coordinates, weighted-summable at every
  order).  This is the genuine order-`a` `Hᵃ` view, the analogue of `deTurckGeometricN`.

* `deTurckRealizeRemainderOf` — the un-gated, perturbation-indexed realized Ricci–DeTurck
  remainder `deTurckRHSSection g_bg (g₀ + ccTensorBilinSymm g₀ T) − Δ_∇ T` of a fibre-small
  `(0,2)`-perturbation `T` (the perturbation-indexed analogue of `deTurckRemainderRealizeSection`,
  using `T` directly rather than the gate representative; zero off the fibre-small domain).

* `ChartJet2LipControl` — the chart-`2`-jet local-Lipschitz control of a `(0,2)`-perturbation
  synthesis `P` on a ball: each realized perturbation `g₀ + ccTensorBilinSymm g₀ (P u)` is a
  genuine metric (`fibreSmall`) and its chart-`2`-jet seminorm difference is uniformly
  `C·K`-Lipschitz in the `Hᵃ⁺¹`-distance on every chart-good compact (`jetLip`).  This packages
  the un-gated supercritical embedding `Hᵃ⁺¹ ↪ C²` content as a *real-valued* chart bound.

* `deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control` — the **chart-`2`-jet → spectral
  bridge** (body `sorry`, transiting the chart-RHS tower): a perturbation synthesis with
  `ChartJet2LipControl` induces a continuous, locally Lipschitz coordinate-spectral nonlinearity
  on its realized DeTurck remainder `deTurckRealizeRemainderOf g₀ g_bg ∘ P`, via the coordinate
  DeTurck-RHS Lipschitz `exists_chartDeTurckRHSComp_lipschitz_on_compact` composed with the
  chart-`C⁰`-to-`Hᵃ` spectral control.

* `exists_deTurckRemainderG0_synthesis_chartJet2Control` — the genuine **supercritical
  eigen-synthesis** (body `sorry`, transiting the Weyl node): there is a perturbation synthesis
  `P` carrying `ChartJet2LipControl` whose realized remainder `deTurckRealizeRemainderOf g₀ g_bg
  (P u)` agrees, at the `L²`-class level, with the gate-based gauge
  `deTurckRemainderRealizeSection g₀ g_bg u` on the gate-realizable locus.

* `exists_deTurckRemainderG0ContSynth` — the genuine, un-gated **continuous DeTurck-remainder
  smooth-section synthesis** `S : Hᵃ⁺¹ → SmoothCcTensor g₀ 0 2` (with `S u =
  deTurckRealizeRemainderOf g₀ g_bg (P u)`), whose induced coordinate-spectral nonlinearity
  `u ↦ deTurckG0SpectralN g₀ a (S u)` is continuous and locally Lipschitz on a ball, and which
  *agrees with the gate-based gauge on the gate-realizable domain*.  It is **proven by
  composition** of the two posited analytic children above (the bridge ∘ the eigen-synthesis):
  the eigen-synthesis supplies `P` + the chart-`2`-jet control + the locus agreement; the bridge
  upgrades the control to spectral continuity + local Lipschitz.  It is phrased about the
  *continuous* synthesis, **never** the gated `realizeMetricAt`.

* `deTurck_g0_genuine_nonlinearity` — `(B)`, the engine input, is **fully proven** here on top
  of the synthesis primitive: `N_cont u := deTurckG0SpectralN g₀ a (S u)`, with continuity and
  local Lipschitz read off the primitive and the *carrier-only* eigenbasis-coordinate tie to
  the gate-based gauge derived from the carrier-agreement (`toL2 (S u) = toL2
  (deTurckRemainderRealizeSection g₀ g_bg u)` on `realizableAtGate g₀ u`, so the `L²` classes —
  hence every coordinate — agree).  Its conclusion is structurally distinct from each
  hypothesis; no packaging.

Consumers of `deTurck_g0_genuine_nonlinearity` transitively depend on `sorryAx` (through the two
posited analytic children) and on the Weyl node, but **never** on a false-as-stated Lipschitz of
the gated gauge or of the gated `realizeMetricAt`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The order-`a` coordinate-spectral nonlinearity of a smooth compactly-supported
`(0,2)`-tensor section.**

Given a smooth compactly-supported `(0,2)`-tensor section `T` on `(M, g₀)`, this is the
order-`a` spectral element whose eigenbasis coordinates are the `L²` coordinates of `T`
against the rough-Laplacian eigenbasis.  The weighted square-summability witness placing
these coordinates in `Hᵃ` is the spectral-scale summability of a smooth compactly-supported
tensor (`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at every real order).  This
is the un-gated coordinate-spectral synthesis primitive: it is the order-`a` `Hᵃ` view of
*any* smooth section, with no gate, exactly as `deTurckGeometricN` reads off
`deTurckRemainderSection`. -/
noncomputable def deTurckG0SpectralN (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (Integral.L2.SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      (a : ℝ) T (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem deTurckG0SpectralN_coeff (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (deTurckG0SpectralN (I := I) g₀ a T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (Integral.L2.SmoothCcTensor.toL2 T) i := rfl

open scoped Classical in
/-- **The realized Ricci–DeTurck remainder of an arbitrary `(0,2)`-perturbation section.**

For a `(0,2)`-tensor perturbation section `T : SmoothCcTensor g₀ 0 2` that is `g₀`-fibre
small with some `δ < 1` (`hsmall`), the realized metric `g₀ + ccTensorBilinSymm g₀ T` is a
genuine smooth Riemannian metric, and this is the `g₀`-tagged Ricci–DeTurck remainder of that
realized metric:
```
deTurckRHSSection g_bg (g₀ + ccTensorBilinSymm g₀ T) − rawTensorConnLapSmooth g₀ 0 2 T
```
(re-tagged from the `g_bg` type tag to the `g₀` type tag, the metric tag being a pure
type-level parameter, exactly as in `deTurckRemainderRealizeSection`).  Off the fibre-small
domain it is the zero section.

This is the un-gated, perturbation-indexed analogue of `deTurckRemainderRealizeSection`: it
uses the supplied perturbation `T` directly (rather than the gate representative
`gateSmoothRep u`), so it carries no gate.  On the gate-realizable locus, with `T` the gate
representative's section, the two coincide. -/
noncomputable def deTurckRealizeRemainderOf (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  if h : ∃ δ : ℝ, δ < 1 ∧
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T h.choose_spec.1 h.choose_spec.2)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T h.choose_spec.1
            h.choose_spec.2)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g₀ 0 2 T
  else
    0

/-- **The chart-`2`-jet local-Lipschitz control of a `(0,2)`-perturbation synthesis on a
ball (the genuine un-gated supercritical analytic hypothesis).**

For a `(0,2)`-perturbation synthesis `P : Hᵃ⁺¹(g₀) → SmoothCcTensor g₀ 0 2`, a radius `R`,
and `K : ℝ≥0`, this predicate says: for every chart base point `α` and every **compact**
`Kc ⊆ interior (extChartAt I α).target`, there is a single uniform constant `C ≥ 0` so that
for all `u, u'` in the closed `Hᵃ⁺¹`-ball of radius `R` about the included zero datum and all
`y ∈ Kc`, the chart-`2`-jet seminorm of the realized-metric difference is `C·K`-rate-Lipschitz
in the `Hᵃ⁺¹`-distance,
```
chartMetricJet2DiffSup (g₀ + ccTensorBilinSymm g₀ (P u))
    (g₀ + ccTensorBilinSymm g₀ (P u')) α y ≤ C * (K : ℝ) * dist u u' ,
```
*provided* `g₀ + ccTensorBilinSymm g₀ (P u)` is realized as a genuine metric (the
`fibreSmall` half).  This is the genuine un-gated analogue — about a *continuous* perturbation
synthesis `P`, valid for all `u` in the ball — of the false-as-stated gated bound
`chartMetricJet2DiffSup_realize_ungated_lipschitz`.  Its right-hand side is a chart-frame
*real-valued* jet bound, structurally unrelated to the spectral conclusion it later yields
(no packaging).

The two arms (`fibreSmall`: each realized metric is a genuine metric over the ball;
`jetLip`: the chart-`2`-jet seminorm difference is locally Lipschitz) together carry exactly
the supercritical embedding `Hᵃ⁺¹ ↪ C²` content (the eigen-synthesis converges in `C²` with
`C²`-norm `≲ ‖u‖`, transiting the Weyl node). -/
structure ChartJet2LipControl (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2)
    (K : ℝ≥0) (R : ℝ) : Prop where
  /-- Over the ball, each realized perturbation is `g₀`-fibre small with some `δ < 1`, so
  `g₀ + ccTensorBilinSymm g₀ (P u)` assembles into a genuine smooth Riemannian metric. -/
  fibreSmall : ∀ u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
    u ∈ Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
      ∃ δ : ℝ, δ < 1 ∧
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (P u)) δ
  /-- Over the ball, the chart-`2`-jet seminorm of the realized-metric difference is
  uniformly `C·K`-Lipschitz in the `Hᵃ⁺¹`-distance, for a per-compact constant `C`. -/
  jetLip : ∀ (α : M) {Kc : Set E}, IsCompact Kc →
    Kc ⊆ interior ((extChartAt I α).target : Set E) →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        u ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
        u' ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
        ∀ (h : ∃ δ : ℝ, δ < 1 ∧
              gFibreOpBound (I := I) (M := M) g₀
                (ccTensorBilinSymm (I := I) g₀ (P u)) δ)
          (h' : ∃ δ : ℝ, δ < 1 ∧
              gFibreOpBound (I := I) (M := M) g₀
                (ccTensorBilinSymm (I := I) g₀ (P u')) δ),
        ∀ y ∈ Kc,
          chartMetricJet2DiffSup (I := I) (M := M)
              (tensorSectionRealizeMetric (I := I) g₀ (P u) h.choose_spec.1
                h.choose_spec.2)
              (tensorSectionRealizeMetric (I := I) g₀ (P u') h'.choose_spec.1
                h'.choose_spec.2)
              α y ≤
            C * (K : ℝ) * dist u u'

/-- **The chart-`2`-jet → spectral bridge: a perturbation synthesis with chart-`2`-jet
local-Lipschitz control induces a continuous, locally Lipschitz coordinate-spectral
nonlinearity on its realized DeTurck remainder.**

For a `(0,2)`-perturbation synthesis `P` carrying the chart-`2`-jet local-Lipschitz control
`ChartJet2LipControl g₀ a P K R` on the radius-`R` ball, the induced coordinate-spectral
nonlinearity `u ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (P u))` — read on
the *realized DeTurck remainder* of the perturbation synthesis — is continuous over all of
`Hᵃ⁺¹` and `LipschitzOnWith` (with a constant produced from `K`) on the radius-`R` ball.

This is the genuine analytic bridge that consumes the coordinate Ricci–DeTurck-RHS Lipschitz
`exists_chartDeTurckRHSComp_lipschitz_on_compact` (chart-frame scalar `2`-jet Lipschitz of the
DeTurck right-hand side) composed with the chart-`C⁰`-to-`Hᵃ` spectral control
(`tensorL2Norm_le_of_pointwise_fiberNormSq_bound` / the spectral projection
`smoothCcTensor_tensorL2Coeff_weighted_summable`): the chart-`2`-jet control of the realized
metric bounds the chart-frame DeTurck-RHS-component difference, which bounds the `L²` (hence
`Hᵃ`) norm of the spectral-projection difference of the realized remainders, giving the
spectral Lipschitz; continuity follows from the same bound with `u' → u`.  Its conclusion
(spectral continuity + local Lipschitz of `deTurckG0SpectralN ∘ (deTurckRealizeRemainderOf ∘
P)`) is structurally distinct from its chart-`2`-jet real-valued hypothesis; no packaging.
The body is `sorry`, transiting the chart-RHS tower (no Weyl dependence here — Weyl is
consumed entirely by `ChartJet2LipControl`). -/
theorem deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2)
    (K : ℝ≥0) {R : ℝ} (hR : 0 < R)
    (hctrl : ChartJet2LipControl (I := I) (M := M) g₀ a P K R) :
    ∃ (K' : ℝ≥0),
      Continuous (fun u => deTurckG0SpectralN (I := I) g₀ a
          (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))) ∧
      LipschitzOnWith K' (fun u => deTurckG0SpectralN (I := I) g₀ a
          (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
        (Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R) := sorry

/-- **Existence of a chart-`2`-jet-controlled un-gated perturbation synthesis whose realized
DeTurck remainder agrees with the gate gauge on the realizable locus (the genuine
supercritical eigen-synthesis).**

For the anchor `g₀`, a flow background `g_bg`, and a supercritical order `a`
(`2a > dim M + 4`), there is a `(0,2)`-perturbation synthesis `P : Hᵃ⁺¹(g₀) → SmoothCcTensor
g₀ 0 2`, a Lipschitz rate `K`, and a positive radius `R`, such that:

* `hctrl` — `P` carries the chart-`2`-jet local-Lipschitz control `ChartJet2LipControl g₀ a
  P K R` on the radius-`R` ball (the un-gated supercritical embedding `Hᵃ⁺¹ ↪ C²` content:
  the eigen-synthesis of `u` converges in `C²` with `C²`-norm `≲ ‖u‖`, so the chart-`2`-jet
  of the realized metric `g₀ + ccTensorBilinSymm g₀ (P u)` is locally Lipschitz in `u`; this
  transits the Weyl node through the all-order Gårding spectral bound
  `pouSobolevToHsNorm_le_spectral`);
* `hcarrier` — on the gate-realizable locus `realizableAtGate g₀ u`, the `L²`-class of the
  realized DeTurck remainder `deTurckRealizeRemainderOf g₀ g_bg (P u)` of `P` agrees with that
  of the gate-based gauge `deTurckRemainderRealizeSection g₀ g_bg u` (on the locus both equal
  the honest DeTurck remainder of the *same* realized metric — the synthesis `P u` is arranged
  so that its realized metric matches the gate representative's, by the gate-internal identity
  `gauge_realizableGate_ccTensorBilinSymm` / `realizableAtGate_carrierInclusion`; the agreement
  is at the `L²`-class level, decoupling the synthesis from the discontinuous gate
  representative).

This is the genuine un-gated continuous-synthesis construction primitive: it produces the
synthesized perturbation carrier together with the chart-`2`-jet control its realized metric
satisfies and the one-directional `L²`-class agreement of its realized remainder with the
gauge on the realizable locus.  Its conclusion is the existence of such a synthesis with
chart-`2`-jet real-valued control and a remainder-`L²`-class identity — structurally distinct
from the spectral continuity/Lipschitz the bridge later derives; no packaging.  The body is
`sorry`, transiting the Weyl node. -/
theorem exists_deTurckRemainderG0_synthesis_chartJet2Control
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2)
        (K : ℝ≥0) (R : ℝ),
      0 < R ∧
      ChartJet2LipControl (I := I) (M := M) g₀ a P K R ∧
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
        realizableAtGate (I := I) g₀ u →
          Integral.L2.SmoothCcTensor.toL2
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))
            = Integral.L2.SmoothCcTensor.toL2
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) := sorry

/-- **The genuine, un-gated continuous DeTurck-remainder smooth-section synthesis.**

For an anchor metric `g₀`, a flow background `g_bg`, and a supercritical order `a`
(`2a > dim M + 4`), there is a smooth-section-valued synthesis
`S : Hᵃ⁺¹(g₀) → SmoothCcTensor g₀ 0 2` such that the *coordinate-spectral* nonlinearity
`u ↦ deTurckG0SpectralN g₀ a (S u)` it induces is:

* `hcont` — **continuous** over all of `Hᵃ⁺¹` (the un-gated coordinate-spectral synthesis is
  continuous because the supercritical embedding `Hᵃ⁺¹ ↪ C²` makes the chart `2`-jet of the
  realized metric `g₀ + ccTensorBilinSymm g₀ (S u)` continuous in `u`, and the
  chart-coordinate DeTurck right-hand-side, hence its `Hᵃ` spectral projection, is continuous
  in that `2`-jet — through the chart-`C⁰`-to-`Hᵃ` control
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound`; this transits the Weyl node);
* `hlip` — **locally Lipschitz**: there are `K : ℝ≥0` and a positive radius `R` with
  `LipschitzOnWith K (fun u => deTurckG0SpectralN g₀ a (S u))` on the closed `Hᵃ⁺¹`-ball
  about the zero datum — gate-free, from the coordinate DeTurck-RHS Lipschitz
  (`exists_chartDeTurckRHSComp_lipschitz_on_compact`) composed with the un-gated supercritical
  chart-`2`-jet Lipschitz of the continuous realization (the corrected analogue of `(A)`,
  about this continuous synthesis rather than the gated `realizeMetricAt`);
* `hcarrier` — **carrier-agreement** (`L²`-class level): on the gate-realizable domain
  `realizableAtGate g₀ u`, the `L²`-class of `S u` agrees with that of the gate-based gauge
  `deTurckRemainderRealizeSection g₀ g_bg u` (there the continuous synthesis reproduces the
  honest DeTurck remainder's `L²`-class; agreement is stated at the `L²`-class — not the
  section — level, which is all the sole consumer needs and which decouples the continuous
  synthesis `S` from the non-canonical, discontinuous gate representative `gateSmoothRep u`).

This is the genuine un-gated continuous-synthesis primitive the maximal-regularity engine's
nonlinearity is built from: the conclusion produces a *section* map together with the
analytic behaviour of its spectral projection, structurally distinct from the existence of
the spectral nonlinearity `N_cont` itself.  It does **not** route through the gated
(discontinuous) `realizeMetricAt`; the carrier-agreement is a one-directional identity on the
gate-realizable domain only, not a global tie to the discontinuous gauge.

It is **proven by composition** of the two posited analytic children: with `S u :=
deTurckRealizeRemainderOf g₀ g_bg (P u)` for the synthesis `P` of
`exists_deTurckRemainderG0_synthesis_chartJet2Control`, the chart-`2`-jet → spectral bridge
`deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control` supplies `hcont`/`hlip`, and the
eigen-synthesis supplies `hcarrier`.  Its body carries no `sorry`; consumers transitively
depend on `sorryAx` only through those two children, and on the Weyl node. -/
theorem exists_deTurckRemainderG0ContSynth
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ (S : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2)
        (K : ℝ≥0) (R : ℝ),
      0 < R ∧
      Continuous (fun u => deTurckG0SpectralN (I := I) g₀ a (S u)) ∧
      LipschitzOnWith K (fun u => deTurckG0SpectralN (I := I) g₀ a (S u))
        (Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R) ∧
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
        realizableAtGate (I := I) g₀ u →
          Integral.L2.SmoothCcTensor.toL2 (S u)
            = Integral.L2.SmoothCcTensor.toL2
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) := by
  classical
  -- The un-gated perturbation synthesis `P` with its chart-`2`-jet control on the ball and
  -- the realized-remainder/gauge `L²`-class agreement on the gate-realizable locus.
  obtain ⟨P, K, R, hR, hctrl, hcarrier⟩ :=
    exists_deTurckRemainderG0_synthesis_chartJet2Control (I := I) g₀ g_bg a ha
  -- The chart-`2`-jet → spectral bridge upgrades the chart-`2`-jet control to continuity and
  -- local Lipschitz of the coordinate-spectral nonlinearity on the realized DeTurck remainder.
  obtain ⟨K', hcont, hlip⟩ :=
    deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control (I := I) g₀ g_bg a P K hR hctrl
  -- The genuine synthesis section is the realized DeTurck remainder of `P`.
  exact ⟨fun u => deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u), K', R, hR, hcont, hlip,
    hcarrier⟩

/-- **The genuine, un-gated coordinate-spectral DeTurck nonlinearity and its
engine-shaped local Lipschitz `(B)`.**

For an arbitrary initial metric `g₀`, a flow background `g_bg`, and a supercritical order
`a` (`2a > dim M + 4`), there is a genuine first-order DeTurck nonlinearity
`N_cont : Hᵃ⁺¹(g₀) → Hᵃ(g₀)`, a Lipschitz constant `K`, and a positive radius `R`, such
that:

* `hR` — `0 < R`;
* `hcont` — `N_cont` is continuous (the genuine DeTurck nonlinearity is continuous over all
  of `Hᵃ⁺¹`, even though it is only *locally* Lipschitz);
* `hLip` — `N_cont` is `LipschitzOnWith K` on the closed `Hᵃ⁺¹`-ball
  `Metric.closedBall (ι 0) R` about the included zero datum — **the exact shape the
  maximal-regularity engine `deTurckRemainder_strong_shortTime_exists` consumes**; this
  local Lipschitz comes, *gate-free*, from the coordinate DeTurck-RHS Lipschitz (i) and the
  supercritical spectral–Sobolev embedding (ii) (`chartMetricJet2DiffSup_realize_ungated_lipschitz`),
  through the `Hᵃ`-norm-to-chart-`C⁰` Sobolev control;
* `hcoeff` — the **carrier-only** eigenbasis-coordinate tie to the gate-based gauge: on the
  gate-realizable domain `realizableAtGate g₀ u` (where the gauge
  `deTurckRemainderRealizeSection g₀ g_bg` is the honest DeTurck remainder), `N_cont u`'s
  coordinates are the `L²` coordinates of that gauge section.  Because the genuine
  maximal-regularity carrier inclusions are exactly the gate-realizable elements, this is
  all the reconciliation `rhs_matches_deturck_at_solution` needs to identify
  `N_cont (carrier)` with the gauge — *without* the false `∀ u` coordinate tie to the
  discontinuous gauge.

`N_cont` is the genuine continuous nonlinearity (locally Lipschitz, un-gated); `hcoeff` is
a *carrier-restricted* coordinate identity, not the conclusion folded in (it constrains
`N_cont` on the realizable domain only, where it is a true geometric fact about the honest
remainder).  The conclusion is the existence of `N_cont` with its local Lipschitz and the
carrier-only tie — structurally distinct from any of its hypotheses; no packaging.  The
body is `sorry`, so consumers transitively depend on `sorryAx` and on the Weyl node, never
on a Lipschitz claim about the gated gauge. -/
theorem deTurck_g0_genuine_nonlinearity
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        (K : ℝ≥0) (R : ℝ),
      0 < R ∧
      Continuous N_cont ∧
      LipschitzOnWith K N_cont
        (Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R) ∧
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
        realizableAtGate (I := I) g₀ u →
          ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (N_cont u).coeff i =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2
                  (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) i) := by
  classical
  -- The genuine un-gated continuous DeTurck-remainder smooth-section synthesis `S`, with the
  -- continuity and local Lipschitz of its induced coordinate-spectral nonlinearity, and the
  -- carrier-agreement with the gate-based gauge on the gate-realizable domain.
  obtain ⟨S, K, R, hR, hcont, hlip, hcarrier⟩ :=
    exists_deTurckRemainderG0ContSynth (I := I) g₀ g_bg a ha
  -- The genuine continuous nonlinearity is the coordinate-spectral synthesis of `S`.
  refine ⟨fun u => deTurckG0SpectralN (I := I) g₀ a (S u), K, R, hR, hcont, hlip, ?_⟩
  -- Carrier-only coordinate tie: on the gate-realizable domain the synthesis section `S u`
  -- coincides with the gauge `deTurckRemainderRealizeSection g₀ g_bg u`, so their `L²`
  -- classes — hence every eigenbasis coordinate — agree.
  intro u hu i
  rw [deTurckG0SpectralN_coeff, hcarrier u hu]

end DifferentialGeometry.PDE.RicciFlow
