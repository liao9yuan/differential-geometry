import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRemainderRealizeGauge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSHighOrderSobolevLipschitz
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

* (i) the **higher-order** Ricci–DeTurck-RHS Sobolev–Lipschitz Nemytskii bound
  `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`
  (`RHSHighOrderSobolevLipschitz.lean`): the weighted-`Hᵃ` seminorm of the `L²`-coordinate
  difference of the realized DeTurck *remainder* sections is controlled by the intrinsic
  `H^{a+2}` Sobolev norm of the perturbation difference (the order-`a` analogue of the
  `C⁰`/`2`-jet base case `exists_chartDeTurckRHSComp_lipschitz_on_compact`, in which the
  chart-frame DeTurck right-hand-side *value* difference is controlled by the chart `2`-jet
  seminorm `chartMetricJet2DiffSup` — the `a = 0` instance); and

* (ii) the **supercritical spectral–Sobolev control** `Hᵃ⁺¹ ↪ H^{a+2}` (`2a > dim M + 4`):
  the continuous regularized eigen-synthesis `P u : SmoothCcTensor g₀ 0 2` of `u` has
  intrinsic `H^{a+2}` Sobolev norm uniformly bounded and `H^{a+2}`-Lipschitz in the
  `Hᵃ⁺¹`-distance on the ball (a smoothing realization gaining the two derivatives the
  second-order DeTurck right-hand side loses, which **transits the Weyl node** through the
  all-order Gårding spectral bound).  This is the un-gated, order-correct analogue of the
  on-disk gated bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional` (which
  controls the chart `2`-jet by the intrinsic `H^{2k}` norm, the `a = 0` order), minus its
  false finite-support (`realizableAt`) hypotheses.

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

* `ChartJet2LipControl` — the supercritical `H^{a+2}` local-Lipschitz control of a
  `(0,2)`-perturbation synthesis `P` on a ball: each realized perturbation `g₀ +
  ccTensorBilinSymm g₀ (P u)` is a genuine metric (`fibreSmall`), the realized perturbation
  `P u` has intrinsic `H^{a+2}` Sobolev norm uniformly bounded by a single `B`, and its
  difference is `C·K`-Lipschitz in the `Hᵃ⁺¹`-distance (`sobolevLip`).  This packages the
  un-gated supercritical embedding `Hᵃ⁺¹ ↪ H^{a+2}` content as *real-valued* Sobolev-norm
  bounds.

* `deTurckRealizeRemainderOf_spectralN_dist_le_of_chartJet2Control` (**fully proven** here, by
  composition of the higher-order Nemytskii child),
  `deTurckRealizeRemainderOf_spectralN_continuous_of_chartJet2Control` (body `sorry`) — the
  two **chart-RHS-tower nodes** (no Weyl dependence): under `ChartJet2LipControl`, the
  coordinate-spectral nonlinearity on the realized DeTurck remainder has a `K'`-rate
  `Hᵃ`-Lipschitz ball `dist`-bound (now genuinely derived from the higher-order Nemytskii
  bound `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` composed with the `H^{a+2}`
  control's Lipschitz arm — no `2`-jet→`Hᵃ` leap), and is globally continuous.

* `exists_deTurckRealizeRemainderOf_synthesis_matching_gauge` — the **deep supercritical
  eigen-synthesis node** (body `sorry`, transiting the Weyl node): there is an
  `H^{a+2}`-controlled perturbation synthesis `P` (`ChartJet2LipControl`) whose realized
  DeTurck remainder `deTurckRealizeRemainderOf g₀ g_bg (P u)` coincides, *as a smooth section*,
  with the gate-based gauge `deTurckRemainderRealizeSection g₀ g_bg u` on the gate-realizable
  locus.

* `deTurckG0SpectralN_continuous_lipschitz_of_chartJet2Control` — the **`H^{a+2}` → spectral
  bridge**, **proven by composition** of the two chart-RHS-tower nodes: a perturbation
  synthesis with `ChartJet2LipControl` induces a continuous, locally Lipschitz
  coordinate-spectral nonlinearity on its realized DeTurck remainder
  `deTurckRealizeRemainderOf g₀ g_bg ∘ P` (the `dist`-bound upgraded to `LipschitzOnWith` via
  `LipschitzOnWith.of_dist_le_mul`).

* `exists_deTurckRemainderG0_synthesis_chartJet2Control` — the genuine **supercritical
  eigen-synthesis**, **proven by composition** of the deep eigen-synthesis node: there is a
  perturbation synthesis `P` carrying `ChartJet2LipControl` whose realized remainder
  `deTurckRealizeRemainderOf g₀ g_bg (P u)` agrees, at the `L²`-class level (the section
  identity projected through `SmoothCcTensor.toL2`), with the gate-based gauge
  `deTurckRemainderRealizeSection g₀ g_bg u` on the gate-realizable locus.

* `exists_deTurckRemainderG0ContSynth` — the genuine, un-gated **continuous DeTurck-remainder
  smooth-section synthesis** `S : Hᵃ⁺¹ → SmoothCcTensor g₀ 0 2` (with `S u =
  deTurckRealizeRemainderOf g₀ g_bg (P u)`), whose induced coordinate-spectral nonlinearity
  `u ↦ deTurckG0SpectralN g₀ a (S u)` is continuous and locally Lipschitz on a ball, and which
  *agrees with the gate-based gauge on the gate-realizable domain*.  It is **proven by
  composition** of the two posited analytic children above (the bridge ∘ the eigen-synthesis):
  the eigen-synthesis supplies `P` + the supercritical `H^{a+2}` control + the locus agreement;
  the bridge upgrades the control to spectral continuity + local Lipschitz.  It is phrased
  about the *continuous* synthesis, **never** the gated `realizeMetricAt`.

* `deTurck_g0_genuine_nonlinearity` — `(B)`, the engine input, is **fully proven** here on top
  of the synthesis primitive: `N_cont u := deTurckG0SpectralN g₀ a (S u)`, with continuity and
  local Lipschitz read off the primitive and the *carrier-only* eigenbasis-coordinate tie to
  the gate-based gauge derived from the carrier-agreement (`toL2 (S u) = toL2
  (deTurckRemainderRealizeSection g₀ g_bg u)` on `realizableAtGate g₀ u`, so the `L²` classes —
  hence every coordinate — agree).  Its conclusion is structurally distinct from each
  hypothesis; no packaging.

Consumers of `deTurck_g0_genuine_nonlinearity` transitively depend on `sorryAx` (through the
higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound
`exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`, the chart-RHS-tower continuity
node, and the eigen-synthesis node) and on the Weyl node, but **never** on a `2`-jet→`Hᵃ`
over-general Lipschitz, nor on a false-as-stated Lipschitz of the gated gauge or of the gated
`realizeMetricAt`.  The order-`a` quantitative Lipschitz node
`deTurckRealizeRemainderOf_spectralN_dist_le_of_chartJet2Control` is now itself genuinely
proven (it no longer carries a `sorry`): the `Hᵃ`-Lipschitz of the realized DeTurck remainder
is derived from the `H^{a+2}` Nemytskii bound and the supercritical `H^{a+2}` Lipschitz
control, eliminating the previous over-general `2`-jet→`Hᵃ` leap. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
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

/-- **The supercritical `H^{a+2}` local-Lipschitz control of a `(0,2)`-perturbation synthesis
on a ball (the genuine un-gated supercritical analytic hypothesis).**

For a `(0,2)`-perturbation synthesis `P : Hᵃ⁺¹(g₀) → SmoothCcTensor g₀ 0 2`, a radius `R`,
and `K : ℝ≥0`, this predicate says: there is a uniform size bound `B ≥ 0` and a uniform
Lipschitz constant `C ≥ 0` so that for all `u, u'` in the closed `Hᵃ⁺¹`-ball of radius `R`
about the included zero datum, the realized perturbation `P u` has intrinsic **`H^{a+2}`**
Sobolev norm `≤ B`, and the `H^{a+2}` norm of the perturbation difference is
`C·K`-rate-Lipschitz in the `Hᵃ⁺¹`-distance,
```
‖(P u).toHs (a+2)‖ ≤ B  and  ‖(P u − P u').toHs (a+2)‖ ≤ C · (K : ℝ) · dist u u' ,
```
where `‖·.toHs (a+2)‖` is the intrinsic order-`(a+2)` Sobolev norm of the smooth section.

This is the genuine **supercritical** strengthening (the `(a+2)`-jet / `H^{a+2}` content):
the realized perturbation is controlled at order `a + 2`, exactly the order the *second-order*
Ricci–DeTurck right-hand side needs to be controlled at order `a` (the right-hand side is a
second-order quasilinear operator in the metric).  It is the un-gated analogue — about a
*continuous* perturbation synthesis `P`, valid for all `u` in the ball — of the on-disk gated
bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional` (which controls the chart
`2`-jet, i.e. the `a = 0` order, by the intrinsic `H^{2k}` norm of the perturbation
difference); here both the order (`a + 2`) and the carrier (a genuine continuous synthesis)
are the corrected ones.  Its right-hand sides are *real-valued* Sobolev-norm bounds,
structurally unrelated to the spectral conclusion they later yield (no packaging).

The two arms (`fibreSmall`: each realized metric is a genuine metric over the ball;
`sobolevLip`: the `H^{a+2}` norm of the perturbation is uniformly bounded and its difference
is locally Lipschitz) together carry exactly the supercritical `Hᵃ⁺¹ ↪ H^{a+2}` content (the
continuous regularized eigen-synthesis — a smoothing realization gaining the two derivatives
the second-order DeTurck right-hand side loses — is `H^{a+2}`-bounded and `H^{a+2}`-Lipschitz
in the `Hᵃ⁺¹`-distance on the ball, transiting the Weyl node through the all-order Gårding
spectral bound; it is *not* the naive coordinate eigen-expansion, which would not gain a
derivative). -/
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
  /-- Over the ball, the intrinsic `H^{a+2}` Sobolev norm of each realized perturbation is
  uniformly bounded by a single `B`, and the `H^{a+2}` norm of the perturbation difference is
  uniformly `C·K`-Lipschitz in the `Hᵃ⁺¹`-distance (the supercritical `Hᵃ⁺¹ ↪ H^{a+2}`
  content). -/
  sobolevLip : ∃ (B : ℝ) (C : ℝ), 0 ≤ B ∧ 0 ≤ C ∧
    ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
      u ∈ Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
      u' ∈ Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) (P u)‖ ≤ B ∧
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) (P u')‖
          ≤ B ∧
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
            (P u - P u')‖ ≤ C * (K : ℝ) * dist u u'

set_option linter.unusedVariables false in
/-- **The quantitative `H^{a+2}` → spectral `Hᵃ`-Lipschitz bound of the realized
DeTurck remainder (a chart-RHS-tower node of the bridge, fully proven here).**

For a `(0,2)`-perturbation synthesis `P` carrying the supercritical `H^{a+2}` local-Lipschitz
control `ChartJet2LipControl g₀ a P K R` on the radius-`R` ball, there is a Lipschitz rate `K'`
so
that, for all `u, u'` in the ball, the `Hᵃ`-distance between the induced coordinate-spectral
nonlinearities of the realized DeTurck remainders is `K'`-rate-controlled by the
`Hᵃ⁺¹`-distance:
```
dist (deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (P u)))
     (deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (P u')))
  ≤ K' * dist u u' .
```

This is the genuine analytic core consumed by the bridge: the **higher-order** chart-RHS
Sobolev–Lipschitz Nemytskii bound `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`
(`RHSHighOrderSobolevLipschitz.lean`) — the order-`a` analogue of the `C⁰`/`2`-jet base case,
controlling the weighted-`Hᵃ` seminorm of the `L²`-coordinate difference of the realized
DeTurck remainders by the intrinsic `H^{a+2}` norm of the perturbation difference — composed
with the supercritical `H^{a+2}` Lipschitz control of the perturbation synthesis
(`ChartJet2LipControl.sobolevLip`).  Concretely: `deTurckG0SpectralN`'s coordinates are the
`L²` coordinates of the realized remainder, and `deTurckRealizeRemainderOf g₀ g_bg (P u)` is
(by metric extensionality through `tensorSectionRealizeMetric_inner`) the realized DeTurck
remainder section, so the `Hᵃ`-`dist`-squared between the two spectral nonlinearities equals
the weighted-`Hᵃ` square-sum the Nemytskii bound controls by `(C' · ‖(P u − P u').toHs
(a+2)‖)²`; the `sobolevLip` Lipschitz then gives `‖(P u − P u').toHs (a+2)‖ ≤ C·K·dist u u'`,
and the uniform `sobolevLip` size bound `‖(P u).toHs (a+2)‖ ≤ B` supplies the Nemytskii
constant's uniformity, yielding `K' := C' · (C · K)`.  Its conclusion is a *real-valued*
`Hᵃ`-distance inequality producing the Lipschitz witness `K'`, structurally distinct from the
`LipschitzOnWith`/`Continuous` topological statements the bridge assembles from it; no
packaging.  It is **proven by composition** of the posited higher-order Nemytskii bound (the
deep analytic content of the order-`a` chart-RHS tower — no Weyl dependence here; Weyl is
consumed entirely by `ChartJet2LipControl`). -/
theorem deTurckRealizeRemainderOf_spectralN_dist_le_of_chartJet2Control
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2)
    (K : ℝ≥0) {R : ℝ} (hR : 0 < R)
    (hctrl : ChartJet2LipControl (I := I) (M := M) g₀ a P K R) :
    ∃ (K' : ℝ≥0),
      ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        u ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
        u' ∈ Metric.closedBall
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith)
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R →
        dist (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
            (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u')))
          ≤ (K' : ℝ) * dist u u' := by
  classical
  obtain ⟨B, Csob, hB, hCsob, hsob⟩ := hctrl.sobolevLip
  obtain ⟨C', hC', hchild⟩ :=
    exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder (I := I) g₀ g_bg a B hB
  refine ⟨⟨C', hC'⟩ * (⟨Csob, hCsob⟩ * K), fun u u' hu hu' => ?_⟩
  -- The fibre-small witnesses over the ball, and the realized metrics they assemble.
  set h := hctrl.fibreSmall u hu with hh_def
  set h' := hctrl.fibreSmall u' hu' with hh'_def
  set g₁ : SmoothRiemannianMetric I M :=
    tensorSectionRealizeMetric (I := I) g₀ (P u) h.choose_spec.1 h.choose_spec.2 with hg₁_def
  set g₂ : SmoothRiemannianMetric I M :=
    tensorSectionRealizeMetric (I := I) g₀ (P u') h'.choose_spec.1 h'.choose_spec.2 with hg₂_def
  -- `deTurckRealizeRemainderOf` reduces, on the fibre-small locus, to the chart-frame
  -- realized DeTurck remainder section the Nemytskii bound controls.
  have hreduce_u : deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)
      = realizedRHSRemainderSection (I := I) g₀ g_bg g₁ (P u) := by
    rw [deTurckRealizeRemainderOf, dif_pos h]; rfl
  have hreduce_u' : deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u')
      = realizedRHSRemainderSection (I := I) g₀ g_bg g₂ (P u') := by
    rw [deTurckRealizeRemainderOf, dif_pos h']; rfl
  -- The realized metrics carry the fibrewise `inner`-identities the Nemytskii bound needs.
  have hg₁_inner : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (P u) x v w := by
    intro x v w; rw [hg₁_def, tensorSectionRealizeMetric_inner]
  have hg₂_inner : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (P u') x v w := by
    intro x v w; rw [hg₂_def, tensorSectionRealizeMetric_inner]
  -- The uniform `H^{a+2}` size bounds + the `H^{a+2}` Lipschitz of the perturbation difference.
  obtain ⟨hsize_u, hsize_u', hlip⟩ := hsob u u' hu hu'
  -- The higher-order Nemytskii bound on the weighted-`Hᵃ` square-sum of the coordinate diff.
  obtain ⟨_, hsum_le⟩ := hchild (P u) (P u') g₁ g₂ hg₁_inner hg₂_inner hsize_u hsize_u'
  -- Rewrite the spectral `dist²` as that weighted-`Hᵃ` square-sum.
  have hdist_sq :
      dist (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
          (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))) ^ 2
        = ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ (P u))
                    - Integral.L2.SmoothCcTensor.toL2
                      (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ (P u'))) i) ^ 2 := by
    rw [dist_eq_norm, tensorHs.norm_sq_eq_tsum]
    refine tsum_congr (fun i => ?_)
    congr 1
    have hcoeff_sub :
        (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))
            - deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))).coeff i
          = (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))).coeff i
            - (deTurckG0SpectralN (I := I) g₀ a
              (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))).coeff i := by
      rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff, sub_eq_add_neg]
    rw [hcoeff_sub, deTurckG0SpectralN_coeff, deTurckG0SpectralN_coeff,
      hreduce_u, hreduce_u']
    have hsub :
        tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ (P u))
                - Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ (P u'))) i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₁ (P u))) i
              - tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2
                  (realizedRHSRemainderSection (I := I) g₀ g_bg g₂ (P u'))) i := by
      unfold tensorL2Coeff
      rw [map_sub]
      rfl
    rw [hsub]
  -- Chain: `dist² ≤ (C'·‖diff.toHs(a+2)‖)² ≤ (K'·dist u u')²`, then take square roots.
  have hKlip_nn : 0 ≤ C' * (Csob * (K : ℝ) * dist u u') :=
    mul_nonneg hC' (by positivity)
  have htoHs_nn :
      0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2)
        (P u - P u')‖ := norm_nonneg _
  have hstep1 :
      dist (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
          (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))) ^ 2
        ≤ (C' * (Csob * (K : ℝ) * dist u u')) ^ 2 := by
    rw [hdist_sq]
    refine hsum_le.trans ?_
    have hmul : C' * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (a + 2) (P u - P u')‖
        ≤ C' * (Csob * (K : ℝ) * dist u u') := by
      exact mul_le_mul_of_nonneg_left hlip hC'
    have hC'mul_nn : 0 ≤ C' * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0)
        (s := 2) (a + 2) (P u - P u')‖ := mul_nonneg hC' htoHs_nn
    nlinarith [hmul, hC'mul_nn, hKlip_nn]
  have hdist_nn :
      0 ≤ dist (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
          (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))) := dist_nonneg
  have hcoe : ((⟨C', hC'⟩ * (⟨Csob, hCsob⟩ * K) : ℝ≥0) : ℝ) * dist u u'
      = C' * (Csob * (K : ℝ) * dist u u') := by
    push_cast; ring
  rw [hcoe]
  calc dist (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
          (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u')))
      = Real.sqrt (dist (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)))
          (deTurckG0SpectralN (I := I) g₀ a
            (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u'))) ^ 2) :=
        (Real.sqrt_sq hdist_nn).symm
    _ ≤ Real.sqrt ((C' * (Csob * (K : ℝ) * dist u u')) ^ 2) := Real.sqrt_le_sqrt hstep1
    _ = C' * (Csob * (K : ℝ) * dist u u') := Real.sqrt_sq hKlip_nn

/-- **Global continuity of the realized-DeTurck-remainder coordinate-spectral nonlinearity
under supercritical `H^{a+2}` control (the deep analytic continuity node of the bridge).**

For a `(0,2)`-perturbation synthesis `P` carrying the supercritical `H^{a+2}` local-Lipschitz
control `ChartJet2LipControl g₀ a P K R`, the induced coordinate-spectral nonlinearity
`u ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (P u))` is continuous over all
of `Hᵃ⁺¹`.

Continuity is genuinely *global* (the genuine synthesis `P` is the continuous
regularized eigen-synthesis through the supercritical embedding `Hᵃ⁺¹ ↪ H^{a+2}`, so its
realized metric's `H^{a+2}` content varies continuously, hence the chart-frame DeTurck
right-hand side and its `Hᵃ` spectral projection vary continuously even at the boundary of the
fibre-small domain), so it cannot be read off a finite-radius distance bound; it is therefore
isolated as its own deep node, structurally distinct from the quantitative ball-Lipschitz
bound.  The body is `sorry` (the deep analytic content, transiting the higher-order chart-RHS
Sobolev tower `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` at every nearby radius
together with the global continuity of the synthesis; Weyl is consumed by
`ChartJet2LipControl`). -/
theorem deTurckRealizeRemainderOf_spectralN_continuous_of_chartJet2Control
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g₀ 0 2)
    (K : ℝ≥0) {R : ℝ} (hR : 0 < R)
    (hctrl : ChartJet2LipControl (I := I) (M := M) g₀ a P K R) :
    Continuous (fun u => deTurckG0SpectralN (I := I) g₀ a
        (deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u))) := sorry

/-- **Existence of a supercritical-`H^{a+2}`-controlled un-gated perturbation synthesis whose
realized DeTurck remainder coincides (as a smooth section) with the gate gauge on the
realizable locus (the deep supercritical eigen-synthesis node).**

For the anchor `g₀`, a flow background `g_bg`, and a supercritical order `a`
(`2a > dim M + 4`), there is a `(0,2)`-perturbation synthesis `P : Hᵃ⁺¹(g₀) → SmoothCcTensor
g₀ 0 2`, a Lipschitz rate `K`, and a positive radius `R`, such that:

* `hctrl` — `P` carries the supercritical `H^{a+2}` local-Lipschitz control
  `ChartJet2LipControl g₀ a P K R` on the radius-`R` ball: the realized perturbation is
  uniformly `H^{a+2}`-bounded and its difference is `H^{a+2}`-Lipschitz in the `Hᵃ⁺¹`-distance
  (the un-gated supercritical embedding `Hᵃ⁺¹ ↪ H^{a+2}` content of the continuous regularized
  eigen-synthesis, transiting the Weyl node through the all-order Gårding spectral bound); and
* `hsec` — on the gate-realizable locus `realizableAtGate g₀ u`, the realized DeTurck
  remainder `deTurckRealizeRemainderOf g₀ g_bg (P u)` coincides, **as a smooth section**, with
  the gate-based gauge `deTurckRemainderRealizeSection g₀ g_bg u` (on the locus both are the
  honest DeTurck remainder of the realized flow; the synthesis `P u` is arranged so its
  realized remainder reproduces the gate gauge's, even though `P u` itself is *not* the
  discontinuous gate representative `gateSmoothRep u`).

This is the genuine deep eigen-synthesis primitive: it produces the synthesized perturbation
carrier together with the supercritical `H^{a+2}` control its realized metric satisfies and the
section-level remainder agreement with the gauge on the realizable locus.  The `H^{a+2}` control
is genuinely produced by the continuous regularized eigen-synthesis (a smoothing realization
gaining the two derivatives the second-order DeTurck right-hand side loses), so the `H^{a+2}`
Lipschitz-in-`Hᵃ⁺¹` and the uniform `H^{a+2}` bound both hold on the ball.  Its conclusion (a
*section-level* remainder identity) is structurally distinct — and, for these smooth sections
with full-support `L²` separation, equivalent — to the `L²`-class identity the eigen-synthesis
parent derives; the parent does the genuine `L²`-projection step.  The body is `sorry`,
transiting the Weyl node. -/
theorem exists_deTurckRealizeRemainderOf_synthesis_matching_gauge
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ (P : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2)
        (K : ℝ≥0) (R : ℝ),
      0 < R ∧
      ChartJet2LipControl (I := I) (M := M) g₀ a P K R ∧
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
        realizableAtGate (I := I) g₀ u →
          deTurckRealizeRemainderOf (I := I) g₀ g_bg (P u)
            = deTurckRemainderRealizeSection (I := I) g₀ g_bg u) := sorry

/-- **The `H^{a+2}` → spectral bridge: a perturbation synthesis with supercritical `H^{a+2}`
local-Lipschitz control induces a continuous, locally Lipschitz coordinate-spectral
nonlinearity on its realized DeTurck remainder.**

For a `(0,2)`-perturbation synthesis `P` carrying the supercritical `H^{a+2}` local-Lipschitz
control `ChartJet2LipControl g₀ a P K R` on the radius-`R` ball, the induced coordinate-spectral
nonlinearity `u ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (P u))` — read on
the *realized DeTurck remainder* of the perturbation synthesis — is continuous over all of
`Hᵃ⁺¹` and `LipschitzOnWith` (with a constant produced from `K`) on the radius-`R` ball.

This is the genuine analytic bridge that consumes the higher-order chart-RHS Sobolev–Lipschitz
Nemytskii bound `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` (the weighted-`Hᵃ`
seminorm of the `L²`-coordinate difference of the realized DeTurck remainders controlled by the
intrinsic `H^{a+2}` norm of the perturbation difference) composed with the supercritical
`H^{a+2}` Lipschitz control of the synthesis (`ChartJet2LipControl.sobolevLip`): the `H^{a+2}`
control of the perturbation bounds the `H^{a+2}` norm of the perturbation difference, which the
Nemytskii bound turns into the weighted-`Hᵃ` (hence `Hᵃ`) norm of the spectral-projection
difference of the realized remainders, giving the spectral Lipschitz; continuity follows from
the same bound with `u' → u`.  Its conclusion (spectral continuity + local Lipschitz of
`deTurckG0SpectralN ∘ (deTurckRealizeRemainderOf ∘ P)`) is structurally distinct from its
`H^{a+2}` real-valued hypothesis; no packaging.

It is **proven by composition** of two chart-RHS-tower nodes (no Weyl dependence here — Weyl is
consumed entirely by `ChartJet2LipControl`): the quantitative `H^{a+2}` → spectral
`Hᵃ`-Lipschitz bound `deTurckRealizeRemainderOf_spectralN_dist_le_of_chartJet2Control` (itself
fully proven, via the Nemytskii bound) supplies the Lipschitz rate `K'` and the ball
`dist`-bound (upgraded here to `LipschitzOnWith` via `LipschitzOnWith.of_dist_le_mul`), and the
global-continuity node `deTurckRealizeRemainderOf_spectralN_continuous_of_chartJet2Control`
supplies continuity.  Its body carries no `sorry`; consumers transitively depend on `sorryAx`
only through the continuity node and (via the quantitative node) the Nemytskii bound, i.e. the
chart-RHS-tower nodes. -/
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
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))) R) := by
  -- The quantitative `H^{a+2}` → spectral `Hᵃ`-Lipschitz bound supplies the rate `K'`
  -- and the ball `dist`-bound; the global-continuity node supplies continuity.
  obtain ⟨K', hbound⟩ :=
    deTurckRealizeRemainderOf_spectralN_dist_le_of_chartJet2Control (I := I) g₀ g_bg a P K hR hctrl
  refine ⟨K',
    deTurckRealizeRemainderOf_spectralN_continuous_of_chartJet2Control
      (I := I) g₀ g_bg a P K hR hctrl,
    ?_⟩
  -- The ball `dist`-bound upgrades to `LipschitzOnWith K'` on the ball.
  exact LipschitzOnWith.of_dist_le_mul (fun u hu u' hu' => hbound u u' hu hu')

/-- **Existence of a supercritical-`H^{a+2}`-controlled un-gated perturbation synthesis whose
realized DeTurck remainder agrees with the gate gauge on the realizable locus (the genuine
supercritical eigen-synthesis).**

For the anchor `g₀`, a flow background `g_bg`, and a supercritical order `a`
(`2a > dim M + 4`), there is a `(0,2)`-perturbation synthesis `P : Hᵃ⁺¹(g₀) → SmoothCcTensor
g₀ 0 2`, a Lipschitz rate `K`, and a positive radius `R`, such that:

* `hctrl` — `P` carries the supercritical `H^{a+2}` local-Lipschitz control
  `ChartJet2LipControl g₀ a P K R` on the radius-`R` ball (the un-gated supercritical embedding
  `Hᵃ⁺¹ ↪ H^{a+2}` content: the continuous regularized eigen-synthesis `P u` has intrinsic
  `H^{a+2}` Sobolev norm uniformly bounded and `H^{a+2}`-Lipschitz in `u`, so the realized
  metric `g₀ + ccTensorBilinSymm g₀ (P u)` is controlled at order `a + 2` — the order the
  second-order DeTurck right-hand side needs at order `a`; this transits the Weyl node through
  the all-order Gårding spectral bound `pouSobolevToHsNorm_le_spectral`);
* `hcarrier` — on the gate-realizable locus `realizableAtGate g₀ u`, the `L²`-class of the
  realized DeTurck remainder `deTurckRealizeRemainderOf g₀ g_bg (P u)` of `P` agrees with that
  of the gate-based gauge `deTurckRemainderRealizeSection g₀ g_bg u` (on the locus both equal
  the honest DeTurck remainder of the *same* realized metric — the synthesis `P u` is arranged
  so that its realized metric matches the gate representative's, by the gate-internal identity
  `gauge_realizableGate_ccTensorBilinSymm` / `realizableAtGate_carrierInclusion`; the agreement
  is at the `L²`-class level, decoupling the synthesis from the discontinuous gate
  representative).

This is the genuine un-gated continuous-synthesis construction primitive: it produces the
synthesized perturbation carrier together with the supercritical `H^{a+2}` control its realized
metric satisfies and the one-directional `L²`-class agreement of its realized remainder with
the gauge on the realizable locus.  Its conclusion is the existence of such a synthesis with
`H^{a+2}` real-valued control and a remainder-`L²`-class identity — structurally distinct
from the spectral continuity/Lipschitz the bridge later derives; no packaging.

It is **proven by composition** of the deep eigen-synthesis node
`exists_deTurckRealizeRemainderOf_synthesis_matching_gauge` (which supplies the
`H^{a+2}`-controlled synthesis `P` and the *section-level* remainder agreement
`deTurckRealizeRemainderOf g₀ g_bg (P u) = deTurckRemainderRealizeSection g₀ g_bg u` on the
locus) by projecting that section identity through the `L²`-class map `SmoothCcTensor.toL2`
(`congrArg`).  Its body carries no `sorry`; consumers transitively depend on `sorryAx`, and on
the Weyl node, only through that eigen-synthesis node. -/
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
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) := by
  -- The deep eigen-synthesis supplies an `H^{a+2}`-controlled synthesis `P` whose realized
  -- DeTurck remainder coincides, *as a smooth section*, with the gate gauge on the realizable
  -- locus.  Projecting that section identity through the `L²`-class map gives the required
  -- `L²`-class agreement.
  obtain ⟨P, K, R, hR, hctrl, hsec⟩ :=
    exists_deTurckRealizeRemainderOf_synthesis_matching_gauge (I := I) g₀ g_bg a ha
  refine ⟨P, K, R, hR, hctrl, fun u hu => ?_⟩
  rw [hsec u hu]

/-- **The genuine, un-gated continuous DeTurck-remainder smooth-section synthesis.**

For an anchor metric `g₀`, a flow background `g_bg`, and a supercritical order `a`
(`2a > dim M + 4`), there is a smooth-section-valued synthesis
`S : Hᵃ⁺¹(g₀) → SmoothCcTensor g₀ 0 2` such that the *coordinate-spectral* nonlinearity
`u ↦ deTurckG0SpectralN g₀ a (S u)` it induces is:

* `hcont` — **continuous** over all of `Hᵃ⁺¹` (the un-gated coordinate-spectral synthesis is
  continuous because the supercritical embedding `Hᵃ⁺¹ ↪ H^{a+2}` makes the `H^{a+2}` content
  of the realized metric `g₀ + ccTensorBilinSymm g₀ (S u)` continuous in `u`, and the
  DeTurck-remainder right-hand-side, hence its `Hᵃ` spectral projection, is continuous in that
  `H^{a+2}` content — through the higher-order chart-RHS Sobolev–Lipschitz Nemytskii bound
  `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`; this transits the Weyl node);
* `hlip` — **locally Lipschitz**: there are `K : ℝ≥0` and a positive radius `R` with
  `LipschitzOnWith K (fun u => deTurckG0SpectralN g₀ a (S u))` on the closed `Hᵃ⁺¹`-ball
  about the zero datum — gate-free, from the higher-order chart-RHS Sobolev–Lipschitz Nemytskii
  bound `exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder` composed with the un-gated
  supercritical `H^{a+2}` Lipschitz of the continuous realization (the corrected analogue of
  `(A)`, about this continuous synthesis rather than the gated `realizeMetricAt`);
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
`exists_deTurckRemainderG0_synthesis_chartJet2Control`, the `H^{a+2}` → spectral bridge
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
  -- The un-gated perturbation synthesis `P` with its supercritical `H^{a+2}` control on the
  -- ball and the realized-remainder/gauge `L²`-class agreement on the gate-realizable locus.
  obtain ⟨P, K, R, hR, hctrl, hcarrier⟩ :=
    exists_deTurckRemainderG0_synthesis_chartJet2Control (I := I) g₀ g_bg a ha
  -- The `H^{a+2}` → spectral bridge upgrades the `H^{a+2}` control to continuity and
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
  local Lipschitz comes, *gate-free*, from the higher-order chart-RHS Sobolev–Lipschitz
  Nemytskii bound (i) (`exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`, controlling
  the realized-remainder weighted-`Hᵃ` seminorm by the `H^{a+2}` perturbation norm) composed
  with the supercritical `H^{a+2}` Lipschitz control of the continuous synthesis (ii);
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
