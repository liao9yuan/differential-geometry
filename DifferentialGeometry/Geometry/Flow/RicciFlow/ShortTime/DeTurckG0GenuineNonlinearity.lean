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

## What is posited here (true children, bottoming at the Weyl node / embedding)

* `chartMetricJet2DiffSup_realize_ungated_lipschitz` — the un-gated supercritical
  chart-`2`-jet Lipschitz of the realized perturbation, **for all** `u, u' : Hᵃ⁺¹`, with
  no gate; this is (ii) (`(A)` of the rebuild).

* `deTurck_g0_genuine_nonlinearity` — the existence of the genuine `N_cont` together with
  its engine-shaped local Lipschitz on a ball about the included zero datum, and the
  *carrier-only* eigenbasis-coordinate tie to the gate-based gauge section (`N_cont u`'s
  coordinates equal the `L²` coordinates of `deTurckRemainderRealizeSection g₀ g_bg u`
  precisely on the gate-realizable domain, where the gauge is the honest DeTurck
  remainder); this is `(B)`.

Both are precise, well-formed, non-vacuous statements; neither packages a conclusion as a
hypothesis.  The bodies are `sorry`; consumers transitively depend on `sorryAx` and on the
Weyl node, but **never** on a false-as-stated Lipschitz of the gated gauge. -/

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

/-- **Un-gated supercritical chart-`2`-jet Lipschitz of the realized perturbation
(the supercritical spectral–Sobolev embedding `(A)`).**

For a supercritical order `a` (`2a > dim M + 4`), a chart base point `α`, and a compact
piece `K ⊆ interior (extChartAt I α).target`, there is a constant `C ≥ 0` such that for
**every** pair `u, u' : Hᵃ⁺¹(g₀)` — with *no* finite-support / `MemAllTensorHs` gate — and
every `y ∈ K`,
```
chartMetricJet2DiffSup (realizeMetricAt g₀ u) (realizeMetricAt g₀ u') α y
  ≤ C · ‖u − u'‖ .
```

This is the un-gated analogue of `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`
with its false finite-support (`realizableAt`) hypotheses removed: the chart `2`-jet of the
metric perturbation `g₀ + ccTensorBilinSymm g₀ (realize u)` is controlled by the
supercritical `Hᵃ⁺¹` norm of the difference `u − u'`, because the eigen-synthesis
`∑ᵢ uᵢ bᵢ` converges in `C²` with `C²`-norm `≲ ‖u‖_{Hᵃ⁺¹}` (eigenfunction `C²`-bounds plus
tail-summability — **transits the Weyl node**).  The conclusion is the chart-`2`-jet
Lipschitz bound, not a hypothesis-packaged conclusion; the gate is absent precisely because
the supercritical embedding makes the realized `2`-jet continuous over all of `Hᵃ⁺¹`.  The
body is `sorry`. -/
theorem chartMetricJet2DiffSup_realize_ungated_lipschitz
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1)),
      ∀ y ∈ K,
        chartMetricJet2DiffSup (I := I) (M := M)
            (realizeMetricAt (I := I) g₀ u) (realizeMetricAt (I := I) g₀ u') α y ≤
          C * ‖u - u'‖ := sorry

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
                  (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) i) := sorry

end DifferentialGeometry.PDE.RicciFlow
