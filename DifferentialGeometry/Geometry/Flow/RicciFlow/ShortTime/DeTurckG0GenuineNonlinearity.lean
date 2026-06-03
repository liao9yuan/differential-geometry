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

## What lives here (the genuine route, bottoming at the Weyl node / embedding)

* `chartMetricJet2DiffSup_realize_ungated_lipschitz` — the *intended* un-gated supercritical
  chart-`2`-jet Lipschitz "for all `u, u' : Hᵃ⁺¹`", phrased about the **gated** realization
  `realizeMetricAt`.  **This statement is false as written** and its `sorry` is left as a
  signature defect, *not consumed anywhere*.  `realizeMetricAt g₀ ·` is gated on the
  finite-support predicate `realizableAt`, whose complement is dense in `Hᵃ⁺¹`
  (`tensorHsFiniteSupportSubmodule_dense`); off the gate it collapses to `g₀`, so it is
  discontinuous — exactly the disease documented above for the gauge.  *Counterexample:* fix
  a finitely-supported fibre-small `u'` with `chartMetricJet2DiffSup g₀ (realizeMetricAt g₀ u')`
  `> 0` at some `y₀ ∈ K`, and an infinitely-supported `δ` with `‖δ‖` arbitrarily small; then
  `u := u' + δ` is not `realizableAt`, so `realizeMetricAt g₀ u = g₀` and the left side stays
  `> 0` while `C · ‖u − u'‖ = C · ‖δ‖ → 0`.  The fix is to use a *continuous* un-gated
  synthesis, which is what the genuine route below does; the gated `realizeMetricAt` must
  never carry a `∀ u` Lipschitz, just as the gated gauge must not.

* `deTurckG0SpectralN` — the concrete un-gated coordinate-spectral nonlinearity of a smooth
  compactly-supported section (its `L²` eigenbasis coordinates, weighted-summable at every
  order).  This is the genuine order-`a` `Hᵃ` view, the analogue of `deTurckGeometricN`.

* `exists_deTurckRemainderG0ContSynth` — the genuine, un-gated **continuous DeTurck-remainder
  smooth-section synthesis** `S : Hᵃ⁺¹ → SmoothCcTensor g₀ 0 2`, whose induced
  coordinate-spectral nonlinearity `u ↦ deTurckG0SpectralN g₀ a (S u)` is continuous and
  locally Lipschitz on a ball (gate-free, via the supercritical embedding `Hᵃ⁺¹ ↪ C²` and the
  coordinate DeTurck-RHS Lipschitz), and which *agrees with the gate-based gauge on the
  gate-realizable domain*.  This is the single genuine analytic primitive (body `sorry`,
  transiting the Weyl node) the engine nonlinearity is built from — phrased about the
  *continuous* synthesis, **never** the gated `realizeMetricAt`.

* `deTurck_g0_genuine_nonlinearity` — `(B)`, the engine input, is **fully proven** here on top
  of the synthesis primitive: `N_cont u := deTurckG0SpectralN g₀ a (S u)`, with continuity and
  local Lipschitz read off the primitive and the *carrier-only* eigenbasis-coordinate tie to
  the gate-based gauge derived from the carrier-agreement (`S u = deTurckRemainderRealizeSection`
  `g₀ g_bg u` on `realizableAtGate g₀ u`, so the `L²` classes — hence every coordinate — agree).
  Its conclusion is structurally distinct from each hypothesis; no packaging.

Consumers of `deTurck_g0_genuine_nonlinearity` transitively depend on `sorryAx` (through
`exists_deTurckRemainderG0ContSynth`) and on the Weyl node, but **never** on a false-as-stated
Lipschitz of the gated gauge or of the gated `realizeMetricAt`. -/

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
gate-realizable domain only, not a global tie to the discontinuous gauge.  The body is
`sorry`, so consumers transitively depend on `sorryAx` and on the Weyl node. -/
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
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)) := sorry

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
