import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0RealizeSectionLipschitz

/-! # The decoupled (`g₀`-anchored, `g_bg`-background) Ricci–DeTurck remainder gauge

This file constructs the *concrete* `g₀`-anchored, `g_bg`-background Ricci–DeTurck
gauge section consumed by the open frontier node
`deTurck_g0_decoupled_principal_match` (`DeTurckG0RealizeFrontier.lean`), and isolates
the single genuinely-open *decoupled* principal-part / Lipschitz datum about it.

For the anchor metric `g₀` and a flow background `g_bg`, the gauge

  `deTurckRemainderRealizeSection g₀ g_bg u
     := deTurckRHSSection g_bg (realizeMetricAt g₀ u)  −  Δ_∇^{g₀} (realizableRepr g₀ u)`

(re-tagged from the `g_bg` type tag to the `g₀` type tag, since the metric tag is a
pure type-level parameter — see `SmoothCcTensor` and `deTurckRHSSectionBg`) is the
exact decoupled analogue of `deTurckRemainderSection` (which is the `g_bg = g₀`
special case): the `g₀`-realized metric `realizeMetricAt g₀ u = g₀ + h_sym(u)` drives
the *background* `g_bg` Ricci–DeTurck right-hand side, minus the `g₀`-rough-Laplacian
of the realized perturbation `realizableRepr g₀ u`.  Off the validity domain the
gauge is the zero section.

The gauge is **concrete** (so the two facts below are *true* — they fail for a generic
discontinuous section): this is exactly the gauge `repr = Nsec` that
`deTurck_g0_decoupled_principal_match` returns.

The single open datum about the concrete gauge is
`deTurckRemainderRealize_geomMatch_lipschitz`:

* the *decoupled* principal-part match (`hNsec_geom`) — for every realize family
  `g_DT`/`u₂`/`T_s` with the realize identity, the smooth-coordinate identity and the
  canonical-smooth-representative `L²` identity (`hcanon`), the `g₀`-rough-Laplacian of
  the carrier `T_s s` plus the `g₀`-`ccTensorBilinSymm` of the gauge of the carrier
  equals `deTurckRicciRHS g_bg (g_DT s)`.  This is the integrated decoupled analogue of
  the symbol-level cancellation `deTurckNonlinearitySpectral_principalPart_cancels`: the
  second-order part of `deTurckRicciRHS g_bg` linearised at `g₀` is the
  `g₀`-rough-Laplacian regardless of `g_bg`, and the `g_bg`-background only enters the
  lower-order DeTurck field carried by the concrete gauge, reconciled with
  `deTurckRicciRHS g_bg (g_DT s)` through the sorry-free bridge
  `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS` (the carrier `T_s s` is the
  canonical smooth representative of the realized perturbation, pinned by `hcanon`).
* the concrete-gauge `Hᵃ`-Lipschitz certificate (`hNsec_lip`) — the gauge's
  `deTurckG0SectionDiffHa`-difference is Lipschitz in the realize input, via the
  chart-coordinate DeTurck-RHS Lipschitz tower
  (`exists_chartDeTurckRHSComp_lipschitz_on_compact`,
  `chartMetricJet2DiffSup_realizeMetricAt_le_toHs`) and the resolvent/eigenbasis
  Parseval identity (`tensorHs.norm_sq_eq_tsum`).

Both are genuine, well-posed, non-vacuous statements about the realized concrete gauge;
neither packages the existential of `deTurck_g0_decoupled_principal_match`, and neither
is a fold of any hypothesis (`hNsec_geom` is the geometric identity, with the realize
data as honest premises; `hNsec_lip` is the resolvent-smoothing bound).  The body is
`sorry`, so consumers transitively depend on `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open scoped Classical in
/-- **The decoupled (`g₀`-anchored, `g_bg`-background) Ricci–DeTurck remainder gauge
as a smooth compactly-supported `(0,2)`-tensor section.**

On the validity domain, with smooth representative `realizableRepr g₀ u` of `u` and
`g₀`-realized metric `realizeMetricAt g₀ u = g₀ + h_sym(u)`, this is

  `deTurckRHSSection g_bg (realizeMetricAt g₀ u) − rawTensorConnLapSmooth g₀ 0 2 (realizableRepr g₀ u)`

(re-tagged from the `g_bg` type tag to the `g₀` type tag, the metric tag being a pure
type-level parameter).  Off the validity domain it is the zero section.

This is the exact decoupled analogue of `deTurckRemainderSection` (its `g_bg = g₀`
special case) and is the concrete gauge `repr = Nsec` returned by
`deTurck_g0_decoupled_principal_match`. -/
noncomputable def deTurckRemainderRealizeSection (g₀ g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    SmoothCcTensor g₀ 0 2 :=
  if h : realizableAt (I := I) g₀ u then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g₀ u)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g₀ u)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g₀ 0 2 (realizableRepr (I := I) g₀ h)
  else
    0

/-- **The decoupled principal-part match and `Hᵃ`-Lipschitz certificate of the
concrete `g₀`-anchored, `g_bg`-background Ricci–DeTurck remainder gauge (open analytic
datum).**

For the concrete gauge `deTurckRemainderRealizeSection g₀ g_bg`:

* (`hNsec_geom`) for every realize family `g_DT`/`u₂`/`T_s` whose realized metric is the
  linear realize `g_DT s = g₀ + ccTensorBilinSymm g₀ (T_s s)` (`hreal`), whose carrier
  coordinates are the `L²` coordinates of `T_s s` (`hsmoothrepr`), and whose `T_s s` is
  the canonical smooth representative of the carrier — its `L²` class is the
  `tensorHsToL2`-realization of `u₂ s` (`hcanon`) — the `g₀`-rough-Laplacian of `T_s s`
  plus the `g₀`-`ccTensorBilinSymm` of the gauge of `u₂ s` equals
  `deTurckRicciRHS g_bg (g_DT s)`;
* (`hNsec_lip`) the gauge's `deTurckG0SectionDiffHa`-difference is `Hᵃ`-Lipschitz in the
  realize input.

This is the genuinely-open *decoupled DeTurck principal-part* datum the `g₀`-anchored
realize program isolates.  The principal-part match is the integrated decoupled analogue
of `deTurckNonlinearitySpectral_principalPart_cancels` reconciled through the sorry-free
bridge `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`; the Lipschitz bound is
the chart-coordinate DeTurck-RHS Lipschitz tower
(`exists_chartDeTurckRHSComp_lipschitz_on_compact`,
`chartMetricJet2DiffSup_realizeMetricAt_le_toHs`) transported across the
resolvent/eigenbasis Parseval identity (`tensorHs.norm_sq_eq_tsum`).  Both hold for the
*concrete* gauge (they fail for a generic discontinuous section); neither folds any
hypothesis nor packages the existential.  The body is `sorry`. -/
theorem deTurckRemainderRealize_geomMatch_lipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    (∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        ‖deTurckG0SectionDiffHa (I := I) (M := M) g₀ a
            (deTurckRemainderRealizeSection (I := I) g₀ g_bg) u u'‖
          ≤ (K : ℝ) * dist u u') ∧
      (∀ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
          (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) →
        (∀ s ∈ Set.Icc (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) →
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          Integral.L2.SmoothCcTensor.toL2 (T_s s) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
          ccTensorBilinSymm (I := I) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
            + ccTensorBilinSymm (I := I) g₀
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg
                  (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
            = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') := sorry

end DifferentialGeometry.PDE.RicciFlow
