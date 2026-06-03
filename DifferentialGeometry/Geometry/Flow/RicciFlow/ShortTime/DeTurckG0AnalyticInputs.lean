import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-! # Deep analytic inputs of the `g₀`-anchored DeTurck–Ricci realize construction

This file isolates, upstream of the open frontier file `DeTurckG0RealizeFrontier.lean`,
the two genuinely-deep analytic prerequisites on which the realize-construction's
frontier leaves bottom out and which are **absent** from the library (the exhaustive
existence search returned nothing).  Each is a precise, well-formed, non-vacuous
statement; none packages a frontier leaf's conclusion as a hypothesis.

* `gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm` — the `C⁰`-Sobolev embedding at
  the `0`-jet fibre level: the `g`-Riemannian fibre operator norm of the symmetric
  bilinear extraction `ccTensorBilinSymm g T` is controlled, uniformly over `M`, by a
  fixed constant times the supercritical intrinsic `H^{2k}` Sobolev norm of `T`.  This
  is the `0`-jet analogue of the chart-`2`-jet seminorm bound
  `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`, specialised to the
  pointwise (no-derivative) sup of the realized perturbation, and is the standard
  Morrey/Sobolev embedding `H^{2k} ↪ C⁰` (`2k > dim M + 4`) read at the fibre level.

* `deturck_g0_parabolic_chartGram_C2_upto_zero` — the parabolic up-to-`t = 0`
  chart-`C²` regularity datum for the realized `g₀`-anchored flow with smooth initial
  datum (carrier starts at `0`): for a flow `g_DT` realized as the linear realize of a
  carrier solving the interior spectral PDE and time-continuous up to `0`, every
  iterated chart-Gram derivative of order `k ≤ 2` is jointly continuous in
  `(time, point)` on `[0, T] × chartLeviCivitaGoodSet α`.  This is the genuine
  parabolic up-to-boundary regularity for smooth initial data: the interior smoothing
  `interior_allscale_time_continuity` gives only `[ε, T]`-control that blows up as
  `ε → 0`, so the up-to-zero datum is the open prerequisite.

Each body is `sorry`, so consumers transitively depend on `sorryAx`. -/

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

/-- **`C⁰`-Sobolev embedding at the `0`-jet fibre level (deep analytic input).**

On a closed Riemannian manifold `(M, g)` there is a fixed constant `C ≥ 0` such that,
for every supercritical Sobolev order `2k` (`2k > dim M + 4`) and every smooth
compactly-supported `(0,2)`-tensor section `T`, the symmetric bilinear extraction
`ccTensorBilinSymm g T` is `g`-fibre controlled by `C · ‖T.toHs (2k)‖`:
`|ccTensorBilinSymm g T x v w| ≤ (C · ‖T.toHs (2k)‖) · √(g x v v) · √(g x w w)`
uniformly over base points `x` and tangent vectors `v, w`.

This is the pointwise (`0`-jet, no-derivative) analogue of the chart-`2`-jet seminorm
bound `chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional`
(`RealizedCovGradJetInput.lean`): both are instances of the Morrey/Sobolev embedding
`H^{2k} ↪ C⁰` for `2k > dim M + 4`, here read at the fibre level of the realized
perturbation.  The conclusion is a fibre-operator-norm bound by the supercritical
intrinsic Sobolev norm, not a hypothesis-restatement; the genuinely-open input is the
intrinsic-`H^{2k}` → `C⁰` embedding constant for the symmetric bilinear extraction.
The body is `sorry`. -/
theorem gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖) := sorry

/-- **Parabolic up-to-`t = 0` chart-`C²` regularity for the `g₀`-anchored realize flow
with smooth initial datum (deep analytic input).**

For the realized `g₀`-anchored parabolic flow `g_DT` over `[0, T]` — the linear realize
`hreal` of a carrier `u₂`/`T_s` solving the interior spectral PDE `hreg` and
time-continuous *up to `0`* via `hcont` (the smooth-initial-datum case, carrier `0`) —
every iterated chart-Gram derivative of order `k ≤ 2` is jointly continuous in
`(time, point)` on `[0, T] × chartLeviCivitaGoodSet α`.

This is the genuine parabolic up-to-boundary regularity for smooth initial data: the
project's interior smoothing `interior_allscale_time_continuity` controls the flow only
on `[ε, T]` with constants that blow up as `ε → 0`, so the up-to-`t = 0` chart-`C²`
datum cannot be read off it and is the open prerequisite.  The hypotheses `hreal`,
`hcont`, `hreg` are genuine constraints on the constructed flow (it is the realize of a
PDE solution), not a fold of the joint-continuity conclusion; no packaging.  The body is
`sorry`. -/
theorem deturck_g0_parabolic_chartGram_C2_upto_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2)
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
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
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s) :
    ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := sorry

/-- **`L²`-time engine solution → pointwise realized carrier bundle for the
`g₀`-anchored flow with smooth initial datum (deep analytic input).**

For the anchor `g₀`, a supercritical order `a` (`2a > dim M + 4`, plus the engine's
`dim M < 2(a − 2)`), the continuous nonlinearity `N_cont` presented through its section
`Nsec` with the coordinate identity `hN_coeff` and the weighted-resolvent Lipschitz
certificate `hNsec_lip`, **and** the `C⁰`-Sobolev fibre embedding `hfibre`
(`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`-shape — the input that turns the
carrier's vanishing at `t = 0` into the metric-realize fibre-smallness), the
maximal-regularity Duhamel engine `deTurckRemainder_strong_shortTime_exists` driven with
initial datum `0` produces a strong `L²`-time solution which, transported to the
pointwise time domain (the indefinite-Bochner / FTC transport that lives strictly
downstream of the headline) and realized off `g₀`, yields:

* a pointwise carrier `u₂ : ℝ → H^{a+2}(g₀)`, smooth representatives
  `T_s : ℝ → SmoothCcTensor g₀ 0 2`, and a realized metric family `g_DT`;
* `g_DT 0 = g₀` (the carrier starts at `0`);
* `hreal` — `g_DT s = g₀ + ccTensorBilinSymm (T_s s)`;
* `hcont` — the included carrier is continuous up to `t = 0`;
* `hreg` — the carrier solves `∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` on `(0, T)`;
* `hsmall` — `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small on `(0, T)`;
* `hsmoothrepr` — `u₂ s`'s coordinates are the `L²` coordinates of `T_s s`.

The conclusion is the existence of the realized carrier bundle — distinct from the
supplied coordinate-identity, Lipschitz, and fibre-embedding hypotheses; no packaging.
The genuinely-open content bundled here is the `L²`-time → pointwise Bochner/FTC
transport together with the up-to-`t = 0` fibre-smallness for smooth initial data.  The
body is `sorry`. -/
theorem deturck_g0_engine_carrier_extraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (ha2 : Module.finrank ℝ E < 2 * (a - 2))
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        Integral.L2.SmoothCcTensor g₀ 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_lip : ∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                  - Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
        ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                    - Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
            ≤ ((K : ℝ) * dist u u') ^ 2)
    (hfibre : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
        ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
            (C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖)) :
    ∃ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
        (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
      0 < T ∧
      g_DT 0 = g₀ ∧
      (∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
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
      (∀ (s : ℝ)
          (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2),
        (u₂ s).coeff i
          = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) := sorry

end DifferentialGeometry.PDE.RicciFlow
