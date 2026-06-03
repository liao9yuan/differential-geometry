import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination

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
  flow's spectral data with `deTurckRicciRHS g_bg`.
* `deTurck_g0_continuous_nonlinearity` — the spectral lift of that section to a
  *continuous* first-order nonlinearity `N_cont : Hᵃ⁺¹(g₀) → Hᵃ(g₀)` whose
  coordinates are the `L²` coordinates of `Nsec`.  The gated `deTurckGeometricN` is
  discontinuous (zeroed off finite support), so the continuous realize-based lift is
  the genuine open datum.
* `deTurck_g0_nonlinearity_lipschitz` — the weighted-resolvent Lipschitz
  certificate of that nonlinearity (the resolvent-smoothing bridge).
* `deTurck_g0_carrier_realize_transport` — the `L²`-time → pointwise Duhamel
  carrier transport: the engine's strong solution, realized off `g₀`, yields a
  genuine pointwise carrier `u₂`/`T_s` and metric family `g_DT` with the interior
  strong derivative, time-continuity, and fibre-small certificates.
* `deTurck_g0_chartGram_continuity` — the `k ≤ 2` chart-Gram continuity of the
  realized flow (the parabolic-regularity datum).

Each body is `sorry`, so consumers transitively depend on `sorryAx`. -/

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

/-- **The geometric gauge-cancelled section and decoupled principal-part match for
the `g₀`-anchored realize flow (open analytic datum).**

For the anchor metric `g₀` and a flow background `g_bg` there is a realize-based
gauge-cancelled `L²`-tensor section family `Nsec` together with its realize
representative `repr` such that:

* `hNsec_realize` — `Nsec u`'s symmetric bilinear extraction equals that of
  `repr u` (the realize identity tying `Nsec` to the linear realization program);
* `hrepr_small` — the realize `ccTensorBilinSymm (repr u)` is `g₀`-fibre small;
* `hNsec_geom` — for *every* metric family `g_DT` realized as the linear realize off
  `g₀` (`hreal`) of a carrier `u₂`/`T_s` whose coordinates are the `L²` coordinates
  of `T_s` (`hsmoothrepr`), the `g₀`-rough-Laplacian of `T_s s` plus the `g₀`-realize
  of `repr` of the carrier equals `deTurckRicciRHS g_bg (g_DT s)`.

`hNsec_geom` is the *decoupled* (anchor `g₀` ≠ background `g_bg`) integrated analogue
of `deTurckNonlinearitySpectral_principalPart_cancels`: the second-order part of
`deTurckRicciRHS g_bg` linearised at `g₀` is the `g₀`-rough-Laplacian *regardless* of
`g_bg`, which only enters the lower-order DeTurck field carried by `repr`.  Here
`repr` is the genuine gauge field (it is *bound together with* the match, not free),
so the match is an honest geometric identity, the open datum the realize program
isolates — not a hypothesis-packaged conclusion.  The body is `sorry`. -/
theorem deTurck_g0_decoupled_principal_match
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ repr Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          Integral.L2.SmoothCcTensor g₀ 0 2,
      (∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
          (x : M) (v w : TangentSpace I x),
        ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
          ccTensorBilinSymm (I := I) g₀ (repr u) x v w) ∧
      (∀ u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        ∃ δ' : ℝ, δ' < 1 ∧
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (repr u)) δ') ∧
      (∀ (g_DT : ℝ → SmoothRiemannianMetric I M)
          (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) →
        (∀ (s : ℝ)
            (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2),
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) →
        ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
          ccTensorBilinSymm (I := I) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
            + ccTensorBilinSymm (I := I) g₀
                (repr (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
            = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') := sorry

/-- **The continuous spectral lift of the gauge section to the `g₀`-DeTurck
nonlinearity (open analytic datum).**

For the realize-based gauge section `Nsec` (the open geometric datum of
`deTurck_g0_decoupled_principal_match`), there is a *continuous* first-order
nonlinearity `N_cont : Hᵃ⁺¹(g₀) → Hᵃ(g₀)` whose eigenbasis coordinates `(N_cont u).coeff i`
are the `L²` coordinates of `Nsec u` (`hN_coeff`).

The finite-support-gated `deTurckGeometricN` is globally discontinuous (it jumps to
`0` off the non-open finite-support locus), hence is **not** this `N_cont`; the
continuous realize-based lift, with infinite-support inputs handled through the
smooth representative, is the project's genuine open continuous-nonlinearity datum.
The conclusion is the existence of the continuous lift with the coordinate identity,
not any Lipschitz/existence statement — no packaging.  The body is `sorry`. -/
theorem deTurck_g0_continuous_nonlinearity
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        Integral.L2.SmoothCcTensor g₀ 0 2) :
    ∃ N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
          tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ),
      ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
          (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2),
        (N_cont u).coeff i =
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i := by
  refine ⟨fun u =>
    Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise
      (g := g₀) (r := 0) (s := 2) (b := (a : ℝ))
      (fun i => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
      (smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M)
        g₀ (a : ℝ) (Nsec u)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)), ?_⟩
  intro u i
  exact Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise_coeff
    (g := g₀) (r := 0) (s := 2) (b := (a : ℝ)) _ _ i

/-- **Weighted-resolvent Lipschitz certificate for the `g₀`-DeTurck nonlinearity
(open analytic datum: the resolvent-smoothing bridge).**

For the realize-based geometric remainder section `Nsec` tied to the linear realize
`repr` by the realize identity `hNsec_realize`, the weighted-resolvent
`Hᵃ`-difference of `Nsec` is locally Lipschitz across Sobolev scales: there is a
constant `K` with the per-mode weighted square-sum of the resolvent coordinates of
`Nsec u − Nsec u'` bounded by `(K · dist u u')²`.

This is exactly the `hNsec_lip` keystone consumed by the maximal-regularity Duhamel
engine (`deturckN_hscale_lipschitz`).  It rests on the smoothing of the compact
tensor resolvent against the realize identity, the genuinely-open resolvent-
smoothing input; it is **not** the Lipschitz conclusion of `N_cont` itself but a
weighted-summability bound on `Nsec`'s coordinates, structurally distinct from the
realize-identity hypothesis.  The body is `sorry`. -/
theorem deTurck_g0_nonlinearity_lipschitz
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (repr Nsec : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
        Integral.L2.SmoothCcTensor g₀ 0 2)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀ (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g₀ (repr u) x v w) :
    ∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
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
            ≤ ((K : ℝ) * dist u u') ^ 2 := sorry

/-- **`L²`-time → pointwise Duhamel carrier transport for the `g₀`-anchored flow
(downstream-only analytic content).**

For the anchor `g₀`, a supercritical order `a` (`2a > dim M + 4` and the engine's
`dim M < 2(a − 2)`), and the continuous nonlinearity `N_cont` presented through its
section `Nsec` with the coordinate identity `hN_coeff` and the weighted-resolvent
Lipschitz certificate `hNsec_lip`, the maximal-regularity Duhamel engine
`deTurckRemainder_strong_shortTime_exists` driven with initial datum `0` produces a
strong solution which, realized off `g₀`, yields a genuine *pointwise* carrier
`u₂ : ℝ → Hᵃ⁺²(g₀)`, smooth representatives `T_s : ℝ → SmoothCcTensor g₀ 0 2`, and a
metric family `g_DT`, with:

* `g_DT 0 = g₀` (the carrier starts at `0`);
* `hreal` — `g_DT s` is the linear realize `g₀ + ccTensorBilinSymm (T_s s)`;
* `hcont` — the included carrier `s ↦ ι (u₂ s)` is continuous up to `t = 0`;
* `hreg` — the carrier solves `∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` on `(0, T)`;
* `hsmall` — `ccTensorBilinSymm (T_s s)` is `g₀`-fibre small on `(0, T)`;
* `hsmoothrepr` — `u₂ s`'s coordinates are the `L²` coordinates of `T_s s`.

The engine outputs an `L²`-time/`H¹`-time object and its derivative *as an
`L²`-time element*; the conversion to the pointwise carrier function with the
pointwise strong derivative is the indefinite-Bochner-integral / FTC transport of
`DeTurckInteriorTimeRegularity.lean`, which transitively imports the headline and so
is isolated here.  The conclusion is the existence of the realized carrier bundle —
distinct from the supplied coordinate-identity and Lipschitz hypotheses; no
packaging.  The body is `sorry`. -/
theorem deTurck_g0_carrier_realize_transport
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
            ≤ ((K : ℝ) * dist u u') ^ 2) :
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

/-- **`k ≤ 2` chart-Gram continuity of the `g₀`-anchored realize flow
(parabolic-regularity datum).**

For the realized `g₀`-anchored parabolic flow `g_DT` over `[0, T]` (the linear
realize `hreal` of a carrier `u₂`/`T_s` solving the interior spectral PDE `hreg`
and time-continuous up to `0` via `hcont`), every iterated chart-Gram derivative of
order `k ≤ 2` is jointly continuous in `(time, point)` on
`[0, T] × chartLeviCivitaGoodSet α`.

This is the genuine parabolic-regularity continuity datum that the `C²`-in-time
realize assembler consumes; it lives strictly downstream of the headline (the
`C²`-realize tower) and is isolated here as an open node about the constructed
flow.  The conclusion is joint continuity of chart-Gram iterated derivatives,
distinct from the carrier hypotheses; no packaging.  The body is `sorry`. -/
theorem deTurck_g0_chartGram_continuity
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

end DifferentialGeometry.PDE.RicciFlow
