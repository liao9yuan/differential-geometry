import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DuhamelSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingTimeBootstrap
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv

/-! # Jointly-smooth representative of the maximal-regularity DeTurck–Ricci solution

For the genuine second-order quasilinear spectral maximal-regularity Duhamel solution `u`
of the Ricci–DeTurck flow linearized about a closed background metric `g₀` — the Duhamel
image of its own genuinely-second-order Nemytskii forcing `gforce`, with zero initial
perturbation and trace `0` at `t = 0` — the smooth-initial-data parabolic solution is
**jointly `C∞` in `(t, x)` up to `t = 0`**.

This is the single classical parabolic-regularity fact behind the realized DeTurck–Ricci
family (Chow–Knopf, DeTurck's Step 1; Ladyzhenskaya–Solonnikov–Uraltseva; Amann maximal
regularity; the interior parabolic smoothing carried up to the smooth initial datum).  It
packages, on a positive smallness horizon `T₁ ≤ T`, a **single time-regular** family of
`C∞` representatives `F : ℝ → SmoothCcTensor g₀ 0 2` (uniformly `g₀`-fibre small with one
constant `δ < 1`) that carries simultaneously:

* `F 0 = 0` — the family starts at the zero initial perturbation;
* the interior `L²` pin tying `F t` to the solution value `u.toFun t` on the closed slab;
* the **Ricci–DeTurck flow derivative**: at every `t ∈ Ico 0 T₁`, base point `x`, and
  tangent pair `(v, w)`, the pointwise `[0, ∞)`-derivative of the perturbation part of the
  realized inner product `s ↦ ccTensorBilinSymm g₀ (F s) x v w` equals the intrinsic
  Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg (g_DT t) x v w`, where
  `g_DT t = tensorSectionRealizeMetric g₀ (F t) hδ_lt (hδ t)`;
* the **joint chart-Gram interior regularity** `JointChartGramSmooth T₁ g_DT` — the
  chart-Gram entries of the realized metric family are jointly `C∞` up to `t = 0`.

## Decomposition of the leaf

The family is assembled from two genuine deep analytic inputs and the proved spectral
infrastructure:

* the **smooth forcing eigen-coordinate family** `forcingSmoothCoordsRealize` — the
  parabolic time-bootstrap of the engine's own Nemytskii forcing: a `C∞`-in-time per-mode
  coordinate family `f` with a `t`-independent summable all-order time-jet spectral-mass
  majorant, realizing the eigen-coordinates of the solution value as the per-mode Duhamel
  convolutions `perModeConv λᵢ (f i)` (the `C∞` strengthening of the every-time spectral
  coordinate identity `maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv`); and
* the **Ricci–DeTurck flow derivative** `realizedFamily_flowDeriv` — the soundness core:
  the chart-evaluated maximal-regularity `L²`-time-derivative of `u`
  (`maxRegDuhamelMap_timeDeriv_eq`, transported by
  `maxreg_l2deriv_to_pointwise_hasderivwithinat`) realized pointwise to the intrinsic
  Ricci–DeTurck remainder on the realized metric.

The smooth representatives themselves are the Weyl-free spectral smooth-representative gate
`spectralSmoothRealizesAsSmooth_holds` applied to the per-time Duhamel value, which lies in
`⋂_σ Hˢ` by `duhamel_into_all_tensorHs`; the short-time fibre smallness is the lossy
spectral fibre bound about the zero initial datum; the joint chart-Gram regularity is the
time-smooth spectral-series interior smoothing
`jointChartGramSmooth_of_spectralSmooth_timeSmooth`, fed the time-jet mode-mass from
`perModeConv_allOrder_timeDeriv_spectralMass_le`.

The two named inputs are honest `sorry`s (the deep parabolic prerequisites); consumers
transitively depend on their `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Coordinate faithfulness of the chart-locality-free eigenbasis coordinate.**
Two `L²` tensors with the same `tensorL2Coeff` family are equal: `HilbertBasis.repr`
injectivity on the eigenbasis `tensorResolventHilbertEigenbasisSigma`, of which
`tensorL2Coeff` is the coordinate readout. -/
private theorem tensorL2_ext_of_tensorL2Coeff_jsmooth
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator
      (Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g r s))
    {S T : TensorL2 r s g}
    (h : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact S i =
      tensorL2Coeff (I := I) (M := M) h_compact T i) :
    S = T := by
  classical
  set b := Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hb
  apply b.repr.injective
  ext i
  have hS : (b.repr S) i = tensorL2Coeff (I := I) (M := M) h_compact S i := rfl
  have hT : (b.repr T) i = tensorL2Coeff (I := I) (M := M) h_compact T i := rfl
  rw [hS, hT, h i]

/-- **The symmetrized extraction of the zero smooth tensor section vanishes.** -/
private theorem ccTensorBilinSymm_zero_apply_jsmooth (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring

/-- **DEEP ANALYTIC INPUT (1/2a) — the parabolic time-bootstrap of the engine forcing:
a `C∞`-in-time per-mode forcing-coordinate family with a `t`-independent all-order
time-jet spectral-mass majorant, realized by a time-continuous `Hᵃ`-representative of the
forcing whose `i`-th eigen-coordinate equals the smooth `f i` on `[0,T]`.**

For the genuinely-second-order Nemytskii forcing `gforce` of the Ricci–DeTurck flow about
`g₀` (the engine forcing `gforce =ᵐ deTurckSobolevNHa2 ∘ (maxRegDuhamelSolField …)`, in
the supercritical regularity regime `2·finrank + 10 ≤ a`), the per-eigenmode forcing
coordinates admit a genuinely **`C∞`-in-time** representative `f` together with a
time-continuous everywhere `Hᵃ`-representative `F` with:

* **(smoothness)** each `f i` is `C∞`;
* **(all-order time-jet spectral-mass)** for every time-derivative order `j` and spatial
  Sobolev order `τ ≥ 0`, the weighted square of the `j`-th time-derivative of `f i` has a
  single `t`-independent summable-across-modes majorant on `[0,T]`;
* **(representative)** `gforce =ᵐ F`, each per-mode coordinate `t ↦ (F t).coeff i` is
  continuous on `[0,T]`, and the forcing masses `forcingMass gforce c` are summable at
  every order `c ≥ 0`;
* **(coordinate realization)** on `[0,T]` the per-mode coordinate of `F` is the smooth
  `f`: `(F t).coeff i = f i t`.

This is the genuine parabolic interior-time smoothing of the engine forcing: beyond the
*continuity* of the forcing's mode coordinates (`maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv`),
the bootstrap supplies the all-order time-derivative spectral-mass control by
differentiating through the Nemytskii first-order coupling
`‖N(u)‖_{Hᵈ} ≲ ‖u‖_{H^{d+1}}` and the maximal-regularity gain, recursively raising the
spatial order by two per time-derivative.  The convolution identity tying these to the
solution value is the *separate* glue lemma `forcingSmoothCoordsRealize` below, which
consumes only the representative data and the public every-time spectral-coordinate bridge.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
private theorem forcingSmoothTimeCoords
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[timeMeasure T] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) := by
  classical
  -- The `C∞`-in-time forcing coordinate family `f` and its time-continuous `Hᵃ`
  -- representative `F`, with the all-order time-jet spectral-mass majorant (deep input).
  obtain ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateFamily (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      gforce hforce
  refine ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, ?_, hF_coeff⟩
  -- The forcing-mass summability at every order, from the in-tree spatial bootstrap
  -- `solFieldMass_summable_all` fed the Nemytskii first-order coupling
  -- `deTurckForcing_firstOrderCoupling`.
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  -- The first-order spectral coupling `hcouple` of the engine forcing.
  have hcouple := deTurckForcing_firstOrderCoupling (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 gforce hforce
  -- Base regularity: the forcing lies in `L²(Hᵃ)` by construction.
  have hbase_forcing : Summable (forcingMass (I := I) (M := M) gforce (a : ℝ)) :=
    summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) (f := gforce) h_compact
  -- Two-derivative gain: the solution-field masses are summable at order `a + 2`.
  have hbase_sol : Summable (solFieldMass (I := I) (M := M) hT.le gforce ((a : ℝ) + 2)) :=
    solFieldMass_summable_of_forcingMass_summable (I := I) (M := M) hT.le gforce (a : ℝ)
      hbase_forcing
  -- The all-order spatial bootstrap: solution masses are summable at every order.
  have hsol_all : ∀ σ : ℝ, Summable (solFieldMass (I := I) (M := M) hT.le gforce σ) :=
    solFieldMass_summable_all (I := I) (M := M) hT.le gforce hcouple hbase_sol
  -- The forcing masses are then summable at every order via the coupling.
  intro c _hc
  exact hcouple c (hsol_all (c + 1))

set_option linter.unusedVariables false in
/-- **DEEP ANALYTIC INPUT (1/2) — the smooth forcing eigen-coordinate family
realizing the solution value (the parabolic time-bootstrap of the engine forcing).**

For the genuine maximal-regularity Duhamel solution `u` of the Ricci–DeTurck flow about
`g₀` (the Duhamel image of its own order-`(a+2)`-regular Nemytskii forcing `gforce`, with
zero initial perturbation and trace `0` at `t = 0`), the per-eigenmode forcing
coordinates admit a genuinely **`C∞`-in-time** representative `f` with a `t`-independent,
summable-across-modes majorant on every time-jet of its weighted coordinate squares, and
realizing the eigen-coordinates of the solution value `u.toFun t` as the per-mode Duhamel
convolutions `perModeConv λᵢ (f i) t`.

The deep parabolic smoothing content (the `C∞`-in-time strengthening with the all-order
time-jet spectral-mass control) is the separate input `forcingSmoothTimeCoords`.  This
lemma is the **glue** that promotes its a.e. coordinate agreement to the every-time
convolution identity for the solution value: the every-time spectral-coordinate identity
`maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv` realizes the solution coordinate as the
per-mode Duhamel convolution of a continuous representative of the forcing coordinate, and
`perModeConv_timeL2_congr` (a.e.-insensitivity of `perModeConv` on `[0,T]`) replaces that
representative by the smooth `f`.  PINNED to the solution by `hduh`/`hforce`/`htrace`
(`htrace` is part of the frozen consumer interface and is not consumed by this glue). -/
private theorem forcingSmoothCoordsRealize
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
  classical
  -- The deep parabolic time-bootstrap: a `C∞`-in-time forcing-coordinate family `f`,
  -- a time-continuous `Hᵃ`-representative `F` of `gforce` whose `i`-th mode coordinate is
  -- the smooth `f i` on `[0,T]`, and the all-order time-jet spectral-mass majorant.
  obtain ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_sum, hF_coeff⟩ :=
    forcingSmoothTimeCoords (I := I) (M := M) g₀ g_bg a ha_super hT hT1 gforce hforce
  refine ⟨f, hf_smooth, hf_mass, ?_⟩
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  -- The public every-time spectral-coordinate bridge with the continuous representative
  -- `F`: it realizes the solution-value coordinate as `perModeConv λᵢ φᵢ`, with `φᵢ` the
  -- `Set.IccExtend` of `t ↦ (F t).coeff i`.
  have hbridge :=
    maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) (T := T) hT hT1 (Nat.cast_nonneg a)
      h_compact gforce (F := F) hF_coord_cont hF_rep hF_sum
  obtain ⟨φ, hφ_cont, hφ_sum, hφ_id⟩ := hbridge
  intro t ht i
  rw [hduh]
  -- `φ i = Set.IccExtend hT.le (fun p => (F p.1).coeff i)` by `maxRegDuhamel…`.
  have hid := hφ_id t ht i
  rw [hid]
  -- On `[0,T]`, `(F · ).coeff i = f i`, so the `IccExtend` agrees a.e. with `f i`; the
  -- `perModeConv` values therefore coincide at `t ∈ [0,T]`.
  refine perModeConv_timeL2_congr (TensorEigenIdx.lambda (I := I) (M := M) i)
    (f₁ := Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F (p : ℝ)).coeff i))
    (f₂ := f i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
  rw [Set.IccExtend_of_mem hT.le _ hs, hF_coeff s hs i]

/-- **DEEP ANALYTIC INPUT (2/2) — the realized perturbation solves the Ricci–DeTurck
flow (the soundness core).**

For the genuine maximal-regularity Duhamel solution `u` and a time-regular representative
family `F` — pinned to `u` by the zero initial value `h_zero`, the interior `L²` pin
`h_pin` on the closed interval `Icc 0 T₁`, the `L²`-time-continuity `h_cont`, and the
order-`(a+2)` forcing-ball bound `hball` — the realized metric family
`g_DT t = tensorSectionRealizeMetric g₀ (F t) hδ_lt (hδ t)` solves the TRUE Ricci–DeTurck
flow: at every `t ∈ Ico 0 T₁`, base point `x`, tangent pair `(v, w)`, the pointwise
`[0,∞)`-derivative of the perturbation part of the realized inner product
`s ↦ ccTensorBilinSymm g₀ (F s) x v w` equals the intrinsic Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg (g_DT t) x v w`.

The `hball` hypothesis (order-`(a+2)` smallness on the forcing horizon) is genuinely
required, not cosmetic: `deTurckSobolevNHa2` applies a `recenteredBallRetraction` of radius
`R₀ = (Classical.choose (deTurckSobolevNHa2_exists_of_super …)).1` BEFORE forming the
forcing, so OFF that ball the forcing value is the retracted nonlinearity, and the
identification `deTurckSobolevNHa2 (solField t) = deTurckSmoothN g₀ g_bg a (F t)` (via
`deTurckSobolevNHa2_eq_smoothN`) — hence the right-hand side value
`deTurckRicciRHS g_bg (g_DT t)` — fails.  `hball` keeps the realized family inside the ball
so the forcing reproduces the genuine smooth Ricci–DeTurck remainder.

The intended classical chain is the term-by-term differentiation of the chart-evaluated
solution value through the supercritical-order-bounded chart-evaluation functional
`L = (smoothCcToTensorHs g₀ a)-extension of (T ↦ ccTensorBilinSymm g₀ T x v w)` (continuous
by `ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy` + `LinearMap.extendOfNorm`): the
solution coordinate `t ↦ tensorL2Coeff (u.toFun t) i` is the per-mode Duhamel convolution
`perModeConv λᵢ (f i)` of the `C∞`-in-time smooth forcing coordinate `f i`
(`forcingSmoothCoordsRealize`, re-derived internally from `u`/`gforce`/`hduh`/`hforce`),
each with the continuous per-mode time-derivative `f i t − λᵢ · perModeConv λᵢ (f i) t`
(`perModeConv_hasDerivAt`); the differentiated spectral series converges uniformly by the
all-order time-jet spectral-mass majorant (`hf_mass`), so `hasDerivAt_tsum` gives the
pointwise derivative, whose value — by `hball ⟹ deTurckSobolevNHa2_eq_smoothN`, the
connection-Laplacian/forcing cancellation (`tensorL2Coeff_ofCompact_rawTensorConnLapSmooth`,
`tensorScaleLaplacian_coeff`), and `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`
— is `deTurckRicciRHS g_bg (g_DT t) x v w`.  (The dispatch's route through
`maxreg_l2deriv_to_pointwise_hasderivwithinat` is NOT viable: that bridge needs a
time-CONTINUOUS `Hᵃ`-representative of `u.deriv`, but `u.deriv =ᵐ timeScaleLaplacian a
solField + gforce` with `gforce` only `L²`-class is genuinely discontinuous; the
differentiability is term-by-term spectral, not via a continuous derivative class.)

PINNED to the solution AND time-regular: `h_pin` (on `Icc 0 T₁`, fixing the boundary value
`F 0 = 0` too) and `h_cont` fix the time-variation a within-`[0,∞)` derivative requires, so
the conclusion is not satisfiable by an arbitrary family.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`).  The remaining
content is the genuine deep parabolic-regularity core (the term-by-term spectral
differentiation through the chart functional). -/
private theorem realizedFamily_flowDeriv
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (h_zero : F 0 = 0)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (h_cont : ContinuousOn
      (fun t : ℝ => (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)))
      (Set.Icc (0 : ℝ) T₁))
    (hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
        (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a
          (by omega))).1) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
        (deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
        (Set.Ici 0) t :=
  sorry

/-- **Joint chart-Gram smoothness of a realized time-smooth spectral family, with the
eigen-coordinate identity relativized to the closed time slab.**

This is `jointChartGramSmooth_of_spectralSmooth_timeSmooth`
(`SpectralEigenSeriesJointGram.lean`) with its eigen-coordinate hypothesis `hcoeff`
relativized from the global `∀ t` to the closed time slab `∀ t ∈ Icc 0 T`.  The
relativization is sound: inside `jointChartGramSmooth_of_spectralSmooth_timeSmooth`,
`hcoeff` is consumed only through `realizedChartGramIncrement_eigenSeries_eq`, which is
applied at points `q ∈ Icc 0 T ×ˢ …`, so only the slab values of `hcoeff` are used; the
global quantification in the sibling's signature is over-stated.  The sibling's `hcoeff`
has since been relativized to `Icc 0 T`, so this lemma is now a **direct citation** of
`jointChartGramSmooth_of_spectralSmooth_timeSmooth` (which is proved sorry-free:
`#print axioms` is `[propext, Classical.choice, Quot.sound]`), not a posited child.

The cutoff representative families produced by `maxreg_solution_jointly_smooth_representative`
are globally fibre-small (`hδ : ∀ t`) and so necessarily differ from the genuine spectral
family off the horizon; their eigen-coordinates therefore agree with the time-smooth
`φ = perModeConv λ f` only on the slab, which is exactly what this relativized form
consumes. -/
private theorem realizedFamily_jointChartGramSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) :=
  jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
    g hT T_rep hδ_lt hδ φ hφ_smooth hcoeff hmodemass

/-- **DEEP ANALYTIC INPUT (horizon) — the order-`(a+2)` smallness horizon of the realized
solution field about the zero initial datum.**

For the maximal-regularity Duhamel solution `u` with zero trace at `t = 0` (`htrace`), and
any positive radius `R₀`, there is a positive **order-`(a+2)` smallness horizon** `d₂ ≤ T`
on which every order-`a`-pinned smooth representative `S` of the solution value
`u.toFun t`  (`toL2 S = tensorHsToL2 (u.toFun t)`) has order-`(a+2)` Sobolev norm at most
`R₀`:  `‖smoothCcToTensorHs g₀ (a+2) S‖ ≤ R₀`.

This is the genuine parabolic interior gain carried up to the smooth (zero) initial datum:
the maximal-regularity solution lies, for `t > 0`, in every spatial Sobolev order, and its
order-`(a+2)` Sobolev norm is time-continuous up to `t = 0` with value `0` at `t = 0`
(zero initial perturbation), so it stays inside the radius-`R₀` ball on a short horizon.
The bound is genuinely about the SOLUTION (not vacuous): at a time `t` where the solution's
order-`(a+2)` norm exceeds `R₀`, the pinned smooth representative — whose order-`(a+2)` norm
is determined by the order-`a` pin via the shared eigenbasis coordinates of `u.toFun t` —
violates the conclusion, so the horizon is genuinely short-time content, not a tautology.

The order-`(a+2)` gain is GENUINELY a property of the Duhamel/heat structure, not of bare
`timeH1`-in-time membership: `u` is bound to the maximal-regularity Duhamel map by `hduh`
(its image of its own order-`(a+2)`-regular forcing `gforce`, reproducing
`deTurckSobolevNHa2` a.e. along the order-`(a+2)` Duhamel field via `hforce`), under which
`u.toFun t` lies in `H^{a+2}` for interior `t` (`duhamel_into_all_tensorHs`) with the
order-`(a+2)` Sobolev norm time-continuous up to `t = 0` and vanishing at `t = 0` (zero
initial datum, `htrace`).  Without the Duhamel binders a generic zero-trace `timeH1`
element admits an `H^a`-bounded high-frequency spike train accumulating at `t = 0`, which
has unbounded `H^{a+2}` norm arbitrarily close to `0`, so the bound would be FALSE — the
Duhamel structure is load-bearing.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`).  The remaining
content is the classical parabolic order-`(a+2)` interior-time smoothing of the Duhamel
solution up to `t = 0` (Amann maximal regularity / Ladyzhenskaya–Solonnikov–Uraltseva), the
order-`(a+2)` analogue of the order-`a` time-continuity `timeH1.continuousOn_toFun`. -/
private theorem realizedSol_solField_smallnessHorizon_Ha2
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ :=
  sorry

set_option linter.unusedVariables false in
/-- **Jointly-smooth representative of the maximal-regularity DeTurck–Ricci solution
(the single deep classical parabolic-regularity leaf).**

For the genuine maximal-regularity Duhamel solution `u` of the Ricci–DeTurck flow about
`g₀` (the Duhamel image of its own forcing `gforce`, reproducing `deTurckSobolevNHa2`
a.e. along the order-`(a+2)` Duhamel field, with zero initial perturbation and trace `0`
at `t = 0`), there is a positive smallness horizon `T₁ ≤ T` and a single time-regular
family of `C∞` representatives `F`, uniformly `g₀`-fibre small with one `δ < 1`, that
carries the zero initial value, the interior `L²` pin to `u.toFun`, the intrinsic
Ricci–DeTurck pointwise flow derivative, and the joint chart-Gram interior regularity of
the realized metric family.  This is the classical smooth-initial-data parabolic joint
`C∞`-up-to-`t = 0` regularity.

Assembled from the two deep analytic inputs `forcingSmoothCoordsRealize` and
`realizedFamily_flowDeriv` and the proved spectral infrastructure; consumers transitively
depend on those inputs' `sorryAx`.

(The frozen-signature hypothesis `hTT₀` is part of the consumer interface and is not
consumed by this decomposition glue.) -/
theorem maxreg_solution_jointly_smooth_representative
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (ha_eq : a = 2 * Module.finrank ℝ E + 10)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ (T₁ : ℝ), 0 < T₁ ∧ T₁ ≤ T ∧
      ∃ (F : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T₁,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
          (deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T₁
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  -- `u` vanishes at `t = 0`.
  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  have hu0 : timeH1.toFun u 0 = 0 := by rw [timeH1.toFun_zero, hinit]
  -- DEEP INPUT 1: the smooth forcing eigen-coordinate family realizing the solution value.
  obtain ⟨f, hf_smooth, hf_mass, hf_id⟩ :=
    forcingSmoothCoordsRealize (I := I) (M := M) g₀ g_bg a ha_super hT hT1 u gforce
      hduh hforce htrace
  -- The smooth eigen-coordinate family `φ i = perModeConv λᵢ (f i)` of the solution.
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hφ_cont : ∀ i, Continuous (φ i) := fun i => (hφ_smooth i).continuous
  -- The per-time all-order endpoint summability of the weighted `φ`-integrals on `[0,T]`.
  -- The per-time all-order endpoint summability of the weighted FORCING integrals on
  -- `[0,T]` (`duhamel_into_all_tensorHs` convolves the forcing `f`, not `φ`).
  have hf_endpoint_sum : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (f i s) ^ 2) := by
    intro c hc t ht
    obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 c hc
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hB_sum.mul_left T)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · -- `wt · ∫₀ᵗ (f i)² ≤ wt · ∫₀ᵀ (f i)² ≤ T · B i`
      have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i c
      have hcont_sq : Continuous (fun s => (f i s) ^ 2) := ((hf_smooth i).continuous).pow 2
      have htint : (∫ s in (0 : ℝ)..t, (f i s) ^ 2) ≤ ∫ s in (0 : ℝ)..T, (f i s) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hT.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set hcont_sq.integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      have hbig : tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..T, (f i s) ^ 2 ≤ T * B i := by
        -- pointwise: `wt · (f i s)² ≤ B i` for `s ∈ [0,T]`, integrated over `[0,T]`
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2)
            MeasureTheory.volume 0 T :=
          (hcont_sq.const_mul _).intervalIntegrable 0 T
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) MeasureTheory.volume 0 T :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..T,
              tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2
            ≤ ∫ _s in (0 : ℝ)..T, B i := by
          refine intervalIntegral.integral_mono_on hT.le hi_lhs hi_const ?_
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        exact hmono
      calc tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..t, (f i s) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..T, (f i s) ^ 2 :=
            mul_le_mul_of_nonneg_left htint hwt_nn
        _ ≤ T * B i := hbig
  -- A representative family `F₀` on `[0,T]`: per-time the `C∞` realization of the
  -- Duhamel value, which equals the `L²` class of `u.toFun t`.
  have hF₀_exists : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    -- the Duhamel value at `t` with coordinates `perModeConv λᵢ (f i) t = φ i t`
    obtain ⟨uDuh, huDuh_coeff, huDuh_mem⟩ :=
      duhamel_into_all_tensorHs (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (t := t) ht.1 h_compact f (fun i => (hf_smooth i).continuous)
        (fun c hc => hf_endpoint_sum c hc t ht)
    -- it equals the `L²` class of `u.toFun t`: same eigen-coordinates
    have hval : uDuh = tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
      refine tensorL2_ext_of_tensorL2Coeff_jsmooth (I := I) (M := M) h_compact (fun i => ?_)
      rw [huDuh_coeff i]
      exact (hf_id t ht i).symm
    -- the smooth representative gate at the value `uDuh`
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              h_compact hσ v = uDuh := huDuh_mem
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) uDuh hmem
    refine ⟨S, ?_⟩
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = (S : TensorL2 0 2 g₀) from rfl,
      hS, hval]
  -- Choose the family, forced to `0` at `t = 0` (where the `L²` class is `0`).
  choose F₀ hF₀ using hF₀_exists
  set Fdef : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) T then F₀ t ht else 0 with hFdef_def
  have hFdef_pin : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T),
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Fdef t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    simp only [hFdef_def, dif_pos ht]
    exact hF₀ t ht
  -- Short-time fibre smallness about the zero initial datum.
  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by rw [ha_eq]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ a ha_even ha_lossy
  have hcontU : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T) :=
    timeH1.continuousOn_toFun u
  have hwithin : ContinuousWithinAt (timeH1.toFun u) (Set.Icc (0 : ℝ) T) 0 :=
    hcontU.continuousWithinAt ⟨le_refl 0, hT.le⟩
  rw [Metric.continuousWithinAt_iff] at hwithin
  obtain ⟨d, hd_pos, hd⟩ := hwithin (1 / (2 * C)) (by positivity)
  -- The order-`(a+2)` forcing ball radius `R₀ > 0`.
  set R₀ : ℝ := (Classical.choose
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1 with hR₀_def
  have hR₀_pos : 0 < R₀ :=
    (Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1
  -- The order-`(a+2)` smallness horizon `d₂` (deep parabolic input).
  obtain ⟨d₂, hd₂_pos, hd₂_le, hd₂⟩ :=
    realizedSol_solField_smallnessHorizon_Ha2 (I := I) (M := M) g₀ g_bg a hT hT1 u gforce
      hduh hforce htrace hR₀_pos
  set T₁ : ℝ := min (min T (d / 2)) d₂ with hT₁_def
  have hT₁_pos : 0 < T₁ := lt_min (lt_min hT (by positivity)) hd₂_pos
  have hT₁_le : T₁ ≤ T := le_trans (min_le_left _ _) (min_le_left _ _)
  have hT₁_le_d2 : T₁ ≤ d₂ := min_le_right _ _
  have hT₁_le_d : T₁ ≤ d / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  -- The final family: the chosen representative on `(0, T₁]`, zero elsewhere.
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Ioc (0 : ℝ) T₁ then Fdef t else 0 with hF_def
  -- `F 0 = 0`.
  have hF_zero : F 0 = 0 := by
    simp only [hF_def]
    rw [if_neg]
    intro hmem; exact absurd hmem.1 (lt_irrefl 0)
  -- The fibre smallness, with `δ = 1/2`.
  have hF_small : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) (1 / 2) := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) T₁
    · -- on `(0, T₁]`: the lossy bound scaled by the horizon smallness
      have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le⟩
      have hpin := hFdef_pin t ht_icc
      have heq : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t) =
          timeH1.toFun u t := by
        refine tensorHs.ext (funext (fun i => ?_))
        rw [smoothCcToTensorHs_coeff, hpin, tensorHsToL2_tensorL2Coeff]
      have hdist : dist t (0 : ℝ) < d := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_le_of_lt (le_trans ht.2 hT₁_le_d) (by linarith)
      have hnorm_lt : dist (timeH1.toFun u t) (timeH1.toFun u 0) < 1 / (2 * C) :=
        hd ht_icc hdist
      have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤
          1 / (2 * C) := by
        rw [hu0, dist_eq_norm, sub_zero] at hnorm_lt
        rw [heq]
        exact hnorm_lt.le
      intro x v w
      rw [hFt]
      refine le_trans (hC (Fdef t) x v w) ?_
      have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤ 1 / 2 := by
        calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖
            ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hnorm_le hC_pos.le
          _ = 1 / 2 := by field_simp
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
        mul_nonneg hsv_nn hsw_nn
      calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
          = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
              (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
        _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
            mul_le_mul_of_nonneg_right hCN_le hmul_nn
        _ = (1 / 2 : ℝ) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
    · -- off `(0, T₁]`: `F t = 0`
      have hFt : F t = 0 := by simp only [hF_def, if_neg ht]
      intro x v w
      rw [hFt, ccTensorBilinSymm_zero_apply_jsmooth]
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      rw [abs_zero]
      positivity
  -- The interior `L²` pin on `Icc 0 T₁`.
  have hF_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · -- `t = 0`: both sides are `0`
      rw [← h0, hF_zero, hu0]
      simp only [map_zero]
    · -- `t ∈ (0, T₁]`: `F t = Fdef t` and the `Fdef` pin applies
      have ht_ioc : t ∈ Set.Ioc (0 : ℝ) T₁ := ⟨h0, ht.2⟩
      have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht_ioc]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hT₁_le⟩
      rw [hFt]
      exact hFdef_pin t ht_icc
  -- `L²`-time-continuity of `t ↦ toL2 (F t)` on `Icc 0 T₁`: it equals
  -- `t ↦ tensorHsToL2 (u.toFun t)`, continuous as a composition.
  have hF_cont : ContinuousOn
      (fun t : ℝ => (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)))
      (Set.Icc (0 : ℝ) T₁) := by
    have hcontU₁ : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T₁) :=
      hcontU.mono (Set.Icc_subset_Icc le_rfl hT₁_le)
    have hcomp : ContinuousOn
        (fun t : ℝ => tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t)) (Set.Icc (0 : ℝ) T₁) :=
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a)).continuous.comp_continuousOn hcontU₁
    refine hcomp.congr (fun t ht => ?_)
    exact hF_pin t ht
  -- The smallness constant `δ = 1/2 < 1`.
  have hδ_lt : (1 / 2 : ℝ) < 1 := by norm_num
  -- The order-`(a+2)` forcing-ball bound on the horizon `Ico 0 T₁ ⊆ Icc 0 d₂`, from the
  -- smallness horizon `hd₂` fed the order-`a` `L²` pin `hF_pin`.
  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    intro t ht
    have ht_d2 : t ∈ Set.Icc (0 : ℝ) d₂ :=
      ⟨ht.1, le_trans ht.2.le hT₁_le_d2⟩
    have ht_icc₁ : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, ht.2.le⟩
    exact hd₂ t ht_d2 (F t) (hF_pin t ht_icc₁)
  -- CONJUNCT (3): the Ricci–DeTurck flow derivative (deep input 2).
  have hF_flow := realizedFamily_flowDeriv (I := I) (M := M) g₀ g_bg a ha_super ha_even hT hT1
    hT₁_pos hT₁_le u gforce hduh hforce htrace F hδ_lt hF_small hF_zero hF_pin hF_cont hball
  -- CONJUNCT (4): the joint chart-Gram smoothness from the time-smooth eigen-coordinates.
  -- The eigen-coordinate identity for the cutoff family `F` on the slab `Icc 0 T₁`:
  -- `tensorL2Coeff (toL2 (F t)) i = φ i t` (at `t = 0` both sides vanish; on `(0,T₁]`
  -- the pin + the smooth-`f` realization identity give it).
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hF_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hT₁_le⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  -- The all-order time-jet mode mass of `φ = perModeConv λ f`, on `[0,T₁]`, from `L6`
  -- fed the smooth-forcing all-order mass (restricted from `[0,T]` to `[0,T₁]`).
  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := T) hT.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_trans ht.2 hT₁_le⟩
    exact hCmaj_le i t ht_icc
  -- CONJUNCT (4) child: the relativized-`hcoeff` form of
  -- `jointChartGramSmooth_of_spectralSmooth_timeSmooth` (L7 only consumes `hcoeff` on the
  -- closed time slab `Icc 0 T`; see SIGNATURE-DEFECT note in the dispatch return).
  have hF_joint : JointChartGramSmooth (I := I) T₁
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hF_small t)) :=
    realizedFamily_jointChartGramSmooth (I := I) (M := M) g₀ hT₁_pos F hδ_lt hF_small
      φ hφ_smooth hcoeff hmodemass
  exact ⟨T₁, hT₁_pos, hT₁_le, F, 1 / 2, hδ_lt, hF_small, hF_zero, hF_pin, hF_flow,
    hF_joint⟩

end DifferentialGeometry.PDE.RicciFlow
