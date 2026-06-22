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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous

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
open DifferentialGeometry.Integral.Connection
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
the smoothing supplies the all-order time-derivative spectral-mass control AND the all-order
forcing-mass summability `∀ c ≥ 0, Summable (forcingMass gforce c)`.  The Ricci–DeTurck
remainder loses exactly **two** spatial derivatives (`‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}`, the
AFFINE ball bound `deTurckRemainder_iteratedCovGradSum_ballBound`, window `d + 2`), so the
all-order forcing-mass summability is NOT obtained by a one-order
(`solFieldMass (d+1) → forcingMass d`) coupling bootstrap — that net advance is `0` for a
`+2` nonlinearity — but is the genuine small-data parabolic interior-smoothing output about
the zero initial datum.  The convolution identity tying these to the solution value is the
*separate* glue lemma `forcingSmoothCoordsRealize` below, which consumes only the
representative data and the public every-time spectral-coordinate bridge.

Proven as glue over the accepted deferred existence-side forcing-regularity input
`deTurckForcing_smoothTimeCoordinateFamily` (`ForcingTimeBootstrap.lean`, the realize-side's
posited regularity leaf, the analogue of `realizedSol_forcing_continuousRepr_allOrderMass`,
delivering both the `C∞`-in-time coordinate family and the all-order forcing-mass
summability); its body is `sorry`-free and consumers transitively depend only on that input's
`sorryAx`. -/
private theorem forcingSmoothTimeCoords
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateFamily (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce
  exact ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩

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
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩ :=
    forcingSmoothTimeCoords (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
  have hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
    intro i
    have hrep_coeff : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (F t).coeff i) := hF_rep.fun_comp (fun S => S.coeff i)
    refine hrep_coeff.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
    exact hF_coeff s hs i
  refine ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, ?_, hforce_coord⟩
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  intro t ht i
  rw [hduh, tensorHsToL2_tensorL2Coeff (Nat.cast_nonneg a)]
  have hid := carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
    (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hT hT1 hd₂_pos hd₂_le h_compact gforce
    (F := F) hF_coord_cont hF_rep i ht
  rw [hid]
  refine perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
    (f₁ := Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F (p : ℝ)).coeff i))
    (f₂ := f i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
  rw [Set.IccExtend_of_mem hd₂_pos.le _ hs, hF_coeff s hs i]

set_option linter.unusedVariables false in
/-- **The order-`(a+2)` time-continuity of the realized smooth-representative field.**

For a time-smooth spectral family whose order-`0` `L²` eigen-coordinates of the smooth
representative `F t` are the `C∞`-in-time scalars `φ i t` on the closed slab (`hcoeff`),
with the all-order time-jet spectral-mass majorant (`hmodemass`), the order-`(a+2)`
spectral-embedding field `t ↦ smoothCcToTensorHs g₀ (a+2) (F t)` is continuous in time on
the closed slab `Icc 0 T₁`.

This is the **continuity analogue** of the joint chart-Gram interior regularity
`realizedFamily_jointChartGramSmooth` (and of the order-`(a+2)` smallness horizon
`realizedSol_solField_smallnessHorizon_Ha2`): it is the Weierstrass `M`-test on the
order-`(a+2)` `Hˢ`-norm series `∑ᵢ (φ i t) • bᵢ` fed the continuity of each mode `φ i`
and a single uniform-in-`t` summable majorant.  The order-`(a+2)` topology is genuinely
stronger than the `L²` topology of the file's existing `hF_cont`, so this is the genuine
parabolic order-`(a+2)` time-regularity of the realized field, not a consequence of the
`L²`-continuity.

PROVEN sorry-free by `tensorHs_continuousOn_of_coeff_of_higher_mass`: the eigen-coordinate
presentation `(smoothCcToTensorHs g₀ (a+2) (F t)).coeff i = φ i t` (`smoothCcToTensorHs_coeff`
+ `hcoeff`) exhibits the field as the basis series `∑ᵢ (φ i t) • bᵢ`; the per-mode norm
`‖(φ i t) • bᵢ‖² = tensorSobolevWeight i (a+2) · (φ i t)²` is dominated, *uniformly in `t`*,
by the geometric/arithmetic-mean split against the `(0, (a+2)+(weylSobolevExp+1))` instance of
the all-order time-jet majorant `hmodemass` — the gain of `weylSobolevExp+1` spatial orders
turns the Weyl-summable inverse weight (`tensorEigen_summable_negpow`) into a summable
square-root majorant — and Mathlib's `continuousOn_tsum` closes the continuity. -/
private theorem realizedSol_solField_continuousOn_Ha2
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T₁ : ℝ} (hT₁_pos : 0 < T₁)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) := by
  classical
  -- The order-`σ' = (a+2) + (weylSobolevExp + 1)` higher-order spectral mass, supplying a
  -- summable square-majorant strictly above the Weyl summability threshold.
  set σ : ℝ := (a : ℝ) + 2 with hσ_def
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hp_def
  set σ' : ℝ := σ + p with hσ'_def
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmodemass 0 σ' (by
    rw [hσ'_def, hσ_def, hp_def]; positivity)
  -- Drop the `iteratedDeriv 0` in the majorant.
  have hmass : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      tensorSobolevWeight (I := I) (M := M) i σ' * (φ i t) ^ 2 ≤ Cmaj i := by
    intro i t ht
    have := hCmaj_le i t ht
    rwa [iteratedDeriv_zero] at this
  -- The eigen-coordinate presentation of the embedded field.
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hcoeff t ht i
  -- Apply the Weierstrass `M`-test for eigen-coordinate-presented `Hˢ`-families.
  have hwthr : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by
    rw [hσ'_def, hp_def]; ring_nf; linarith
  exact tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀ hwthr
    (s := Set.Icc (0 : ℝ) T₁)
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ hcoeff'
    (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum hmass

set_option linter.unusedVariables false in
/-- **DEEP ANALYTIC INPUT (2/2a) — the pointwise forcing-coordinate identification.**

For the genuine maximal-regularity Duhamel solution `u` and a smooth representative family
`F` pinned to `u` on the closed slab `Icc 0 T₁` (`h_pin`), with the order-`(a+2)` forcing
ball bound `hball`, the `C∞`-in-time smooth forcing coordinate `f i` (from
`forcingSmoothCoordsRealize`) equals, at every interior time `t ∈ Ico 0 T₁` and eigen-index
`i`, the `i`-th eigen-coordinate of the genuine smooth Ricci–DeTurck remainder
`deTurckSmoothRemainder g₀ g_bg (F t)`:

  `f i t = tensorL2Coeff (toL2 (deTurckSmoothRemainder g₀ g_bg (F t) hδ_lt (hδ t))) i`.

This is the soundness link tying the forcing coordinate to the realized nonlinearity.  It
is the **pointwise** (every interior `t`) reading of the a.e. forcing identity `hforce`
(`gforce =ᵐ deTurckSobolevNHa2 ∘ solField`): the forcing coordinate `f i`, a continuous
representative of `gforce`'s `i`-th coordinate, agrees a.e. with the `i`-th coordinate of
`deTurckSobolevNHa2 (solField t)`, which on the ball (`hball`) reproduces
`deTurckSmoothN (F t)` (`deTurckSobolevNHa2_eq_smoothN`), whose coordinate is exactly the
remainder coordinate (`deTurckSmoothN_coeff`).  Upgrading the a.e. agreement to the
everywhere-on-interior identity uses the order-`(a+2)` time-continuity of the realized
solution field up to `t = 0`; the smooth `f i` is continuous, and
`t ↦ deTurckSmoothN (F t).coeff i` is continuous on the slab through the continuity of the
realized field, so the two continuous functions agreeing a.e. agree everywhere on the open
interior, hence at every `t ∈ Ico 0 T₁` (`MeasureTheory.Measure.eqOn_Ico_of_ae_eq`).

PROVEN as glue: the a.e. forcing-coordinate identity is the forcing-coordinate link
`hforce_coord` (`f i =ᵐ (gforce).coeff i`) composed with `hforce`
(`gforce =ᵐ deTurckSobolevNHa2 ∘ solField`) and the slab order-`(a+2)` field identity
`solField t =ᵐ smoothCcToTensorHs g₀ (a+2) (F t)` (classical-stacking of the per-mode
structural integral identities `maxRegDuhamelSolField_coeff_ae` (`u₀ = 0`) and
`recentredCarrier_toFun_coeff`, pinned through `h_pin`), then `deTurckSobolevNHa2_eq_smoothN`
on the ball; the right-side continuity is the order-`(a+2)` field continuity
`realizedSol_solField_continuousOn_Ha2` composed with the `deTurckSobolevNHa2` Lipschitz
(`deTurckSobolevNHa2_lipschitzWith`) and the continuous coordinate functional `coeffCLM`.  The
only deep input transited is the posited order-`(a+2)` field continuity leaf
`realizedSol_solField_continuousOn_Ha2` (the soundness-side analogue of the smoothness
horizon `realizedSol_solField_smallnessHorizon_Ha2`); consumers transitively depend on its
`sorryAx`. -/
private theorem realizedForcingCoord_eq_smoothN
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
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
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)] f i)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
        (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a
          (by omega))).1) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg (F t) hδ_lt (hδ t))) i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) hc
  -- The time-smooth eigen-coordinate family `φ i = perModeConv λᵢ (f i)` of the solution.
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  -- The eigen-coordinate identity on the closed slab `Icc 0 T₁`:
  -- `tensorL2Coeff (toL2 (F t)) i = φ i t` (from `h_pin` + `hf_id`).
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [h_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]

  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
  
  
  have hfield_cont : ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) :=
    realizedSol_solField_continuousOn_Ha2 (I := I) (M := M) g₀ a hT₁_pos F φ hφ_smooth
      hcoeff hmodemass
  -- The order-`(a+2)` field identity on the slab: the genuine Duhamel solution field
  -- equals (a.e.) the order-`(a+2)` embedding of the smooth representative `F t`.  This is
  -- the classical-stacking consequence of the per-mode structural integral identities
  -- `maxRegDuhamelSolField_coeff_ae` (`u₀ = 0`) and `recentredCarrier_toFun_coeff`, pinned
  -- through `h_pin`/`hf_id`.
  have hu_eq : u = recentredCarrier (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce := by
    refine timeH1.ext ?_ ?_
    · have hinit : u.init = 0 := by
        rw [← timeH1.trace0_apply (X := tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) (T := T) u]
        exact htrace
      rw [hinit]
      simp only [recentredCarrier, timeH1.init_mk]
    · rw [hduh]
      simp only [recentredCarrier, timeH1.deriv_mk]
  have hfield_ae : (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)) := by
    -- Per-mode a.e. identity on the slab, assembled across the countable eigen-index.
    have hper : ∀ i, ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T₁)),
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i := by
      intro i
      -- `(solField t).coeff i =ᵐ ∫₀ᵗ deriv.coeff i` (the `u₀ = 0` structural identity),
      -- restricted from `Icc 0 T` to the slab `Icc 0 T₁`.
      have hsub : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hT₁_le
      have hsol := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
          (h_compact := hc) (a := (a : ℝ)) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i)
      filter_upwards [hsol, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc]
        with t htsol htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := hsub htmem
      rw [htsol, tensorHs.zero_coeff, zero_add]
      -- `(u.toFun t).coeff i = ∫₀ᵗ deriv.coeff i` (the carrier integral identity).
      have hcarr : (timeH1.toFun u t).coeff i =
          ∫ s in (0 : ℝ)..t, ((maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce).deriv s).coeff i := by
        rw [hu_eq]
        exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i htmem'
      rw [← hcarr, smoothCcToTensorHs_coeff, h_pin t htmem, tensorHsToL2_tensorL2Coeff]
    rw [← MeasureTheory.ae_all_iff] at hper
    filter_upwards [hper] with t ht
    exact tensorHs.ext (funext fun i => ht i)
  -- Assemble: the a.e. forcing-coordinate identity, then the a.e.→everywhere upgrade.
  -- Fix the eigen-index and prove `EqOn (f i) RHS` on `Ico 0 T₁`.
  intro t₀ ht₀ i
  set RHS : ℝ → ℝ := fun t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg (F t) hδ_lt (hδ t))) i
    with hRHS_def
  -- RHS equals the eigen-coordinate of `deTurckSmoothN g₀ g_bg a (F t)`.
  have hRHS_smoothN : ∀ t, RHS t =
      (deTurckSmoothN (I := I) (M := M) g₀ g_bg a (F t) hδ_lt (hδ t)).coeff i := by
    intro t; rw [hRHS_def, deTurckSmoothN_coeff]
  -- On the slab the smooth nonlinearity coincides with `deTurckSobolevNHa2` of the embedding.
  have heqN : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i = RHS t := by
    intro t ht
    rw [hRHS_smoothN t,
      deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super (F t)
        hδ_lt (hδ t) (hball t ht)]
  
  
  obtain ⟨KN, hKN⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hRHS_cont : ContinuousOn RHS (Set.Ico (0 : ℝ) T₁) := by
    have hcomp : ContinuousOn
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i)
        (Set.Icc (0 : ℝ) T₁) := by
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)))
          (Set.Icc (0 : ℝ) T₁) :=
        hKN.continuous.comp_continuousOn hfield_cont
      exact (coeffCLM (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (σ := (a : ℝ)) i).continuous
        |>.comp_continuousOn hN_cont
    refine (hcomp.mono Set.Ico_subset_Icc_self).congr (fun t ht => ?_)
    exact (heqN t ht).symm
  -- LHS continuity: `f i` is `C∞`, hence continuous.
  have hLHS_cont : ContinuousOn (f i) (Set.Ico (0 : ℝ) T₁) :=
    (hf_smooth i).continuous.continuousOn
  -- The a.e. agreement of `f i` with `RHS` on `Ico 0 T₁`, from the forcing chain + field id.
  have hae : (f i) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico (0 : ℝ) T₁)] RHS := by

    have h1 : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)]
        (fun t => (gforce t).coeff i) := (hforce_coord i).symm

    have h2 : (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      hforce.fun_comp (fun S => S.coeff i)


    have hsub₁ : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hT₁_le
    have hsub₁F : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) d₂F :=
      Set.Icc_subset_Icc le_rfl hT₁_le_d2F
    have h1' : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (gforce t).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁F h1
    have h2' : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁ h2
    have h12 : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      h1'.trans h2'
    
    
    have h3 : (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      hfield_ae.fun_comp (fun S =>
        (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a S).coeff i)
    have hchain : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      h12.trans h3
    -- Restrict from `Icc 0 T₁` to `Ico 0 T₁`, then use `heqN` to replace by `RHS`.
    have hchain' : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self hchain
    refine hchain'.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ico] with t ht
    exact heqN t ht
  -- The a.e.→everywhere upgrade on the `Ico 0 T₁` slab.
  have heqOn : Set.EqOn (f i) RHS (Set.Ico (0 : ℝ) T₁) :=
    MeasureTheory.Measure.eqOn_Ico_of_ae_eq (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hae hLHS_cont hRHS_cont
  exact heqOn ht₀

set_option linter.unusedVariables false in
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

This is now PROVEN by the term-by-term spectral differentiation outlined above: the
arbitrary-`(x, v, w)` eigen-series identity `ccTensorBilinSymm_eigenSeries_eq`
(`SpectralPointwiseFlowDeriv.lean`, the public arbitrary-pair re-derivation of the chart-`C⁰`
spectral convergence), the per-mode derivative `perModeConv_hasDerivAt`, the closed-set
`tsum` within-derivative `hasDerivWithinAt_tsum` (fed the uniform-in-time order-`1` time-jet
mode-mass majorant `perModeConv_allOrder_timeDeriv_spectralMass_le` and the supercritical
Weyl tail `tensorEigen_summable_negpow` through AM–GM), the within-set congruence onto
`Ici 0`, and the value identity via the forcing-coordinate input
`realizedForcingCoord_eq_smoothN`, the connection-Laplacian eigen-coordinate scaling
`tensorL2Coeff_ofCompact_rawTensorConnLapSmooth`, the metric-tag transport
`ccTensorBilinSymm_toSection_congr`, and
`deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`.  The only remaining deferred input
is `realizedForcingCoord_eq_smoothN` (the pointwise a.e.→everywhere forcing-coordinate
upgrade, honest `sorry`); consumers transitively depend on its `sorryAx`. -/
private theorem realizedFamily_flowDeriv
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
    {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
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
          (by omega))).1)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)] f i) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
        (deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
        (Set.Ici 0) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc

  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  -- The per-mode time-derivative `φ i' s = f i s − λᵢ · φ i s` (`perModeConv_hasDerivAt`).
  set φ' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => f i s - TensorEigenIdx.lambda (I := I) (M := M) i * φ i s with hφ'_def
  have hφ_deriv : ∀ i (s : ℝ), HasDerivAt (φ i) (φ' i s) s := by
    intro i s
    exact perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i)
      (hf_smooth i).continuous s
  -- The all-order time-jet mode mass of `φ` on `[0,T]` (`L6`).
  have hφ_mass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    exact perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ


  have hcoeff : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) i = φ i s := by
    intro s hs i
    rw [h_pin s hs, tensorHsToL2_tensorL2Coeff]
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hid := hf_id s hs_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]


  have hu_mem : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s) := by
    intro s hs σ hσ
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (fun τ hτ => ?_) σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj⟩ := hφ_mass 0 τ hτ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hCmaj_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hCmaj i s hs_icc
      rw [iteratedDeriv_zero] at h
      rw [hcoeff s hs i]
      exact h

  have hforcing := realizedForcingCoord_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 hTT₀ hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u gforce hduh hforce htrace
    F hδ_lt hδ f hf_id hf_smooth hf_mass hforce_coord h_pin hball
  
  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by omega
  -- The Weyl tail exponent: a single fixed even order `sW` strictly above `weylSobolevExp`.
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) :=
    tensorEigen_summable_negpow (I := I) (M := M) g₀ (sW : ℝ) hsW_gt
  -- Main work: fix the time `t` and the chart-evaluation data `(x, v, w)`.
  intro t ht x v w
  -- The fixed per-mode scalar `ψ i = ccTensorBilinSymm g₀ (eigenSmooth i) x v w` and its
  -- spectral-`a` Sobolev-weight bound.
  obtain ⟨C, hC_pos, hC_bd⟩ :=
    abs_eigenBilinScalar_le (I := I) (M := M) g₀ a ha_lossy x v w
  set K : ℝ := Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- The per-mode scalar bound: `|ψ i| ≤ (C·K) · √(weight i a)`.
  have hψ_bd : ∀ i, |eigenBilinScalar (I := I) g₀ x v w i| ≤
      (C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) := by
    intro i
    have := hC_bd i
    rw [hK_def]
    calc |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) *
            (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := this
      _ = C * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) := by ring
  -- A summability engine: a `tensorSobolevWeight (a + sW)`-weighted square-summable
  -- coordinate family `c`, paired with the per-mode scalar bound, yields a summable product
  -- (AM–GM split of the order-`a` weight into `(a + sW)` and the `(-sW)` Weyl tail).
  have hprod_summable : ∀ (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
          (c i) ^ 2) →
      Summable (fun i => c i * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro c hc_sum
    -- Dominate `|c i · ψ i|` by `½·((C·K)·(weight i (a+sW)·(c i)²) + (C·K)·weight i (-sW))`.
    have hdom : Summable (fun i =>
        (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
            (c i) ^ 2)) +
          (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) :=
      ((hc_sum.mul_left (C * K)).mul_left (1 / 2)).add
        ((hweyl.mul_left (C * K)).mul_left (1 / 2))
    refine Summable.of_norm_bounded hdom (fun i => ?_)
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    -- `√(weight a) = √(weight (a+sW)) · √(weight (-sW))` (rpow additivity).
    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |c i| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |c i| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          have hAB : (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((a : ℝ) + (sW : ℝ)))) *
              Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              (C * K) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((a : ℝ) + (sW : ℝ)))) *
                Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by ring
          rw [hAB]
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ)) * (c i) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring
  -- The eigen-series summability at any time `s ∈ [0,T₁]` (coordinate family `φ · s`).
  have hsum_series : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      Summable (fun i => φ i s * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro s hs
    refine hprod_summable (fun i => φ i s) ?_
    obtain ⟨B, hB_sum, hB_le⟩ := hφ_mass 0 ((a : ℝ) + (sW : ℝ)) (by positivity)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hB_le i s hs_icc
      rwa [iteratedDeriv_zero] at h
  -- The derivative-series summability bound, UNIFORM over `s ∈ [0,T₁]` (coordinate family
  -- `φ' · s`): the order-`1` time-jet mode-mass gives a single `t`-independent majorant.
  obtain ⟨Bφ', hBφ'_sum, hBφ'_le⟩ := hφ_mass 1 ((a : ℝ) + (sW : ℝ)) (by positivity)
  -- Package the within-derivative on `Ici 0` of the smooth eigen-series `G s = ∑' φ i s · ψ i`.
  -- The per-term within-derivative and its uniform summable bound on `Ici 0 ∩ Icc 0 T₁`.
  set u_bd : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
      (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))
    with hu_bd_def
  have hu_bd_sum : Summable u_bd :=
    ((hBφ'_sum.mul_left (C * K)).mul_left (1 / 2)).add
      ((hweyl.mul_left (C * K)).mul_left (1 / 2))
  -- For `s ∈ Icc 0 T₁`, `|φ' i s · ψ i| ≤ u_bd i`.
  have hφ'_term_bd : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ‖φ' i s * eigenBilinScalar (I := I) g₀ x v w i‖ ≤ u_bd i := by
    intro i s hs
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    have hbd1 : tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (sW : ℝ)) *
        (φ' i s) ^ 2 ≤ Bφ' i := by
      have h := hBφ'_le i s hs_icc
      rwa [iteratedDeriv_one, show deriv (φ i) s = φ' i s from (hφ_deriv i s).deriv] at h
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ' i s| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |φ' i s| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((a : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
            ((a : ℝ) + (sW : ℝ)) * (φ' i s) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring
      _ ≤ (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_refl _)
          exact mul_le_mul_of_nonneg_left hbd1 hCK_nn
  -- The within-derivative of `G s = ∑' φ i s · ψ i` on the convex set `Icc 0 T₁`.
  have hG_deriv : HasDerivWithinAt
      (fun s : ℝ => ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩
    refine hasDerivWithinAt_tsum
      (f := fun i s => φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (f' := fun i s => φ' i s * eigenBilinScalar (I := I) g₀ x v w i)
      (u := u_bd) (s := Set.Icc (0 : ℝ) T₁)
      (fun i z _hz => ?_) (fun i z hz => hφ'_term_bd i z hz) hu_bd_sum
      (convex_Icc 0 T₁) ht_icc (hsum_series t ht_icc) ht_icc
    exact ((hφ_deriv i z).hasDerivWithinAt).mul_const _
  -- The eigen-series identity: `ccTensorBilinSymm g₀ (F s) x v w = ∑' φ i s · ψ i` on the slab.
  have hG_eq : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ccTensorBilinSymm (I := I) g₀ (F s) x v w =
        ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i := by
    intro s hs
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (hu_mem s hs) (F s)
      (SmoothCcTensor.toL2_apply (F s)) x v w ?_
    · rw [heig]
      exact tsum_congr (fun i => by rw [hcoeff s hs i])
    · -- summability of the coordinate eigen-series at `s`
      refine (hsum_series s hs).congr (fun i => ?_)
      rw [hcoeff s hs i]
  -- Transfer the within-`Icc 0 T₁` derivative of `G` to `ccTensorBilinSymm g₀ (F ·) x v w`,
  -- then enlarge the set from `Icc 0 T₁` to `Ici 0` (they agree on `Icc 0 T₁`, which is a
  -- `nhdsWithin (Ici 0) t`-neighborhood of `t ∈ Ico 0 T₁`).
  have hG_deriv' : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    refine hG_deriv.congr (fun s hs => hG_eq s hs) ?_
    exact hG_eq t ⟨ht.1, le_of_lt ht.2⟩
  have hIci : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Ici (0 : ℝ)) t := by
    have hmem : Set.Icc (0 : ℝ) T₁ ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hsub : Set.Ici (0 : ℝ) ∩ Set.Iio T₁ ⊆ Set.Icc (0 : ℝ) T₁ :=
        fun s hs => ⟨hs.1, le_of_lt hs.2⟩
      exact Filter.mem_of_superset
        (inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)) hsub
    exact (hG_deriv'.mono_of_mem_nhdsWithin hmem)
  -- The value identity: the differentiated series equals the intrinsic Ricci–DeTurck RHS.
  -- `φ' i t = tensorL2Coeff (toL2 R) i`, where `R` is the (re-`g₀`-tagged) Ricci–DeTurck
  -- section of the realized metric: `f i t` is the remainder coordinate (`hforcing`) and
  -- `−λᵢ · φ i t` is the connection-Laplacian coordinate (`rawTensorConnLapSmooth`); their
  -- sum is the un-cancelled RHS-section coordinate.
  have hval : (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w := by
    set gDT := tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgDT_def
    -- The un-cancelled RHS section, re-tagged to `g₀`: `R.toSection = (deTurckRHSSection
    -- g_bg gDT).toSection`.
    set R : SmoothCcTensor g₀ 0 2 :=
      { toSection := (deTurckRHSSection (I := I) g_bg gDT).toSection
        hasCompactSupport := (deTurckRHSSection (I := I) g_bg gDT).hasCompactSupport }
      with hR_def
    -- `R = deTurckSmoothRemainder g₀ g_bg (F t) + rawTensorConnLapSmooth g₀ 0 2 (F t)`
    -- (the connection Laplacian `sub_add_cancel`s the remainder's subtracted term).
    have hR_split : R = deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg (F t) hδ_lt (hδ t) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := by
      rw [deTurckSmoothRemainder]
      rw [sub_add_cancel]
    -- Coordinate identity: `φ' i t = tensorL2Coeff (toL2 R) i`.
    have hcoord : ∀ i, φ' i t =
        tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i := by
      intro i
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩
      -- `f i t = tensorL2Coeff (toL2 (deTurckSmoothRemainder …)) i` (forcing input).
      have hf_coord := hforcing t ht i
      -- `−λᵢ · φ i t = tensorL2Coeff (toL2 (rawTensorConnLapSmooth (F t))) i`.
      have hraw : tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i :=
        tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i
      rw [hcoeff t ht_icc i] at hraw
      rw [hR_split, ContinuousLinearMap.map_add, tensorL2Coeff_add, ← hf_coord, hraw, hφ'_def]
      ring
    -- The eigen-series of `R` realizes the RHS value (`R` is a smooth tensor, in all `Hˢ`).
    have hR_mem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
            SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R := by
      intro σ hσ
      refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) (fun τ _hτ => ?_) σ hσ
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ τ R hc
    -- The eigen-series summability for `R`'s coordinates: they are `φ' · t`.
    have hR_sum : Summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
        eigenBilinScalar (I := I) g₀ x v w i) := by
      refine (hprod_summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i) ?_)
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
        ((a : ℝ) + (sW : ℝ)) R hc
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) hR_mem R
      (SmoothCcTensor.toL2_apply R) x v w hR_sum
    -- `∑' φ' i t · ψ i = ∑' (coord_R i) · ψ i = ccTensorBilinSymm g₀ R x v w`.
    rw [show (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
        ∑' i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
            eigenBilinScalar (I := I) g₀ x v w i from
      tsum_congr (fun i => by rw [hcoord i])]
    rw [← heig]
    -- `ccTensorBilinSymm g₀ R x v w = ccTensorBilinSymm g_bg (deTurckRHSSectionBg …) = RHS`.
    rw [ccTensorBilinSymm_toSection_congr R (deTurckRHSSectionBg (I := I) g_bg gDT)
      (by rw [hR_def, deTurckRHSSectionBg_toSection]) x v w]
    exact deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS (I := I) g_bg gDT x v w
  rw [← hval]
  exact hIci

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

This is now PROVEN sorry-free by reduction to the per-mode-convolution small-time norm
foundation `tensorHs_smallTime_norm_le_of_perModeConv`: the smooth forcing eigen-coordinate
family `f` (from `forcingSmoothCoordsRealize`) realizes the solution-value coordinate as the
per-mode Duhamel convolution `tensorL2Coeff (tensorHsToL2 (u.toFun t)) i = perModeConv λᵢ
(f i) t`, the order-`(a+2)` spectral-mass majorant is the `(j, τ) = (0, a+2)` instance of the
all-order time-jet majorant supplied with those coordinates, and the pinned smooth
representative `W = smoothCcToTensorHs g₀ (a+2) S` (with `W.coeff i = perModeConv λᵢ (f i) t`
via `smoothCcToTensorHs_coeff` + the order-`a` pin) realizes the spectral element whose norm
the foundation bounds by `R₀` on the small-time horizon.  The remaining deferred content is
isolated in `forcingSmoothCoordsRealize`'s forcing-time-bootstrap inputs (the classical
parabolic order-`(a+2)` interior-time smoothing of the Duhamel forcing, Amann maximal
regularity / Ladyzhenskaya–Solonnikov–Uraltseva); consumers transitively depend only on
those inputs' `sorryAx`. -/
private theorem realizedSol_solField_smallnessHorizon_Ha2
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
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
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ := by
  classical
  
  
  
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, _⟩ :=
    forcingSmoothCoordsRealize (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce htrace

  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)

  obtain ⟨d₂, hd₂_pos, hd₂_le, hbound⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₂F_pos f
      (fun i => (hf_smooth i).continuous)
      (B := B) hB_sum
      (fun i s hs => by
        have h := hB_le i s hs
        rwa [iteratedDeriv_zero] at h)
      hR₀
  refine ⟨d₂, hd₂_pos, le_trans hd₂_le hd₂F_le, ?_⟩
  intro t ht S hS
  have ht_d2F : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hd₂_le⟩

  set W : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S with hW_def

  have hWcoeff : ∀ i, W.coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t := by
    intro i
    rw [hW_def, smoothCcToTensorHs_coeff, hS, ← hf_id t ht_d2F i]

  have := hbound t ht W hWcoeff
  rwa [hW_def] at this

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
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (ha_eq : a = 2 * Module.finrank ℝ E + 10)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super).choose)
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
  
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, hforce_coord⟩ :=
    forcingSmoothCoordsRealize (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce htrace

  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hφ_cont : ∀ i, Continuous (φ i) := fun i => (hφ_smooth i).continuous



  have hf_endpoint_sum : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (f i s) ^ 2) := by
    intro c hc t ht
    obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 c hc
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hB_sum.mul_left d₂F)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · -- `wt · ∫₀ᵗ (f i)² ≤ wt · ∫₀ᵀ (f i)² ≤ T · B i`
      have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i c
      have hcont_sq : Continuous (fun s => (f i s) ^ 2) := ((hf_smooth i).continuous).pow 2
      have htint : (∫ s in (0 : ℝ)..t, (f i s) ^ 2) ≤ ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hd₂F_pos.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set hcont_sq.integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      have hbig : tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 ≤ d₂F * B i := by

        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2)
            MeasureTheory.volume 0 d₂F :=
          (hcont_sq.const_mul _).intervalIntegrable 0 d₂F
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) MeasureTheory.volume 0 d₂F :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..d₂F,
              tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2
            ≤ ∫ _s in (0 : ℝ)..d₂F, B i := by
          refine intervalIntegral.integral_mono_on hd₂F_pos.le hi_lhs hi_const ?_
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        exact hmono
      calc tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..t, (f i s) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 :=
            mul_le_mul_of_nonneg_left htint hwt_nn
        _ ≤ d₂F * B i := hbig


  have hF₀_exists : ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      ∃ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht

    obtain ⟨uDuh, huDuh_coeff, huDuh_mem⟩ :=
      duhamel_into_all_tensorHs (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (t := t) ht.1 h_compact f (fun i => (hf_smooth i).continuous)
        (fun c hc => hf_endpoint_sum c hc t ht)

    have hval : uDuh = tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
      refine tensorL2_ext_of_tensorL2Coeff_jsmooth (I := I) (M := M) h_compact (fun i => ?_)
      rw [huDuh_coeff i]
      exact (hf_id t ht i).symm

    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              h_compact hσ v = uDuh := huDuh_mem
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) uDuh hmem
    refine ⟨S, ?_⟩
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = (S : TensorL2 0 2 g₀) from rfl,
      hS, hval]

  choose F₀ hF₀ using hF₀_exists
  set Fdef : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂F then F₀ t ht else 0 with hFdef_def
  have hFdef_pin : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) d₂F),
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Fdef t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    simp only [hFdef_def, dif_pos ht]
    exact hF₀ t ht
  
  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ a ha_lossy
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
    realizedSol_solField_smallnessHorizon_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ u gforce hduh hforce htrace hR₀_pos
  set T₁ : ℝ := min (min (min T (d / 2)) d₂) d₂F with hT₁_def
  have hT₁_pos : 0 < T₁ := lt_min (lt_min (lt_min hT (by positivity)) hd₂_pos) hd₂F_pos
  have hT₁_le : T₁ ≤ T :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hT₁_le_d2 : T₁ ≤ d₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hT₁_le_d2F : T₁ ≤ d₂F := min_le_right _ _
  have hT₁_le_d : T₁ ≤ d / 2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  
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
      have ht_icc_d2F : t ∈ Set.Icc (0 : ℝ) d₂F :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le_d2F⟩
      have hpin := hFdef_pin t ht_icc_d2F
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
      have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
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
  
  have hF_flow := realizedFamily_flowDeriv (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
    hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u gforce hduh hforce htrace F hδ_lt hF_small hF_zero
    hF_pin hF_cont hball f hf_smooth hf_mass hf_id hforce_coord




  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hF_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]


  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
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
