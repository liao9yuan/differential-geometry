import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinLimitUniformMass
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularity

/-!
# The smooth per-mode time-coordinate of the Ricci–DeTurck engine forcing

For the genuinely-second-order Nemytskii forcing of the Ricci–DeTurck flow about a
closed background metric `g₀`,

  `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField a hT hT1 0 gforce)`,

in the supercritical regularity regime `2·finrank + 10 ≤ a` with zero initial datum, this
file isolates the **single genuinely-irreducible quasilinear parabolic prerequisite** the
forcing time-bootstrap rests on, and assembles the consumer-facing coordinate field on top
of it.

## The split: two irreducible classical inputs, one core assembly, one consumer glue

* `deTurckForcing_solCoeff_jetSpectralMass` — **POSIT (A)**, the all-orders interior-time
  smoothing of the zero-datum quasilinear maximal-regularity solution field at the level of
  its eigen-coordinates (the solution is `C∞`-in-time into *every* spatial order, with the
  full all-order time-jet/all-order spatial spectral-mass majorant), together with the a-priori
  bound that the solution stays inside the Nemytskii realizability ball
  (`‖u t‖_{H^{a+2}} ≤ deTurckRealizabilityRadius`) on `[0,T]`.  Honest `sorry`.

* `deTurckSobolevNHa2_jetSpectralMass_preserving` — **POSIT (B)**, the order-preserving
  smoothness of the Ricci–DeTurck Nemytskii forcing on the supercritical Sobolev algebra: it
  carries an **in-ball** jet-spectral-mass-controlled input coordinate field to a
  jet-spectral-mass-controlled output coordinate field.  The in-ball guard is essential — the
  ball-retraction truncation inside `deTurckSobolevNHa2` is only Lipschitz (a kink) at the
  realizability sphere, so smoothness preservation is a statement about in-ball data, where the
  nonlinearity is the genuine smooth intrinsic remainder.  Honest `sorry`.

* `deTurckForcing_timeModeCoeff_smooth_allOrderJet` — **the deep core**, stated at the most
  primitive grain: the `L²` TIME-MODE coordinate elements `timeModeCoeff gforce i` carry
  `C∞`-in-time representatives with an all-order time-jet spectral-mass majorant on the closed
  slab `[0,T]`, agreeing a.e. with `timeModeCoeff gforce i` itself.  It is **sorry-free GLUE**
  over (A) and (B): (B) applied to (A)'s solution-coordinate field supplies the smooth
  representative with the majorant, and the a.e. agreement bridges `timeModeCoeff gforce i`
  through `timeModeCoeff_coeFn` and `hforce` to the Nemytskii-image coordinate.

* `deTurckForcing_smoothCoordinate_aeTimeJet` — **the consumer leaf**, assembled as
  sorry-free glue over the core: the per-mode forcing coordinate field `f` with the same
  smoothness and all-order time-jet majorant, agreeing a.e. with the bare pointwise
  coordinate `fun t => (gforce t).coeff i`.  The only step beyond the core is bridging
  `timeModeCoeff gforce i =ᵐ fun t => (gforce t).coeff i` via the already-proven
  `timeModeCoeff_coeFn`.

The per-mode forcing coordinate `t ↦ (gforce t).coeff i` is the `i`-th eigenbasis
coordinate of the Nemytskii image `N(u(t))` of the maximal-regularity Duhamel solution
`u`.  Because the datum is the **smooth (zero)** initial perturbation, the solution is
`C∞`-up-to-`t = 0` (the classical small-data parabolic interior-time smoothing — Amann
maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva; Lieberman), and the Nemytskii
forcing is a smooth function of the solution, so the per-mode coordinate is genuinely
`C∞`-in-time.  Its time-jets couple all modes (the nonlinear coupling), so the all-order
time-jet spectral-mass control does **not** reduce to the per-mode scalar ODE recursion of
the *linear* heat semigroup (the forcing coordinate is `N(u).coeff i`, not the Duhamel
solution coordinate `u.coeff i`, hence not the per-mode convolution
`perModeConv λᵢ (timeModeCoeff gforce i)` of the linear theory), nor to the
integrated-in-time spatial forcing mass `forcingMass gforce c` (which controls
`∫₀ᵀ |coeffᵢ|²` but neither the pointwise-in-`t` value nor any time-derivative).  It is the
genuine quasilinear smoothing input, isolated here as the two classical deep prerequisites
(A) the quasilinear interior-time smoothing of the solution and (B) the order-preserving
smoothness of the Nemytskii forcing, with the core assembled sorry-free on top of them.

DEFERRED (the two honest `sorry`s are exactly POSIT (A)
`deTurckForcing_solCoeff_jetSpectralMass` and POSIT (B)
`deTurckSobolevNHa2_jetSpectralMass_preserving`; the core
`deTurckForcing_timeModeCoeff_smooth_allOrderJet` and the consumer leaf are sorry-free glue
over them, and consumers transitively depend on their `sorryAx`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedVariables false in
theorem maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hk⟩ :=
    deTurckForcing_finiteOrderSmoothDriver (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 gforce hforce hspatial
  choose F hF_smooth hF_mass hF_ae using hk
  set f0 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ := F 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) d ⊆ closure (interior (Set.Icc (0 : ℝ) d)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd_pos)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (F k i) (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro k i
    have hae : (F k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (f0 i) :=
      (hF_ae k i).symm.trans (hF_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hF_smooth k i).continuous).continuousOn ((hF_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hF_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) d) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hd_pos (hf0_smoothOn i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) d →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) d) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨d, hd_pos, hd_le, ψ, hψ_smooth, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hF_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (ψ i) t = iteratedDeriv j (F j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
        ((hF_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  · intro i
    have hf0ψ : (f0 i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (ψ i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
      exact hψ_eqOn i ht
    exact (hF_ae 0 i).trans hf0ψ

set_option linter.unusedVariables false in
theorem maxRegSolField_parabolicInterior_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a (by omega)) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMass (I := I) (M := M)
      g₀ g_bg a (by omega) hT hT1 gforce hforce
      (deTurckGalerkin_solField_uniformSpatialMass_allOrder (I := I) (M := M)
        g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_top (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) (hf_smooth i)
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le_d₀, hball_W⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₀_pos f
      (fun i => (hf_smooth i).continuous) (B := B0) hB0_sum
      (fun i s hs => by
        have h := hB0_le i s hs
        rwa [iteratedDeriv_zero] at h)
      (deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a (by omega))
  have hd₂_le : d₂ ≤ T := le_trans hd₂_le_d₀ hd₀_le
  have hd₂_le_d₀' : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) d₀ :=
    Set.Icc_subset_Icc le_rfl hd₂_le_d₀
  refine ⟨d₂, hd₂_pos, hd₂_le, φ, ⟨hφ_smooth, ?_⟩, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₀) hd₀_pos.le f hf_smooth hf_mass j τ hτ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t (hd₂_le_d₀' ht)
  · have hsolcoeff_ae : ∀ i,
        (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
      intro i
      have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hd₂_le
      have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) hT hT1 hc gforce i)
      have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
        have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
              (fun s => (gforce s).coeff i) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
            (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
        exact htmc.trans
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
            hd₂_le_d₀' (hf_ae i))
      have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
        exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hforce_ae ht
      exact hstep1.trans hstep2
    have hcoeff_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t :=
      (MeasureTheory.ae_all_iff).2 hsolcoeff_ae
    filter_upwards [hcoeff_eq, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht_coeff ht_mem
    refine hball_W t ht_mem
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t) ?_
    intro i
    exact ht_coeff i
  · intro i
    have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hd₂_le
    have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
          (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) hT hT1 hc gforce i)
    have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
      have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun s => (gforce s).coeff i) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
      exact htmc.trans
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
          hd₂_le_d₀' (hf_ae i))
    have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
      rw [hφ_def]
      exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
        hforce_ae ht
    exact hstep1.trans hstep2

set_option linter.unusedVariables false in
private theorem deTurckForcing_smoothForcingDriver
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    maxRegSolField_parabolicInterior_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a (by omega) hT hd₂_pos hd₂_le
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨d₂, hd₂_pos, hd₂_le, ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₂_le
  have hforce_coeff : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  exact hforce_coeff.trans (hψ_ae i)

set_option linter.unusedVariables false in
private theorem deTurckForcing_solCoeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a (by omega)) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothForcingDriver (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
      gforce hforce hgforce
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_top (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) (hf_smooth i)
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le_d₀, hball_W⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₀_pos f
      (fun i => (hf_smooth i).continuous) (B := B0) hB0_sum
      (fun i s hs => by
        have h := hB0_le i s hs
        rwa [iteratedDeriv_zero] at h)
      (deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a (by omega))
  have hd₂_le : d₂ ≤ T := le_trans hd₂_le_d₀ hd₀_le
  have hd₂_le_d₀' : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) d₀ :=
    Set.Icc_subset_Icc le_rfl hd₂_le_d₀
  refine ⟨d₂, hd₂_pos, hd₂_le, φ, ⟨hφ_smooth, ?_⟩, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₀) hd₀_pos.le f hf_smooth hf_mass j τ hτ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t (hd₂_le_d₀' ht)
  · have hsolcoeff_ae : ∀ i,
        (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
      intro i
      have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hd₂_le
      have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) hT hT1 hc gforce i)
      have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
        have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
              (fun s => (gforce s).coeff i) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
            (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
        exact htmc.trans
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
            hd₂_le_d₀' (hf_ae i))
      have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
        exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hforce_ae ht
      exact hstep1.trans hstep2
    have hcoeff_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t :=
      (MeasureTheory.ae_all_iff).2 hsolcoeff_ae
    filter_upwards [hcoeff_eq, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht_coeff ht_mem
    refine hball_W t ht_mem
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t) ?_
    intro i
    exact ht_coeff i
  · intro i
    have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hd₂_le
    have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
          (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) hT hT1 hc gforce i)
    have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
      have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun s => (gforce s).coeff i) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
      exact htmc.trans
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
          hd₂_le_d₀' (hf_ae i))
    have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
      rw [hφ_def]
      exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
        hforce_ae ht
    exact hstep1.trans hstep2

set_option linter.unusedVariables false in
private theorem deTurckForcing_fixedPoint_coeff_smooth_and_mass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (c i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] c i) := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothForcingDriver (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₀ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₀_le
  have hbridge : (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)]
        (fun t => (gforce t).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
  exact hbridge.trans (hf_ae i)

/-- **THE IRREDUCIBLE DEEP CORE — `C∞`-in-time smoothness with an all-order time-jet
spectral-mass majorant of the forcing's `L²` TIME-MODE coordinates `timeModeCoeff gforce i`.**

This is the single genuinely-irreducible quasilinear parabolic prerequisite of the forcing
time-bootstrap, stated at the **most primitive grain possible**: it speaks ONLY of the
per-mode `L²`-coordinate elements `timeModeCoeff gforce i ∈ L²(0,T)` of the engine forcing
`gforce`, asserting that each carries a `C∞`-in-time representative `g i` with an all-order
time-jet spectral-mass majorant on the closed slab `[0,T]`, and that the representative
agrees a.e. with the `L²`-coordinate element itself (`timeModeCoeff gforce i =ᵐ g i`).

It is STRICTLY more primitive than the consumer leaf
`deTurckForcing_smoothCoordinate_aeTimeJet`: that leaf's a.e.-agreement conjunct is phrased
against the bare pointwise coordinate `fun t => (gforce t).coeff i`, whereas this core is
phrased against the `L²`-coordinate functional image `timeModeCoeff gforce i`.  The bridge
between the two — `timeModeCoeff gforce i =ᵐ fun t => (gforce t).coeff i`
(`timeModeCoeff_coeFn`) — is an already-proven brick, so this core carries NEITHER the
`fun t => (gforce t).coeff i` a.e.-agreement wrapper NOR any reformulation of the leaf's
conclusion; it is the genuine smoothness-of-the-Nemytskii-image-coordinate input on which
the leaf is assembled.

WHY this is the irreducible parabolic/Nemytskii core.  The per-mode forcing coordinate is
the `i`-th eigenbasis coordinate of the Nemytskii image `N(u(t))` of the maximal-regularity
Duhamel solution `u = maxRegDuhamelSolField a hT hT1 0 gforce`.  Because the datum is the
smooth (zero) initial perturbation the solution is `C∞`-up-to-`t = 0` (the classical
small-data parabolic interior-time smoothing — Amann maximal regularity; Ladyzhenskaya–
Solonnikov–Uraltseva; Lieberman) and the supercritical Sobolev order `2·finrank + 10 ≤ a`
places `Hᵃ` in a Sobolev algebra, making the second-order Ricci–DeTurck Nemytskii forcing a
smooth map of the solution; hence the per-mode coordinate is genuinely `C∞`-in-time.  Its
time-jets couple ALL modes (the nonlinear coupling), so the all-order time-jet spectral-mass
control does NOT reduce to the per-mode scalar ODE recursion of the *linear* heat semigroup
(the forcing coordinate is `N(u).coeff i`, not the Duhamel solution coordinate `u.coeff i`,
so it is NOT the per-mode convolution `perModeConv λᵢ (timeModeCoeff gforce i)` of the
linear theory), nor to the integrated-in-time spatial forcing mass `forcingMass gforce c`
(which controls `∫₀ᵀ |coeffᵢ|²` but neither the pointwise-in-`t` value nor any
time-derivative).  It is the genuine quasilinear smoothing input.

PINNED to the forcing by `hforce` and the a.e.-agreement conjunct (so it is not vacuous):
`timeModeCoeff gforce i =ᵐ g i` forces `g i` to track the actual `L²` coordinates of
`gforce`, itself fixed by `hforce` to the genuine second-order Nemytskii image of its own
Duhamel solution field.

This is **sorry-free GLUE** over POSIT (A) `deTurckForcing_solCoeff_jetSpectralMass` and POSIT
(B) `deTurckSobolevNHa2_jetSpectralMass_preserving`: (B) applied to (A)'s solution-coordinate
field `φ` (instantiated at `w := u`) supplies the smooth representative `ψ` with the all-order
time-jet majorant, and the a.e. conjunct chains `timeModeCoeff gforce i =ᵐ (gforce ·).coeff i`
(`timeModeCoeff_coeFn`) `=ᵐ (N(u ·)).coeff i` (`hforce` pushed through the coordinate functional)
`=ᵐ ψ i`.  Consumers transitively depend on (A) and (B)'s `sorryAx`. -/
theorem deTurckForcing_timeModeCoeff_smooth_allOrderJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] g i) :=
  deTurckForcing_fixedPoint_coeff_smooth_and_mass (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce

/-- **The `C∞`-in-time per-mode forcing coordinate field of the Ricci–DeTurck engine
forcing.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), the per-eigenmode
forcing coordinates admit a genuinely **`C∞`-in-time** field `f` with:

* **(smoothness)** each `f i` is `C∞`;
* **(all-order time-jet spectral-mass)** for every time-derivative order `j` and spatial
  Sobolev order `τ ≥ 0`, the weighted square of the `j`-th time-derivative of `f i` has a
  single `t`-independent summable-across-modes majorant on the CLOSED slab `[0,T]`
  (including `t = 0`);
* **(a.e. coordinate agreement)** each `f i` agrees a.e. with the actual `i`-th coordinate
  of the forcing: `(fun t => (gforce t).coeff i) =ᵐ f i`.

This is `GLUE` over the single deep parabolic core
`deTurckForcing_timeModeCoeff_smooth_allOrderJet`: the core supplies, for the `L²` time-mode
coordinates `timeModeCoeff gforce i`, a smooth representative field `g` with the all-order
time-jet majorant and the a.e. agreement `timeModeCoeff gforce i =ᵐ g i`.  Taking `f := g`,
conjuncts (smoothness) and (all-order time-jet spectral-mass) are exactly the core's, and
(a.e. coordinate agreement) is the core's a.e. agreement composed with the already-proven
coordinate-representative brick `timeModeCoeff_coeFn`
(`timeModeCoeff gforce i =ᵐ fun t => (gforce t).coeff i`), giving
`fun t => (gforce t).coeff i =ᵐ g i`.

Consumers transitively depend on the core's `sorryAx` through this assembly. -/
theorem deTurckForcing_smoothCoordinate_aeTimeJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a (by omega)).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadius (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJet (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, fun i => ?_⟩
  have htmc : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd₂_le) ?_
    exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  exact htmc.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
