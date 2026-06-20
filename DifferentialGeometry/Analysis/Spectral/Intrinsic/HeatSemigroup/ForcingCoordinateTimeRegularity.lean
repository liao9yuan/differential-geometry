import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet

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

/-- **The all-order time-jet spectral-mass control of a per-mode time-coordinate family.**

A coordinate family `φ : TensorEigenIdx g₀ 0 2 → ℝ → ℝ` (the per-eigenmode time-coordinates
of a tensor-valued time field) is *jet-spectral-mass controlled* on `[0,T]` when

* each `φ i` is `C∞`-in-time, and
* for every time-derivative order `j` and every spatial Sobolev order `τ ≥ 0`, the weighted
  square `tensorSobolevWeight i τ · (∂ₜʲ(φ i) t)²` has a single `t`-independent
  summable-across-modes majorant on the closed slab `[0,T]`.

This is exactly the hypothesis shape consumed by `perModeConv_allOrder_timeDeriv_spectralMass_le`
on the forcing side, and exactly the conclusion shape of the deep core; isolating it as a named
predicate lets the two genuinely-irreducible parabolic/Nemytskii inputs and the core's assembly
speak the same language. -/
private def JetSpectralMassControl
    (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (φ i)) ∧
    (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)

/-- **The realizability radius of the Ricci–DeTurck Nemytskii forcing.**

The `H^{a+2}`-norm radius `R₀` of the realizability ball selected inside `deTurckSobolevNHa2`
(the radius produced by `deTurckSobolevNHa2_exists_of_super`): on `H^{a+2}`-data of norm `≤ R₀`
the truncation/recentred-ball-retraction inside `deTurckSobolevNHa2` is the identity and the
nonlinearity equals the genuine smooth intrinsic remainder `deTurckSmoothN`
(`deTurckSobolevNHa2_eq_smoothN`).  Inputs straying outside this ball are radially truncated,
which only Lipschitz-projects them onto the sphere and breaks smoothness at the boundary — so the
order-preserving smoothness of the forcing (POSIT (B)) is a statement about **in-ball** data, and
the solution field fed to it (POSIT (A)) must be certified to remain in this ball. -/
private noncomputable def deTurckRealizabilityRadius
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

/-- The realizability radius is strictly positive. -/
private theorem deTurckRealizabilityRadius_pos
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    0 < deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super :=
  (Classical.choose_spec
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

/-- **POSIT (A) — all-orders interior-time smoothing of the zero-datum quasilinear
maximal-regularity solution field, at the level of its eigen-coordinates.**

For the `H^{a+2}`-valued maximal-regularity Duhamel solution field
`u = maxRegDuhamelSolField (a : ℝ) hT hT1 0 gforce` of the zero-datum quasilinear Ricci–DeTurck
forcing problem (`gforce` pinned to its own Nemytskii image by `hforce`), the per-eigenmode
time-coordinate family `i ↦ (t ↦ (u t).coeff i)` carries a `C∞`-in-time representative `φ` that
is jet-spectral-mass controlled on `[0,T]` — i.e. `u` is `C∞`-in-time into **every** spatial
order `Hᵗ` (not merely `H^{a+2}`), uniformly up to `t = 0`, with the full all-order
time-jet/all-order spatial spectral-mass majorant.  It additionally certifies that the solution
field stays inside the Nemytskii **realizability ball** on `[0,T]`
(`‖u t‖_{H^{a+2}} ≤ deTurckRealizabilityRadius`), the in-ball guard the order-preserving Nemytskii
smoothness (POSIT (B)) requires of its input — a genuine a-priori bound on the small-time
zero-datum quasilinear solution, supplied by the same fixed-point construction that produces it.

WHY this is genuinely irreducible.  This is the all-orders **parabolic interior smoothing** of a
zero-datum quasilinear solution: the smooth (zero) initial perturbation makes the solution
`C∞`-up-to-`t = 0`, lying in `⋂_τ Hᵗ` in the interior, with every time-derivative spatially
controlled summably across modes.  The supercritical order `2·finrank + 10 ≤ a` places `Hᵃ` in a
Sobolev algebra, the regime in which the Amann / Ladyzhenskaya–Solonnikov–Uraltseva / Lieberman
quasilinear-parabolic bootstrap closes.  The **linear** template is
`solField_into_all_tensorHs_interior` (`ParabolicInteriorSmoothing.lean`), which supplies the
order-`σ` *spatial* summability of the maximal-regularity field at every `σ` from the base
regularity plus the first-order coupling; this posit is its genuinely **quasilinear / all-order
time-jet** strengthening (the nonlinear coupling of the modes through the Nemytskii fixed point
forbids reducing it to the per-mode scalar ODE recursion of the linear theory).

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
private theorem deTurckForcing_solCoeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ T ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[timeMeasure T] φ i :=
  sorry

set_option linter.unusedVariables false in
private theorem deTurckRemainder_path_timeJet_section
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiff ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDeriv j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j q : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ K) := by
  classical
  obtain ⟨Rjet, hsmooth, hjet, hmass⟩ :=
    deTurckRemainder_path_coeff_timeJet_withMass (I := I) (M := M)
      g₀ g_bg hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  refine ⟨Rjet, hsmooth, hjet, ?_⟩
  intro j q
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q ≤ 2 * k := ⟨q, by omega⟩
  set σ' : ℝ := ((2 * k : ℕ) : ℝ) with hσ'_def
  have hσ'_nn : (0 : ℝ) ≤ σ' := by rw [hσ'_def]; positivity
  obtain ⟨B, hB_sum, hBle⟩ := hmass j σ' hσ'_nn
  obtain ⟨Csum, hCsum_nn, hCsum⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ k
  have hBtsum_nn : 0 ≤ ∑' i, B i :=
    tsum_nonneg (fun i =>
      le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ') (sq_nonneg _))
        (hBle i 0 ⟨le_rfl, hT.le⟩))
  refine ⟨Csum * Real.sqrt (∑' i, B i), by positivity, ?_⟩
  intro t ht
  set N : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hNsq_le : N ^ 2 ≤ ∑' i, B i := by
    have heq : N ^ 2 = ∑' i, tensorSobolevWeight (I := I) (M := M) i σ' *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).coeff i) ^ 2 := by
      rw [hN_def, tensorHs.norm_sq_eq_tsum]
    rw [heq]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable) hB_sum
    rw [smoothCcToTensorHs_coeff]
    exact hBle i t ht
  have hN_le : N ≤ Real.sqrt (∑' i, B i) := by
    rw [← Real.sqrt_sq hN_nn]
    exact Real.sqrt_le_sqrt hNsq_le
  have hcovsum := hCsum (Rjet j t)
  have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤
      ∑ j' ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ :=
    Finset.single_le_sum
      (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖)
      (fun j' _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖
      ≤ ∑ j' ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j' (Rjet j t)‖ := hsingle
    _ ≤ Csum * N := by rw [hN_def]; exact hcovsum
    _ ≤ Csum * Real.sqrt (∑' i, B i) :=
        mul_le_mul_of_nonneg_left hN_le hCsum_nn

private theorem deTurckSmoothN_path_coeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ T ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
          (deTurckSmoothN (I := I) (M := M) g₀ g_bg a (F t) hδ_lt (hδ t)).coeff i = ψ i t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set Rem : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t) with hRem_def
  set ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rem t)) i with hψ_def
  obtain ⟨Rjet, hsmooth, hjet, hcovbnd⟩ :=
    deTurckRemainder_path_timeJet_section (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT F hδ_lt hδ φ hφ_smooth hcoeff hmodemass
  refine ⟨ψ, ⟨fun i => hsmooth i, ?_⟩, ?_⟩
  · intro j σ hσ
    obtain ⟨k, hk⟩ : ∃ k : ℕ, σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) ≤ (2 * k : ℕ) := by
      obtain ⟨k, hk⟩ := exists_nat_gt
        (σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1))
      exact ⟨k, by push_cast; linarith⟩
    set σ' : ℝ := ((2 * k : ℕ) : ℝ) with hσ'_def
    have hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by
      rw [hσ'_def]; linarith
    obtain ⟨C, hC_nn, hCle⟩ :=
      exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ k
    have hcovsum_bnd : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ≤ K := by
      have hbnds : ∀ q ∈ Finset.range (2 * k + 1), ∃ Kq : ℝ, 0 ≤ Kq ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q (Rjet j t)‖ ≤ Kq :=
        fun q _ => hcovbnd j q
      choose! Kq hKq_nn hKq using hbnds
      refine ⟨C * ∑ q ∈ Finset.range (2 * k + 1), Kq q,
        mul_nonneg hC_nn (Finset.sum_nonneg (fun q hq => hKq_nn q hq)), ?_⟩
      intro t ht
      refine le_trans (hCle (Rjet j t)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hC_nn
      refine Finset.sum_le_sum (fun q hq => ?_)
      exact hKq q hq t ht
    obtain ⟨K, hK_nn, hKle⟩ := hcovsum_bnd
    refine ⟨fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2,
      ?_, ?_⟩
    · exact (tensorEigen_summable_negpow (I := I) (M := M) g₀ (σ' - σ) hσσ').mul_right (K ^ 2)
    · intro i t ht
      rw [hjet j i t ht]
      set u : ℝ := tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i with hu_def
      have hcoeff_eq : (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).coeff i = u := by
        rw [smoothCcToTensorHs_coeff]
      have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
      have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
          tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
            tensorSobolevWeight (I := I) (M := M) i σ' := by
        unfold tensorSobolevWeight
        rw [← Real.rpow_add hbase, show -(σ' - σ) + σ' = σ from by ring]
      have hterm_le : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤ K ^ 2 := by
        have hmass : tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2 ≤
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ ^ 2 := by
          rw [tensorHs.norm_sq_eq_tsum]
          have hsummable := (smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)).weighted_summable
          have hle := hsummable.le_tsum i (fun i' _ =>
            mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i' σ') (sq_nonneg _))
          rw [hcoeff_eq] at hle
          exact hle
        refine le_trans hmass ?_
        have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ' (Rjet j t)‖ := norm_nonneg _
        have := hKle t ht
        nlinarith [this, hnn, hK_nn]
      calc tensorSobolevWeight (I := I) (M := M) i σ * u ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) *
              (tensorSobolevWeight (I := I) (M := M) i σ' * u ^ 2) := by rw [hsplit]; ring
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) * K ^ 2 :=
            mul_le_mul_of_nonneg_left hterm_le
              (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  · intro t ht i
    rw [deTurckSmoothN_coeff]

private theorem deTurckSobolevNHa2_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ T)
    (hw : ∀ i, (fun t => (w t).coeff i) =ᵐ[timeMeasure T] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ T ∧
        ∀ i, (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
            =ᵐ[timeMeasure T] ψ i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set R₀ : ℝ := deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super with hR₀_def
  have hR₀_pos : 0 < R₀ := deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a ha_super
  obtain ⟨hφ_smooth, hφ_mass⟩ := hφ
  have hmass0 : ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have := hBle i t ht
    rwa [iteratedDeriv_zero] at this
  have hsum_pt : ∀ t, t ∈ Set.Icc (0 : ℝ) T →
      ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2) := by
    intro t ht σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => hBle i t ht) hBs
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  set ct : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => φ i t with hct_def
  have hreconstruct : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = φ i t := by
    intro t ht
    obtain ⟨B0, hB0s, hB0le⟩ := hmass0 0 le_rfl
    set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
      tensorHs_of_spectralMass_majorant (I := I) (M := M) (ct t) B0 hB0s
        (fun i => by
          have := hB0le i t ht
          simpa [hct_def] using this) with hv0_def
    set u : TensorL2 0 2 g₀ :=
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
    have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = φ i t := by
      intro i
      rw [hu_def, tensorHsToL2_tensorL2Coeff]
      simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff, hct_def]
    have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
      intro σ hσ
      refine (hsum_pt t ht σ hσ).congr (fun i => ?_)
      rw [hu_coeff i]
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
      allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
    refine ⟨S, fun i => ?_⟩
    have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
      rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
          = (S : TensorL2 0 2 g₀) from rfl, hS]
    rw [hSL2, hu_coeff i]
  choose! S₀ hS₀ using hreconstruct
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) T then S₀ t else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    simp only [hF_def, ht, if_pos]
    exact hS₀ t ht i
  have hF_smoothCc_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T) := by
    set σ : ℝ := (a : ℝ) + 2 with hσ_def
    set σ' : ℝ := σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) with hσ'_def
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0 σ' (by
      rw [hσ'_def, hσ_def]; positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀
      (σ := σ) (σ' := σ') ?_ (s := Set.Icc (0 : ℝ) T)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ
      hF_smoothCc_coeff (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have : σ' - σ = ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by rw [hσ'_def]; ring
    rw [this]; linarith
  have hball_ae : ∀ᵐ t ∂(timeMeasure T),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_all : ∀ᵐ t ∂(timeMeasure T), ∀ i, (w t).coeff i = φ i t :=
      MeasureTheory.ae_all_iff.mpr (fun i => hw i)
    have hae_mem : ∀ᵐ t ∂(timeMeasure T), t ∈ Set.Icc (0 : ℝ) T := by
      rw [timeMeasure, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact MeasureTheory.ae_of_all _ (fun t ht => ht)
    filter_upwards [hae_all, hae_mem] with t htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) = w t := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [hF_smoothCc_coeff t htmem i, ← htall i]
    rw [heq]; exact hw_ball t htmem
  have hcont_norm : ContinuousOn
      (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖)
      (Set.Icc (0 : ℝ) T) := continuous_norm.comp_continuousOn hfield_cont
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    have hae_le : ∀ᵐ s ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T)),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ≤ R₀ := by
      have := hball_ae; rwa [timeMeasure] at this
    have hg_cont : ContinuousOn
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀)
        (Set.Icc (0 : ℝ) T) := hcont_norm.inf continuousOn_const
    have hfg : (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T)]
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F s)‖ ⊓ R₀) := by
      filter_upwards [hae_le] with s hs
      exact (min_eq_left hs).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hT) hfg hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ⊓ R₀ := heq ht
    rw [hmin]; exact inf_le_right
  obtain ⟨δ, hδ_lt, hδ_all⟩ :
      ∃ δ : ℝ, δ < 1 ∧ ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (F t)) δ := by
    obtain ⟨hp_pos, hp_lt, hp_ball⟩ := Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)
    have hsmoothZero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h0 : (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2) :=
        (zero_smul ℝ _).symm
      rw [h0, smoothCcToTensorHs_smul, zero_smul]
    refine ⟨(Classical.choose (deTurckSobolevNHa2_exists_of_super
      (I := I) (M := M) g₀ a ha_super)).2, hp_lt, fun t => ?_⟩
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · exact hp_ball (F t) (hball_pt t ht)
    · have hF0 : F t = 0 := by simp only [hF_def, ht, if_neg, not_false_iff]
      refine hp_ball (F t) ?_
      rw [hF0, hsmoothZero, norm_zero]
      exact hp_pos.le
  obtain ⟨ψ, hψ_ctrl, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT F hδ_lt hδ_all φ hφ_smooth
      hF_coeff hφ_mass
  refine ⟨ψ, hψ_ctrl, fun i => ?_⟩
  have hae_all : ∀ᵐ t ∂(timeMeasure T), ∀ j, (w t).coeff j = φ j t :=
    MeasureTheory.ae_all_iff.mpr (fun j => hw j)
  have hae_mem : ∀ᵐ t ∂(timeMeasure T), t ∈ Set.Icc (0 : ℝ) T := by
    rw [timeMeasure, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact MeasureTheory.ae_of_all _ (fun t ht => ht)
  filter_upwards [hae_all, hae_mem] with t htall htmem
  have hwF : w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, ← hF_smoothCc_coeff t htmem j]
  rw [hwF,
    deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super ha_even
      (F t) hδ_lt (hδ_all t) (by
        have hle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ :=
          hball_pt t htmem
        have hpf : (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1 = R₀ := rfl
        rw [hpf]; exact hle)]
  exact hψ_coeff t htmem i

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
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[timeMeasure T] g i) := by
  obtain ⟨φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    deTurckForcing_solCoeff_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT hT1 hTT₀ gforce hforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hforce_coeff :
      (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    hforce.fun_comp (fun w => w.coeff i)
  exact ((timeModeCoeff_coeFn (I := I) (M := M) gforce i).trans hforce_coeff).trans (hψ_ae i)

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
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T] f i) := by
  obtain ⟨g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJet (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT hT1 hTT₀ gforce hforce
  refine ⟨g, hg_smooth, hg_mass, fun i => ?_⟩
  exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
