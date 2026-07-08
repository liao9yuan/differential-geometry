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

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
