import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

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

/-- **POSIT (B) — the Ricci–DeTurck Nemytskii forcing carries an all-orders-smooth input field to
an all-orders-smooth output field, at the level of eigen-coordinates.**

For the total continuous quasilinear Ricci–DeTurck nonlinearity
`N = deTurckSobolevNHa2 g₀ g_bg a : H^{a+2} → Hᵃ` in the supercritical regime
`2·finrank + 10 ≤ a` (so `H^{a+2}` is a Sobolev algebra), and any `H^{a+2}`-valued time field
`w : ℝ → H^{a+2}` that (i) stays inside the Nemytskii **realizability ball** on `[0,T]`
(`hw_ball : ‖w t‖ ≤ deTurckRealizabilityRadius`) and (ii) whose per-eigenmode coordinate family
`i ↦ (t ↦ (w t).coeff i)` is jet-spectral-mass controlled on `[0,T]` (via a `C∞` representative
`φ`), the per-eigenmode coordinate family of the composed forcing `i ↦ (t ↦ (N (w t)).coeff i)`
is again jet-spectral-mass controlled on `[0,T]` (via a `C∞` representative `ψ` that represents
the forcing coordinate a.e.).

The in-ball guard `hw_ball` is **essential and not vacuous**: `deTurckSobolevNHa2` is defined by a
dense-Lipschitz extension composed with a recentred radial **ball retraction**
(`recenteredBallRetraction 0 R₀`); on data straying outside the realizability ball that retraction
is the radial projection onto the sphere, which is only Lipschitz, not `C¹`, at the boundary — so
without `hw_ball` a smooth-in-time `w` crossing the realizability sphere would make
`t ↦ (N (w t)).coeff i` merely continuous (a kink), contradicting the `C∞` representative the
conclusion demands.  On in-ball data the retraction is the identity and `N` equals the genuine
smooth intrinsic remainder `deTurckSmoothN` (`deTurckSobolevNHa2_eq_smoothN`), which is the regime
in which order-preserving smoothness holds.  This is the same in-ball / fibre-small validity-domain
hypothesis the rest of the cluster carries (`deTurckSmoothN_ballLipschitz_Ha2`,
`deTurckSobolevNHa2_eq_smoothN`, `sobolevBall_smooth_fibreSmall`).

This is the consumer-minimal form actually needed by the assembly: not the bare
`ContDiff ℝ ∞` of `N` as a Banach map `H^{a+2} → Hᵃ`, but the **order-preserving** statement that
`N` pushes an in-ball all-orders-smooth (every-`Hᵗ`, all-time-jet) input through to an
all-orders-smooth output with the time-jet/spectral-mass control intact — exactly what the chain
rule plus the majorant assembly transports across the composition.

WHY this is genuinely irreducible.  This is the smoothness and all-order regularity-preservation
of a **superposition (Nemytskii) operator** on the supercritical Sobolev algebra `H^{a+2}`: on the
realizability ball the second-order intrinsic Ricci–DeTurck remainder `deTurckSmoothN` is a smooth
fibrewise-polynomial expression in the metric perturbation and its first two covariant derivatives,
so on the algebra `H^{a+2}` (supercritical `a`, hence `H^{a+2} ↪ C²`) it is a smooth map preserving
membership in every higher Sobolev order, with derivative/jet bounds tame in the input regularity
(the Moser / Schauder-ring estimates for products and compositions in a Sobolev algebra).

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
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
            =ᵐ[timeMeasure T] ψ i :=
  sorry

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
      g₀ g_bg a ha_super ha_even hT hT1 gforce hforce
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
      g₀ g_bg a ha_super ha_even hT hT1 gforce hforce
  refine ⟨g, hg_smooth, hg_mass, fun i => ?_⟩
  exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
