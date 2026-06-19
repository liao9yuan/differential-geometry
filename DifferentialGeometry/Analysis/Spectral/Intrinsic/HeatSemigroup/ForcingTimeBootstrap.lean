import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

/-!
# The parabolic time-bootstrap of the Ricci–DeTurck engine forcing

For the genuinely-second-order Nemytskii forcing of the Ricci–DeTurck flow about a
closed background metric `g₀`,

  `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField a hT hT1 0 gforce)`,

in the supercritical regularity regime `2·finrank + 10 ≤ a` with zero initial datum, this
file isolates the two genuine classical parabolic prerequisites behind the joint
`C∞`-up-to-`t = 0` regularity of the realized DeTurck–Ricci solution family.

## The two analytic inputs

* `deTurckForcing_firstOrderCoupling` — the **first-order Sobolev coupling** of the
  Nemytskii nonlinearity, integrated in time and read at the spectral-mass level: the
  forcing masses at every spatial order `d` are controlled by the solution-field masses at
  order `d + 1`.  This is the honest spectral encoding of `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+1}}`
  (the Ricci–DeTurck remainder loses exactly one spatial derivative), and is precisely the
  abstract `hcouple` hypothesis consumed by the in-tree mass bootstrap
  `solFieldMass_summable_all`.  It is `t`-independent and a genuine property of the
  *operator* `deTurckSobolevNHa2`, not of the bootstrap conclusion.

* `deTurckForcing_smoothTimeCoordinateFamily` — the **`C∞`-in-time forcing coordinate
  family**: a smooth-in-time per-mode coordinate `f` and a time-continuous everywhere
  `Hᵃ`-representative `F` of `gforce`, with a single `t`-independent summable all-order
  time-jet spectral-mass majorant, whose `i`-th `L²`-coordinate agrees with `f i` on the
  closed slab `[0,T]`.  This is the classical parabolic interior-time smoothing carried up
  to the smooth (zero) initial datum (Amann maximal regularity; Ladyzhenskaya–Solonnikov–
  Uraltseva; Lieberman): every mixed time–space derivative of the forcing is continuous on
  the compact slab `[0,T] × M`, hence bounded into every spatial Sobolev order, uniformly in
  `t`.  Because the Nemytskii forcing is nonlinear its time-jets couple all modes, so this
  control does not reduce to the per-mode scalar ODE recursion of the *linear* heat
  semigroup; it is the genuine quasilinear smoothing input.

Both are honest `sorry`s (the deep parabolic prerequisites); consumers transitively depend
on their `sorryAx`.
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

/-- **DEEP ANALYTIC INPUT — the first-order spectral coupling of the Ricci–DeTurck
Nemytskii forcing.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀`, the per-mode forcing masses are controlled, one spatial order at a time, by the
solution-field masses one order higher: for every order `d`, if the solution masses at
order `d + 1` are summable (the solution lies in `L²([0,T]; H^{d+1})`) then the forcing
masses at order `d` are summable (the forcing lies in `L²([0,T]; Hᵈ)`).

This is the honest spectral-mass encoding of the **first-order loss** of the Ricci–DeTurck
remainder `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+1}}` integrated in time.  It is a property of the
operator `deTurckSobolevNHa2` (zero principal symbol; the remainder is first-order), not the
conclusion of any bootstrap, and is precisely the abstract `hcouple` hypothesis of the
in-tree mass bootstrap `solFieldMass_summable_all` / `solFieldMass_summable_succ`.

**EXISTENCE-SIDE INPUT — the high-order tame/Moser lift of the Ricci–DeTurck
Nemytskii forcing.**

This is the genuine *quadratic-derivative-loss* analytic content of the engine
forcing, isolated as the single deferred input of the realize-side spectral
coupling.  For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (…)`
about `g₀` and any spatial order `d ≥ a`, **once** the realized solution field
lies one order higher (`Summable (solFieldMass hT gforce (d + 1))`, i.e.
`u ∈ L²([0,T]; H^{d+1})`), the Nemytskii image `N(u) = gforce` itself lifts to a
bona-fide time-`L²` field at the spatial order `d`:

  `∃ gforce_d ∈ L²([0,T]; Hᵈ),  ι gforce_d = gforce`,

where `ι = timeL2Inclusion` is the order-`d → a` Sobolev inclusion on the
time-`L²` scale.  This is the honest "`N` loses exactly one spatial derivative"
content of the Ricci–DeTurck remainder, `‖N(u)‖_{Hᵈ} ≲ (1 + ‖u‖_{L^∞}) ·
‖u‖_{H^{d+1}}` integrated in time: in the supercritical regime
`2·finrank + 10 ≤ a` the base regularity `a + 1 ≫ finrank/2` forces
`u ∈ L^∞` with a finite time-uniform constant, so the Moser/tame product
estimate puts `N(u)` into `L²(Hᵈ)` whenever `u ∈ L²(H^{d+1})`.

It is genuinely the existence side's analytic property of the *operator*
`deTurckSobolevNHa2` (its Sobolev-order mapping behaviour), not the conclusion of
any bootstrap: the conclusion below asserts only *summability of a mass family*,
whereas this input produces an *actual element of the order-`d` time-`L²`
space* — strictly stronger structural content from which the summability follows
by the intrinsic Plancherel mass identity `summable_weight_mul_norm_timeModeCoeff_sq`.

DEFERRED (honest `sorry`; this is the realize side's single posited existence-side
input — the deep parabolic Moser estimate. Consumers transitively depend on its
`sorryAx`). -/
private theorem deTurckForcing_higherOrderRepresentative
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∀ (d : ℝ) (hda : (a : ℝ) ≤ d),
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        ∃ gforce_d : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 d) T,
          timeL2Inclusion (I := I) (M := M) hda gforce_d = gforce :=
  sorry

/-- **The first-order spectral coupling of the Ricci–DeTurck Nemytskii forcing.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀`, the per-mode forcing masses are controlled, one spatial order at a time, by the
solution-field masses one order higher: for every order `d`, if the solution masses at
order `d + 1` are summable (the solution lies in `L²([0,T]; H^{d+1})`) then the forcing
masses at order `d` are summable (the forcing lies in `L²([0,T]; Hᵈ)`).

The proof splits at the base regularity `a` of the forcing:

* **for `d ≤ a`** the bound is *unconditional*: `gforce ∈ L²([0,T]; Hᵃ)` by
  construction, so the order-`a` masses are intrinsically summable (the spectral
  Plancherel identity `summable_weight_mul_norm_timeModeCoeff_sq`), and the
  order-`d` masses are dominated by them since the Sobolev weight is monotone in
  the order (`tensorSobolevWeight_mono`); the hypothesis is not even needed;

* **for `d > a`** the genuine first-order loss enters: the realized solution field
  lying one order higher (the summability hypothesis at `d + 1`) supplies, through
  the deferred Moser/tame lift `deTurckForcing_higherOrderRepresentative`, an actual
  order-`d` time-`L²` representative `gforce_d` of the forcing; the order-`d` masses
  of `gforce` then coincide with those of `gforce_d` (the time-mode coordinate is
  Sobolev-inclusion invariant, `timeModeCoeff_timeL2Inclusion`) and are intrinsically
  summable by the same Plancherel identity applied at order `d`.

This is precisely the abstract `hcouple` hypothesis of the in-tree mass bootstrap
`solFieldMass_summable_all` / `solFieldMass_summable_succ`, and its only deep analytic
content is the deferred existence-side input
`deTurckForcing_higherOrderRepresentative`. -/
theorem deTurckForcing_firstOrderCoupling
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d) := by
  -- The chart-locality-free compactness of the rank-`(0,2)` `L²`-side resolvent,
  -- the spectral-discreteness witness consumed by the Plancherel mass identity.
  have h_compact : IsCompactOperator
      ⇑(DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventL2
          (I := I) (M := M) g₀ 0 2) :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  -- The intrinsic order-`a` forcing masses are summable: this is the spectral
  -- Plancherel identity for the construction-given `Hᵃ` time-`L²` forcing.
  have hbase : Summable (forcingMass (I := I) (M := M) gforce (a : ℝ)) :=
    summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M)
      (f := gforce) h_compact
  intro d hsol
  rcases le_or_gt d (a : ℝ) with hda | hda
  · -- `d ≤ a`: dominate the order-`d` masses by the (summable) order-`a` masses,
    -- using monotonicity of the Sobolev weight in the order; unconditional.
    refine Summable.of_nonneg_of_le
      (fun i => forcingMass_nonneg (I := I) (M := M) gforce d i) (fun i => ?_) hbase
    refine mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i hda) (sq_nonneg _)
  · -- `d > a`: the genuine first-order loss.  The solution lying one order higher
    -- supplies an order-`d` time-`L²` representative `gforce_d` of the forcing
    -- (the deferred Moser/tame lift); its intrinsic order-`d` masses agree with
    -- those of `gforce` and are summable by the Plancherel identity at order `d`.
    obtain ⟨gforce_d, hgd⟩ :=
      deTurckForcing_higherOrderRepresentative (I := I) (M := M) g₀ g_bg a ha_super
        hT hT1 gforce hforce d hda.le hsol
    have hsum_d : Summable (forcingMass (I := I) (M := M) gforce_d d) :=
      summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M)
        (f := gforce_d) h_compact
    refine hsum_d.congr (fun i => ?_)
    have hcoeff :
        timeModeCoeff (I := I) (M := M) gforce_d i
          = timeModeCoeff (I := I) (M := M) gforce i := by
      rw [← hgd]
      exact (timeModeCoeff_timeL2Inclusion (I := I) (M := M) hda.le gforce_d i).symm
    simp only [forcingMass, hcoeff]

/-- **DEEP ANALYTIC INPUT — the `C∞`-in-time forcing coordinate family.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), the per-eigenmode
forcing coordinates admit a genuinely **`C∞`-in-time** representative `f` together with a
time-continuous everywhere `Hᵃ`-representative `F` with:

* **(smoothness)** each `f i` is `C∞`;
* **(all-order time-jet spectral-mass)** for every time-derivative order `j` and spatial
  Sobolev order `τ ≥ 0`, the weighted square of the `j`-th time-derivative of `f i` has a
  single `t`-independent summable-across-modes majorant on `[0,T]`;
* **(representative)** `gforce =ᵐ F` and each per-mode coordinate `t ↦ (F t).coeff i` is
  continuous on `[0,T]`;
* **(coordinate realization)** on `[0,T]` the per-mode coordinate of `F` is the smooth
  `f`: `(F t).coeff i = f i t`.

This is the genuine parabolic interior-time smoothing of the engine forcing carried up to
the smooth (zero) initial datum: beyond the *continuity* of the forcing's mode coordinates,
the smoothing supplies all-order time-derivative spectral-mass control by differentiating
through the maximal-regularity gain against the Nemytskii first-order coupling.  The
forcing's mixed time–space derivatives are continuous on the compact slab `[0,T] × M`, hence
bounded into every spatial Sobolev order, uniformly in `t`.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
theorem deTurckForcing_smoothTimeCoordinateFamily
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
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) :=
  sorry

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
