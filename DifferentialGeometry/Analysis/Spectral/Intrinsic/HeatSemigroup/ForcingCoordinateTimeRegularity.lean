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
forcing time-bootstrap rests on: the existence of a `C∞`-in-time per-eigenmode forcing
coordinate field with an all-order time-jet spectral-mass majorant on the closed slab
`[0,T]`, agreeing a.e. with the actual per-mode coordinate of `gforce`.

## What this file posits versus what the bootstrap builds on top

The per-mode forcing coordinate `t ↦ (gforce t).coeff i` is the `i`-th eigenbasis
coordinate of the Nemytskii image `N(u(t))` of the maximal-regularity Duhamel solution
`u`.  Because the datum is the **smooth (zero)** initial perturbation, the solution is
`C∞`-up-to-`t = 0` (the classical small-data parabolic interior-time smoothing — Amann
maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva; Lieberman), and the Nemytskii
forcing is a smooth function of the solution, so the per-mode coordinate is genuinely
`C∞`-in-time.  Its time-jets couple all modes (the nonlinear coupling), so the all-order
time-jet spectral-mass control does **not** reduce to the per-mode scalar ODE recursion of
the *linear* heat semigroup, nor to the integrated-in-time spatial forcing mass
`forcingMass gforce c` (which controls `∫₀ᵀ |coeffᵢ|²` but neither the pointwise-in-`t`
value nor any time-derivative).  It is the genuine quasilinear smoothing input, and it is
the irreducible deep parabolic leaf of the realize-side forcing time-bootstrap.

This posit is deliberately stated at the **per-mode scalar grain**: it carries the smooth
coordinate field `f`, the all-order time-jet majorant, and the per-mode a.e. agreement
`(fun t => (gforce t).coeff i) =ᵐ f i` — strictly more primitive than (and structurally
distinct from) the bundled everywhere `Hᵃ`-representative `F` that the consumer
`deTurckForcing_smoothTimeCoordinateField` assembles from it.  PINNED to the forcing by
`hforce` (so it is not vacuous): the per-mode a.e. agreement forces `f i` to track the
actual coordinates of `gforce`, itself fixed by `hforce` to the genuine second-order
Nemytskii image of its own Duhamel solution field.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`).
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

/-- **DEEP PARABOLIC LEAF — the `C∞`-in-time per-mode forcing coordinate field of the
Ricci–DeTurck engine forcing (the genuinely-irreducible quasilinear time-smoothing).**

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

This is the genuine quasilinear parabolic interior-time smoothing of the engine forcing
carried up to the smooth (zero) initial datum (Amann maximal regularity; Ladyzhenskaya–
Solonnikov–Uraltseva; Lieberman): every mixed time–space derivative of the forcing is
continuous on the compact slab `[0,T] × M`, hence bounded into every spatial Sobolev order
uniformly in `t`, and at `t = 0` the smooth zero datum rules out any parabolic blow-up.
Because the Nemytskii forcing is nonlinear its time-jets couple all modes, so this control
does not reduce to the per-mode scalar ODE recursion of the *linear* heat semigroup nor to
the integrated-in-time spatial forcing mass `forcingMass gforce c` (the `L²`-in-time
integral bound, which controls neither the pointwise-in-`t` value nor any time-derivative);
it is the genuine quasilinear smoothing input.

PINNED to the forcing by `hforce` and the a.e.-agreement conjunct (so it is not vacuous):
`(fun t => (gforce t).coeff i) =ᵐ f i` forces `f i` to track the actual coordinates of
`gforce`, itself fixed by `hforce` to the genuine second-order Nemytskii image of its own
Duhamel solution field.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
theorem deTurckForcing_smoothCoordinate_aeTimeJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
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
      (∀ i, (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T] f i) :=
  sorry

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
