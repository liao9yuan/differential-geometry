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
file isolates the genuine classical parabolic prerequisite behind the joint
`C∞`-up-to-`t = 0` regularity of the realized DeTurck–Ricci solution family.

## The second-order derivative loss of the Nemytskii forcing

The Ricci–DeTurck remainder is genuinely **second order**: it loses exactly **two** spatial
derivatives (the quadratic `u·∂²u` term, carried by the inverse-Gram `C₂·∇²` arm).  At the
spatial-Sobolev level this is the AFFINE ball bound
`deTurckRemainder_iteratedCovGradSum_ballBound` (`DeTurck/DeTurckRemainderAbsoluteBallBound.lean`,
window `d + 2`): on a covariant-`L²` ball of radius `R`,

  `∑_{q ≤ d} ‖∇^q N(T)‖²  ≤  C · (1 + ∑_{i ≤ d+2} ‖∇^i T‖²)`,

i.e. `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}` (quadratic, +2), **not** `≲ 1 + ‖u‖_{H^{d+1}}` (+1).
Because the loss is `+2`, the naive one-order interior-smoothing bootstrap of
`ParabolicInteriorSmoothing.lean` (`solFieldMass_summable_all`, fed a `+1` coupling
`solFieldMass (d+1) → forcingMass d`) STALLS: its net advance per step is
parabolic-gain (`+2`) − coupling-loss (`+2`) `= 0`, so it cannot derive forcing-mass
summability at all orders.  The honest mechanism is the **small-data fibre-smallness
contraction** about the zero initial datum (base order `a + 2 ≫ finrank/2` held FIXED, not
ratcheted by `+1`): with the `(1 + ‖u‖_∞)` Moser factor controlled by the supercritical
embedding and the fibre-smallness `δ < 1`, the genuine parabolic interior-time smoothing of
the engine forcing supplies the all-order forcing-mass summability directly.

## The analytic input

* `deTurckForcing_smoothTimeCoordinateFamily` — the **`C∞`-in-time forcing coordinate
  family**, together with the all-order forcing-mass summability: a smooth-in-time per-mode
  coordinate `f`, a time-continuous everywhere `Hᵃ`-representative `F` of `gforce` with a
  single `t`-independent summable all-order time-jet spectral-mass majorant, the per-mode
  `L²`-coordinate of `F` agreeing with `f i` on the closed slab `[0,T]`, AND the forcing
  masses `forcingMass gforce c` summable at every spatial order `c ≥ 0`.  This is the
  classical parabolic interior-time smoothing of the engine forcing carried up to the smooth
  (zero) initial datum (Amann maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva;
  Lieberman), in its genuine second-order / small-data form: every mixed time–space
  derivative of the forcing is continuous on the compact slab `[0,T] × M`, hence bounded into
  every spatial Sobolev order, uniformly in `t`.  Because the Nemytskii forcing is nonlinear
  its time-jets couple all modes, so this control does not reduce to the per-mode scalar ODE
  recursion of the *linear* heat semigroup; it is the genuine quasilinear smoothing input,
  and the all-order forcing-mass summability is its genuine `+2`/small-data output (the
  coupling-agnostic analogue of the sibling
  `realizedSol_forcing_continuousRepr_allOrderMass`).

## The two genuinely-deep parabolic leaves

The combination `deTurckForcing_smoothTimeCoordinateFamily` is **decomposed** into the two
genuinely-classical parabolic facts it rests on, each isolated as a single named,
forcing-pinned honest input (PINNED to `hforce`, so neither is vacuous):

* `deTurckForcing_smoothTimeCoordinateField` — the **`C∞`-in-time forcing coordinate field**
  with the all-order time-jet spectral-mass majorant on the closed slab `[0,T]` and an
  everywhere representative `F` realizing the smooth coordinates (`(F t).coeff i = f i t`).
  This is the genuine quasilinear parabolic interior-time smoothing of the engine forcing
  carried up to the smooth (zero) initial datum: the Nemytskii forcing is `C∞`-in-time on
  `[0,T]` because the datum is smooth and the maximal-regularity solution is `C∞`-up-to-`0`,
  and its time-jets couple all modes (the nonlinear coupling), so this control does not
  reduce to the per-mode linear-heat ODE recursion.

* `deTurckForcing_allOrderForcingMass` — the **all-order spatial forcing-mass summability**
  `∀ c ≥ 0, Summable (forcingMass gforce c)`.  This is the `+2`/small-data interior-smoothing
  output (the coupling-agnostic analogue of the sibling
  `realizedSol_forcing_continuousRepr_allOrderMass`), TRUE at the FIXED base order `a + 2`
  under the fibre-smallness `δ < 1` of the zero-datum solution — NOT the dead `+1` coupling
  bootstrap (whose net advance is `0` for the `+2` nonlinearity).

The combination `deTurckForcing_smoothTimeCoordinateFamily` is then pure GLUE: `f`, `F` and
clauses (smoothness), (time-jet majorant), (representative `=ᵐ`), (coordinate realization)
come straight from `deTurckForcing_smoothTimeCoordinateField`; the per-mode coordinate
continuity of `F` is the smoothness of `f` transported across the coordinate realization;
and the all-order forcing-mass summability is `deTurckForcing_allOrderForcingMass`.

Both leaves are honest `sorry`s (the deep parabolic prerequisites); consumers transitively
depend on their `sorryAx`.
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

/-- **DEEP PARABOLIC LEAF (1/2) — the `C∞`-in-time forcing coordinate field of the
Ricci–DeTurck engine forcing.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), the per-eigenmode
forcing coordinates admit a genuinely **`C∞`-in-time** field `f`, together with an
everywhere `Hᵃ`-representative `F` of `gforce` whose per-mode `L²` coordinate on the closed
slab `[0,T]` is exactly the smooth `f`:

* **(smoothness)** each `f i` is `C∞`;
* **(all-order time-jet spectral-mass)** for every time-derivative order `j` and spatial
  Sobolev order `τ ≥ 0`, the weighted square of the `j`-th time-derivative of `f i` has a
  single `t`-independent summable-across-modes majorant on the CLOSED slab `[0,T]`
  (including `t = 0`);
* **(representative)** `gforce =ᵐ F`;
* **(coordinate realization)** on `[0,T]` the per-mode coordinate of `F` is the smooth `f`:
  `(F t).coeff i = f i t`.

This is the genuine quasilinear parabolic interior-time smoothing of the engine forcing
carried up to the smooth (zero) initial datum (Amann maximal regularity; Ladyzhenskaya–
Solonnikov–Uraltseva; Lieberman): every mixed time–space derivative of the forcing is
continuous on the compact slab `[0,T] × M`, hence bounded into every spatial Sobolev order
uniformly in `t`.  Because the Nemytskii forcing is nonlinear its time-jets couple all
modes, so this control does not reduce to the per-mode scalar ODE recursion of the *linear*
heat semigroup; it is the genuine quasilinear smoothing input.

PINNED to the forcing by `hforce` (so it is not vacuous): the conjuncts `gforce =ᵐ F` and
`(F t).coeff i = f i t` force `f i` to track the actual coordinates of `gforce`, which is
itself fixed by `hforce` to the genuine second-order Nemytskii image of its own Duhamel
solution field.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
theorem deTurckForcing_smoothTimeCoordinateField
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
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) :=
  sorry

/-- **DEEP PARABOLIC LEAF (2/2) — all-order spatial forcing-mass summability of the
Ricci–DeTurck engine forcing.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), the forcing masses
`forcingMass gforce c` are summable at every spatial Sobolev order `c ≥ 0` (the forcing lies
in `L²([0,T]; Hᶜ)` for every `c`).

The Ricci–DeTurck remainder loses exactly **two** spatial derivatives (the quadratic
`u·∂²u` arm, the AFFINE ball bound `deTurckRemainder_iteratedCovGradSum_ballBound`, window
`d + 2`): `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}`, NOT `≲ 1 + ‖u‖_{H^{d+1}}`.  Because the loss is
`+2`, this all-order summability is NOT obtained by a one-order
(`solFieldMass (d+1) → forcingMass d`) coupling bootstrap — that net advance is `0` for a
`+2` nonlinearity.  It is the genuine **small-data parabolic interior-smoothing** output:
about the zero initial datum the realized solution field is fibre-small with one constant
`δ < 1`, the `(1 + ‖u‖_∞)` Moser factor is controlled by the supercritical embedding
(`2·finrank + 10 ≤ a` forces the base order `a + 2 ≫ finrank/2`, held FIXED), and the
short-time contraction `C·δ < 1` smooths the forcing into every spatial Sobolev order on the
horizon.  This is the coupling-agnostic analogue of the sibling leaf
`realizedSol_forcing_continuousRepr_allOrderMass`, whose third clause is exactly this
statement under the same hypotheses.

PINNED to the forcing by `hforce` (so it is not vacuous).

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
theorem deTurckForcing_allOrderForcingMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c) :=
  sorry

/-- **DEEP ANALYTIC INPUT — the `C∞`-in-time forcing coordinate family with all-order
forcing-mass summability.**

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
* **(all-order forcing-mass summability)** the forcing masses `forcingMass gforce c` are
  summable at every spatial order `c ≥ 0` (the forcing lies in `L²([0,T]; Hᶜ)` for every
  `c`);
* **(coordinate realization)** on `[0,T]` the per-mode coordinate of `F` is the smooth
  `f`: `(F t).coeff i = f i t`.

This is the genuine parabolic interior-time smoothing of the engine forcing carried up to
the smooth (zero) initial datum.  The Ricci–DeTurck remainder loses exactly **two** spatial
derivatives (the quadratic `u·∂²u` arm, the AFFINE ball bound
`deTurckRemainder_iteratedCovGradSum_ballBound`, window `d + 2`):
`‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}`, NOT `≲ 1 + ‖u‖_{H^{d+1}}`.  Because the loss is `+2`, the
all-order forcing-mass summability is NOT obtained by a one-order
(`solFieldMass (d+1) → forcingMass d`) coupling bootstrap — that net advance is `0` for a
`+2` nonlinearity.  It is the genuine **small-data parabolic interior-smoothing** output:
about the zero initial datum the realized solution field is fibre-small with one constant
`δ < 1`, the `(1 + ‖u‖_∞)` Moser factor is controlled by the supercritical embedding
(`2·finrank + 10 ≤ a` forces the base order `a + 2 ≫ finrank/2`, held FIXED), and the
short-time contraction `C·δ < 1` smooths the forcing into every spatial Sobolev order on the
horizon — the coupling-agnostic all-order forcing-mass summability stated here (the analogue
of the sibling leaf `realizedSol_forcing_continuousRepr_allOrderMass`).

GLUE: the smooth field `f`, the representative `F`, and the conjuncts (smoothness),
(all-order time-jet majorant), (representative `=ᵐ`), (coordinate realization) are supplied
by `deTurckForcing_smoothTimeCoordinateField`; the per-mode coordinate continuity of `F` is
the smoothness of `f` transported across the coordinate realization (`ContinuousOn.congr`);
and the all-order spatial forcing-mass summability is `deTurckForcing_allOrderForcingMass`.
Consumers transitively depend on the `sorryAx` of those two deep parabolic leaves. -/
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
      (∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) := by
  obtain ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateField (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      gforce hforce
  have hF_coord_cont : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine ContinuousOn.congr (f := fun t => f i t) ?_ ?_
    · exact (hf_smooth i).continuous.continuousOn
    · intro t ht
      exact hF_coeff t ht i
  refine ⟨f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, ?_, hF_coeff⟩
  exact deTurckForcing_allOrderForcingMass (I := I) (M := M) g₀ g_bg a ha_super hT hT1
    gforce hforce

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
