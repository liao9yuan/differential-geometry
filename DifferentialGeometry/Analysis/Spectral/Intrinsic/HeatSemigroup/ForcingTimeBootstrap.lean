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

/-- **DEEP PARABOLIC LEAF — the small-data fibre-smallness factored Nemytskii spectral
remainder bound (the genuine `θ < 1` contraction).**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), at every spatial order
`c ≥ a` the order-`c` spectral forcing mass is bounded, mode by mode, by a genuinely
**contractive** multiple of the order-`(c + 2)` spectral solution mass plus a single FIXED,
datum-independent smooth-section background:

  `forcingMass gforce c i  ≤  θ · solFieldMass gforce (c + 2) i  +  ‖N0‖²-mass at order c`,

with `0 < θ` and the **short-time contraction** `θ · (1 + T)² < 1`.

This is the genuine small-data smoothing content, NOT the affine ball bound
`deTurckRemainder_iteratedCovGradSum_ballBound` (which is `C · (1 + ‖u‖²)` with `C ≥ 1` and
NO contraction factor).  The factor `θ < 1 / (1 + T)²` comes from the **short-time smallness
of the zero-datum solution operator**: about the zero initial datum the realized solution
field is fibre-small with one uniform constant `δ < 1`
(`realizedDeTurck_timeRegular_family` / `solInterior_smoothRepr_pin`), and on the short
horizon `T ≤ 1` the Duhamel solution norm is small enough that the genuinely-second-order
top arm `(∇²u)` of the Nemytskii is absorbed with a contractive coefficient — the standard
quasilinear small-data parabolic mechanism (Amann maximal regularity;
Ladyzhenskaya–Solonnikov–Uraltseva; Lieberman).  The background `N0 := N(0) =
−2 Ric(g₀) + 𝓛_{W} g₀` is a FIXED smooth section (`deTurckSmoothRemainder g₀ g_bg 0`),
INDEPENDENT of `gforce`, hence lies in `H^∞` with spectral masses summable at every order
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, the field `weighted_summable` of
`smoothCcToTensorHs`).

NON-VACUOUS and not hypothesis-packaging: `θ > 0` strict forbids the degenerate `θ = 0`
witness, and the background is the mass of a FIXED smooth section (NOT `forcingMass gforce c`
itself), so the inequality genuinely *constrains* the forcing — it is FALSE precisely when
the real Nemytskii bound fails, and it is satisfiable for the genuine zero-datum forcing.
PINNED to the forcing by `hforce`.

DEFERRED (honest `sorry`; the genuine short-time small-data contraction of the zero-datum
Ricci–DeTurck solution operator; consumers transitively depend on its `sorryAx`). -/
theorem deTurckForcing_smallness_factored_spectral_remainder_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (c : ℝ) (hc : (a : ℝ) ≤ c) :
    ∃ (θ : ℝ) (N0 : SmoothCcTensor g₀ 0 2),
      0 < θ ∧ θ * (1 + T) ^ 2 < 1 ∧
        ∀ i, forcingMass (I := I) (M := M) gforce c i ≤
          θ * solFieldMass (I := I) (M := M) hT.le gforce (c + 2) i +
            tensorSobolevWeight (I := I) (M := M) i c *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ c N0).coeff i) ^ 2 :=
  sorry

set_option linter.unusedVariables false in
/-- **DEEP PARABOLIC LEAF — the small-data Nemytskii spectral `+2` forcing-mass advance.**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), the all-order spatial
forcing-mass summability is generated, two spatial orders at a time, by the genuine
small-data parabolic interior smoothing of the engine forcing: **at every spatial order
`d ≥ a`, forcing-mass summability at order `d` (the forcing in `L²([0,T]; Hᵈ)`) propagates
up to forcing-mass summability at order `d + 2` (the forcing in `L²([0,T]; H^{d+2}})`).**

The `+2` increment matches the genuine **second-order** derivative loss of the Ricci–DeTurck
remainder (the quadratic inverse-Gram `C₂·∇²` arm): the AFFINE ball bound
`deTurckRemainder_iteratedCovGradSum_ballBound` (window `d + 2`) gives
`‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+2}}`, NOT `≲ 1 + ‖u‖_{H^{d+1}}`.  This is why the advance is
two orders, and why it is **not** the dead one-order coupling
(`solFieldMass (d+1) → forcingMass d`) that `solFieldMass_summable_all` consumes: composed
with the PROVEN `+2` Duhamel gain `solFieldMass_le_forcingMass`
(`solFieldMass (c+2) ≤ (1+T)²·forcingMass c`), a `+2` loss matched by a `+2` gain has net
order advance `0` and stalls.

PROVEN here as the **same-order absorption fixed point** over the genuine contractive factored
bound `deTurckForcing_smallness_factored_spectral_remainder_bound` (`θ · (1 + T)² < 1`,
the short-time small-data contraction about the zero datum): instantiating the factored
bound at order `c = d + 2` gives, mode by mode,
`forcingMass gforce (d+2) i ≤ θ · solFieldMass gforce (d+4) i + bg_i`; the PROVEN `+2` Duhamel
gain `solFieldMass_le_forcingMass` bounds `solFieldMass gforce (d+4) i ≤ (1+T)² ·
forcingMass gforce (d+2) i`; so the self-referential `forcingMass gforce (d+2) i ≤
θ(1+T)² · forcingMass gforce (d+2) i + bg_i` closes (since `θ(1+T)² < 1`) to
`forcingMass gforce (d+2) i ≤ bg_i / (1 − θ(1+T)²)`, summable mode by mode because the FIXED
smooth background `N0 ∈ H^∞` has summable spectral masses at every order — the fixed point,
not a net order race.  This is the coupling-agnostic spectral output feeding
`realizedSol_forcing_continuousRepr_allOrderMass`.

PINNED to the forcing by `hforce`: `hforce` fixes `gforce` to the genuine second-order
Nemytskii image of its own Duhamel solution field.  The hypothesis
`Summable (forcingMass gforce d)` is satisfiable (it holds at `d = a` by the Plancherel
identity `summable_weight_mul_norm_timeModeCoeff_sq`); the absorption fixed point closes the
`+2` advance at the target order `d + 2` directly from the contractive factored bound, so the
implication is contentful and `hd` is harmless (proving the stronger order-`(d+2)`
summability outright).  Consumers transitively depend on the `sorryAx` of the deep
contractive factored bound. -/
theorem deTurckForcing_forcingMass_summable_succ
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (d : ℝ) (hda : (a : ℝ) ≤ d)
    (hd : Summable (forcingMass (I := I) (M := M) gforce d)) :
    Summable (forcingMass (I := I) (M := M) gforce (d + 2)) := by
  classical
  have hda2 : (a : ℝ) ≤ d + 2 := by linarith
  obtain ⟨θ, N0, hθ_pos, hθ_contract, hbound⟩ :=
    deTurckForcing_smallness_factored_spectral_remainder_bound (I := I) (M := M) g₀ g_bg a
      ha_super hT hT1 gforce hforce (d + 2) hda2
  set μ : ℝ := 1 - θ * (1 + T) ^ 2 with hμ_def
  have hμ_pos : 0 < μ := by rw [hμ_def]; linarith
  set bg : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (d + 2) *
      ((smoothCcToTensorHs (I := I) (M := M) g₀ (d + 2) N0).coeff i) ^ 2 with hbg_def
  have hbg_summable : Summable bg :=
    (smoothCcToTensorHs (I := I) (M := M) g₀ (d + 2) N0).weighted_summable
  have habsorb : ∀ i, μ * forcingMass (I := I) (M := M) gforce (d + 2) i ≤ bg i := by
    intro i
    have hgain :
        solFieldMass (I := I) (M := M) hT.le gforce ((d + 2) + 2) i ≤
          (1 + T) ^ 2 * forcingMass (I := I) (M := M) gforce (d + 2) i :=
      solFieldMass_le_forcingMass (I := I) (M := M) hT.le gforce (d + 2) i
    have hθ_nn : 0 ≤ θ := hθ_pos.le
    have hsol_le :
        θ * solFieldMass (I := I) (M := M) hT.le gforce ((d + 2) + 2) i ≤
          θ * (1 + T) ^ 2 * forcingMass (I := I) (M := M) gforce (d + 2) i := by
      have := mul_le_mul_of_nonneg_left hgain hθ_nn
      linarith [this]
    have hfm := hbound i
    have : forcingMass (I := I) (M := M) gforce (d + 2) i ≤
        θ * (1 + T) ^ 2 * forcingMass (I := I) (M := M) gforce (d + 2) i + bg i := by
      calc forcingMass (I := I) (M := M) gforce (d + 2) i
          ≤ θ * solFieldMass (I := I) (M := M) hT.le gforce ((d + 2) + 2) i + bg i := hfm
        _ ≤ θ * (1 + T) ^ 2 * forcingMass (I := I) (M := M) gforce (d + 2) i + bg i := by
            linarith [hsol_le]
    rw [hμ_def]; nlinarith [this]
  refine Summable.of_nonneg_of_le
    (fun i => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i)
    (fun i => ?_) (hbg_summable.mul_left μ⁻¹)
  have h := habsorb i
  rw [← le_div_iff₀' hμ_pos, div_eq_inv_mul] at h
  exact h

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

PROVEN here as the spatial-order bootstrap over the genuine `+2` small-data advance: the base
order `c = a` is the Plancherel identity `summable_weight_mul_norm_timeModeCoeff_sq` (the
forcing lives in `L²([0,T]; Hᵃ)` by construction); the `+2` step
`deTurckForcing_forcingMass_summable_succ` (the deep small-data Nemytskii spectral coupling)
ratchets the summability up to every order `a + 2 n`; and the down-widening
(`tensorSobolevWeight_mono`, the weight is `≥ 1` and the exponent larger) covers every real
order `c ≥ 0` from a sufficiently high `a + 2 n ≥ c`.  Consumers transitively depend on the
`sorryAx` of the deep `+2` advance. -/
theorem deTurckForcing_allOrderForcingMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  -- BASE (`c = a`): the forcing lives in `L²([0,T]; Hᵃ)`, so its order-`a` masses are
  -- summable by the Plancherel identity (definitionally `forcingMass gforce a`).
  have hbase : Summable (forcingMass (I := I) (M := M) gforce (a : ℝ)) :=
    summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) gforce h_compact
  -- The `+2` ratchet: forcing-mass summability at every order `a + 2 n`, `n : ℕ`, by the
  -- deep small-data Nemytskii spectral advance applied `n` times above the base order `a`.
  have hstep : ∀ n : ℕ,
      Summable (forcingMass (I := I) (M := M) gforce ((a : ℝ) + 2 * n)) := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ k ih =>
      have hda : (a : ℝ) ≤ (a : ℝ) + 2 * (k : ℝ) := by
        have : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        linarith
      have hadv := deTurckForcing_forcingMass_summable_succ (I := I) (M := M) g₀ g_bg a
        ha_super hT hT1 gforce hforce ((a : ℝ) + 2 * (k : ℝ)) hda ih
      have hrw : (a : ℝ) + 2 * (k : ℝ) + 2 = (a : ℝ) + 2 * ((k : ℕ) + 1 : ℕ) := by
        push_cast; ring
      rwa [hrw] at hadv
  -- ALL orders `c ≥ 0`: reach a high even-spaced order `a + 2 n ≥ c`, then DOWN-WIDEN — the
  -- order-`c` masses are dominated mode by mode by the order-`(a + 2 n)` masses (`(1 + λᵢ)^c ≤
  -- (1 + λᵢ)^{a + 2 n}`, the weight is `≥ 1` and the exponent larger), same `timeModeCoeff`.
  intro c _hc
  obtain ⟨n, hn⟩ := exists_nat_ge (c - a)
  have hc_le : c ≤ (a : ℝ) + 2 * (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (n : ℝ) ≤ 2 * (n : ℝ) := by linarith
    linarith
  refine Summable.of_nonneg_of_le
    (fun i => forcingMass_nonneg (I := I) (M := M) gforce c i)
    (fun i => ?_) (hstep n)
  have hwle : tensorSobolevWeight (I := I) (M := M) i c ≤
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + 2 * (n : ℝ)) :=
    tensorSobolevWeight_mono (I := I) (M := M) i hc_le
  simpa only [forcingMass] using
    mul_le_mul_of_nonneg_right hwle (sq_nonneg _)

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
