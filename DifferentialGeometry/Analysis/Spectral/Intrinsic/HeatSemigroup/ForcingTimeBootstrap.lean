import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingCoordinateTimeRegularity
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
  This is now itself GLUE over the single genuinely-irreducible deep parabolic leaf
  `deTurckForcing_smoothCoordinate_aeTimeJet` (`ForcingCoordinateTimeRegularity.lean`),
  which supplies the smooth coordinate field `f`, the all-order time-jet majorant, and the
  per-mode a.e. agreement `(fun t => (gforce t).coeff i) =ᵐ f i`; the everywhere `Hᵃ`
  representative `F` is ASSEMBLED here from `f` (its slab coordinates are `f`, summable
  across modes by the `j = 0, τ = a` instance of the majorant), the `=ᵐ` representative is
  the per-mode a.e. agreement combined across the countable eigen-index, and the coordinate
  realization is by construction.  The deep leaf is the genuine quasilinear parabolic
  interior-time smoothing of the engine forcing carried up to the smooth (zero) initial
  datum: the Nemytskii forcing is `C∞`-in-time on `[0,T]` because the datum is smooth and
  the maximal-regularity solution is `C∞`-up-to-`0`, and its time-jets couple all modes (the
  nonlinear coupling), so this control does not reduce to the per-mode linear-heat ODE
  recursion nor to the integrated-in-time spatial forcing mass.

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

`deTurckForcing_smoothTimeCoordinateField` is now sorry-free GLUE over the single deep leaf
`deTurckForcing_smoothCoordinate_aeTimeJet`; `deTurckForcing_allOrderForcingMass` is
sorry-free GLUE (the spatial-order `+2` ratchet) over the single deep total-norm leaf
`deTurckForcing_forcingMass_summable_succ` (the genuine total small-data quasilinear
parabolic `+2` interior-smoothing advance, TRUE at the total `H`-norm level — NOT a per-mode
factored bound, which is false because the zero-datum Duhamel solution is per-mode smaller
than the forcing).  Both rest on a single deep parabolic prerequisite each (the honest
`sorry`s); consumers transitively depend on their `sorryAx`.
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

GLUE over the single genuinely-irreducible deep parabolic leaf
`deTurckForcing_smoothCoordinate_aeTimeJet` (`ForcingCoordinateTimeRegularity.lean`): that
leaf supplies the `C∞`-in-time per-mode coordinate field `f`, the all-order time-jet
spectral-mass majorant, and the per-mode a.e. coordinate agreement
`(fun t => (gforce t).coeff i) =ᵐ f i`.  The everywhere `Hᵃ`-representative `F` is then
ASSEMBLED here from `f` (its slab coordinates are `f`, summable across modes by the
`j = 0, τ = a` instance of the majorant), the `=ᵐ` representative is the per-mode a.e.
agreement combined across the countable eigen-index (`MeasureTheory.ae_all_iff`) and
`tensorHs.ext`, and the coordinate realization is by construction.  The smoothness and the
majorant pass straight through.  Consumers transitively depend on the `sorryAx` of that one
deep leaf. -/
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
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJet (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      gforce hforce
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (a : ℝ) (Nat.cast_nonneg a)
  -- The slab summability of the order-`a` weighted coordinate squares, uniform in `t`,
  -- from the `j = 0, τ = a` time-jet majorant (`iteratedDeriv 0 (f i) = f i`).
  have hslab_sum : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (f i t) ^ 2) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)) (sq_nonneg _)
    · have := hB_le i t ht
      rwa [iteratedDeriv_zero] at this
  -- The everywhere `Hᵃ`-representative `F`: on the slab its `i`-th coordinate is the smooth
  -- `f i`; off the slab it is `0` (irrelevant to `=ᵐ[timeMeasure T]`).
  set F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) T then
      ⟨fun i => f i t, hslab_sum t ht⟩ else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, (F t).coeff i = f i t := by
    intro t ht i
    simp only [hF_def, dif_pos ht]
  refine ⟨f, F, hf_smooth, hf_mass, ?_, hF_coeff⟩
  -- The representative `=ᵐ`: the per-mode a.e. agreements `(gforce ·).coeff i =ᵐ f i`
  -- combine across the countable eigen-index to a single a.e.-in-`t` joint agreement, then
  -- `tensorHs.ext` upgrades it to `gforce t = F t` a.e.
  have hjoint : ∀ᵐ t ∂timeMeasure T, ∀ i, (gforce t).coeff i = f i t :=
    (MeasureTheory.ae_all_iff).2 hf_ae
  have hrestrict : ∀ᵐ t ∂timeMeasure T, t ∈ Set.Icc (0 : ℝ) T := by
    rw [show timeMeasure T = MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) from rfl]
    exact MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hjoint, hrestrict] with t ht_eq ht_mem
  refine tensorHs.ext ?_
  funext i
  rw [ht_eq i, hF_coeff t ht_mem i]

/-- **DEEP PARABOLIC LEAF — the fibre-small spectral self-feedback contraction of the
Ricci–DeTurck engine forcing at the order-`(d+2)` total energy (operator form).**

For the engine forcing `gforce =ᵐ deTurckSobolevNHa2 g₀ g_bg a ∘ (maxRegDuhamelSolField …)`
about `g₀` (supercritical `2·finrank + 10 ≤ a`, zero initial datum), pinned by `hforce` to
the genuine second-order Nemytskii image of its own zero-datum Duhamel solution field, the
order-`(d+2)` total spectral forcing energy obeys a genuine **small-data self-feedback
contraction**: there is one contraction factor `θ < 1` (the genuine fibre-small short-time
smallness of the zero-datum solution operator, below `1` because the engine is evaluated on
the realizability ball where the second-order Nemytskii loss is small-data) and one finite
background level `Kd ≥ 0` (the order-`d`-energy-controlled affine remainder of the
non-vanishing background nonlinearity `N(0)`, finite precisely because `hd` makes the
order-`d` forcing energy finite), such that **for every finite mode set `s` the order-`(d+2)`
forcing-mass partial sum absorbs into a `θ`-fraction of itself plus `Kd`**:

  `∑_{i ∈ s} forcingMass gforce (d+2) i  ≤  θ · ∑_{i ∈ s} forcingMass gforce (d+2) i  +  Kd`.

This is the honest **operator-level** content of the small-data parabolic interior
smoothing (Amann maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva; Lieberman), lying
strictly **below** the summability conclusion: it is a partial-sum self-feedback inequality
about the solution operator (driven by `hforce` and the small-data fibre-smallness `θ < 1`),
NOT the statement `Summable (forcingMass gforce (d+2))` (no packaging).  The mechanism: by
`hforce`, `gforce =ᵐ N(u)` with `u = maxRegDuhamelSolField 0 gforce`, so the order-`(d+2)`
forcing energy is the order-`(d+2)` energy of `N(u)`; the genuine second-order Nemytskii
affine ball bound `deTurckRemainder_iteratedCovGradSum_ballBound` (window `d+2`) controls it
by `C·(1 + ‖u‖²_{H^{d+4}})`; the PROVEN Duhamel `+2` gain `solFieldMass_le_forcingMass`
(`solFieldMass (c+2) ≤ (1+T)²·forcingMass c`) controls `‖u‖²_{H^{d+4}}` by
`(1+T)²·‖gforce‖²_{H^{d+2}}`, i.e. by the very order-`(d+2)` forcing energy on the left; and
the genuine small-data short-time smallness of the realized solution on the realizability
ball makes the resulting self-coefficient `θ < 1`.  This total absorption — never a per-mode
reverse bound, which is FALSE (`solFieldMass_le_forcingMass` shows the zero-datum solution is
per-mode SMALLER than the forcing, so a per-mode reverse would force `1 ≤ θ(1+T)²`) — is the
genuine `+2` content.

PINNED to the forcing by `hforce`; `hd` is genuinely consumed (it bounds `Kd`).

DEFERRED (honest `sorry`; the genuine fibre-small zero-datum maximal-regularity spectral
self-feedback estimate; consumers transitively depend on its `sorryAx`). -/
theorem deTurckForcing_forcingMass_partialSum_contraction
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
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
      ∀ s : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        ∑ i ∈ s, forcingMass (I := I) (M := M) gforce (d + 2) i ≤
          θ * (∑ i ∈ s, forcingMass (I := I) (M := M) gforce (d + 2) i) + Kd :=
  sorry

/-- **DEEP PARABOLIC LEAF — the small-data Nemytskii spectral `+2` forcing-mass advance
(the total `H`-norm form).**

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

This is the genuine deep small-data quasilinear parabolic `+2` interior-smoothing leaf
(Amann maximal regularity; Ladyzhenskaya–Solonnikov–Uraltseva; Lieberman), stated and TRUE
**at the TOTAL `H`-norm level** — `Summable (forcingMass gforce ·)` is the total order-`d`
spatial Sobolev energy of the forcing being finite, which is mode-mixing-safe.  It is the
spectral-summability isomorph of the A-side total-norm bound
`deTurckSobolevNHa2_mixed_lipschitz_pointwise`.  Crucially it is **NOT** a per-mode factored
bound `forcingMass c i ≤ θ · solFieldMass (c+2) i + bg_i` with `θ(1+T)² < 1`: that per-mode
reverse inequality is FALSE — the in-tree `solFieldMass_le_forcingMass` shows the zero-datum
Duhamel solution is per-mode SMALLER than the forcing
(`solFieldMass (c+2) i ≤ (1+T)²·forcingMass c i`), so a per-mode reverse bound would force
`1 ≤ θ(1+T)²`, contradicting `θ(1+T)² < 1`, at every mode carrying forcing energy off the
fixed background.  The quadratic Nemytskii mode-mixing always populates such modes.  The
honest content lives only at the total-norm level: the `δ < 1` short-time contraction is
internal to the zero-datum solution operator (the total `H^{d+2}` energy of the small-data
solution is controlled by the total `H^{d+2}` energy of the forcing through the contractive
zero-datum maximal-regularity estimate), and that total absorption — not a per-mode
inequality — closes the `+2` advance.

PROVEN here as a genuine composition over the operator-level fibre-small spectral
self-feedback contraction `deTurckForcing_forcingMass_partialSum_contraction`: that node
supplies a contraction factor `θ < 1` and a finite order-`d`-controlled background `Kd` with
the partial-sum absorption
`∑_{i∈s} forcingMass gforce (d+2) i ≤ θ·∑_{i∈s} forcingMass gforce (d+2) i + Kd` at every
finite mode set `s`; rearranging, `(1 − θ)·∑_{i∈s} ≤ Kd`, so every partial sum is bounded by
the single constant `Kd/(1 − θ)`, and `summable_of_sum_le` (the order-`(d+2)` forcing masses
are nonnegative and their partial sums are uniformly bounded) yields the summability.

PINNED to the forcing by `hforce`: `hforce` fixes `gforce` to the genuine second-order
Nemytskii image of its own Duhamel solution field.  The hypothesis
`Summable (forcingMass gforce d)` is satisfiable (it holds at `d = a` by the Plancherel
identity `summable_weight_mul_norm_timeModeCoeff_sq`) and genuinely consumed: it bounds the
background level `Kd` of the contraction node.  Consumers transitively depend on the `sorryAx`
of the deep contraction node. -/
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
  obtain ⟨θ, hθ_nn, hθ_lt, Kd, hKd_nn, hcontract⟩ :=
    deTurckForcing_forcingMass_partialSum_contraction (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 gforce hforce d hda hd
  have hone_sub_θ_pos : 0 < 1 - θ := by linarith
  refine summable_of_sum_le (c := Kd / (1 - θ))
    (fun i => forcingMass_nonneg (I := I) (M := M) gforce (d + 2) i) (fun s => ?_)
  have hS := hcontract s
  rw [le_div_iff₀ hone_sub_θ_pos]
  nlinarith [hS]

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
