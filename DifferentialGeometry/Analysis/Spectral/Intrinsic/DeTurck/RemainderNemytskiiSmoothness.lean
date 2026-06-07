import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0GenuineNonlinearity
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-! # All-order Fréchet smoothness of the concrete DeTurck-remainder Nemytskii map

The map-level (purely *spatial*) all-order differentiability of the concrete gauge-cancelled
Ricci–DeTurck-remainder Nemytskii map, on the fibre-small validity ball, together with the
time-path chain-rule corollary the per-mode Duhamel bootstrap consumes.

The Nemytskii map this is about is the exact composition the maximal-regularity engine's forcing
factors through (`deTurckGenuineN_firstOrder_operatorLoss`, `forcing_continuous_interior`):
```
T ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg T) ,
```
the order-`a` coordinate-spectral nonlinearity (`deTurckG0SpectralN`, linear-continuous on `L²`
coordinates) read off the realized Ricci–DeTurck remainder
`deTurckRealizeRemainderOf g₀ g_bg T = deTurckRHSSection g_bg (g₀ + ccTensorBilinSymm g₀ T) −
Δ_∇ T` of the `(0,2)`-perturbation `T`.

## Why the validity-ball restriction is what makes the statement TRUE (the truncation litmus)

`deTurckRealizeRemainderOf g₀ g_bg T` is defined by a `dif` on the fibre-small guard
`∃ δ < 1, gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ` (`PosDefPerturbation.gFibreOpBound`,
the operator bound `|h x v w| ≤ δ √(g₀ v v) √(g₀ w w)`): on the fibre-small locus it is the
genuine realized remainder section (a rational-polynomial functional of the realized metric's
`≤ 2`-jet — the retag `−2 Ric + Lie` is rational in the realized metric through the inverse-Gram
Neumann series `invGramPerturbation`, the chart structural Christoffel bricks are polynomial, and
`Δ_∇` is linear — while `deTurckG0SpectralN` is the *linear* `L²`-coordinate projection), and
**off** the fibre-small locus it is the **zero** section.

This finite-`dif` truncation is exactly why the **global** map
`T ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg T)` is **not** differentiable —
not even `C¹` — across the fibre-small boundary `δ ↗ 1`: as the realized metric `g₀ +
ccTensorBilinSymm g₀ T` degenerates, the genuine remainder section does **not** tend to `0` (the
inverse-Gram blows up, `‖−2 Ric‖` does not vanish), yet the truncation switches the value to `0`,
a jump discontinuity in value, hence a fortiori a non-removable first-order kink at the boundary
of the open fibre-small region.  (This is the map-level analogue of the *gated*-gauge
discontinuity documented in `DeTurckG0GenuineNonlinearity.lean`: the gate jumps to `g₀` off its
dense-complement locus.)  A global `ContDiff`/`ContDiffOn ℝ ⊤ … Set.univ` claim for this map is
therefore **FALSE as stated**.

The fix — and the content posited here — is the *restricted* statement: on a closed ball in the
intrinsic chart-Sobolev `H^q` norm of radius `ρ` chosen small enough that the supercritical
embedding `H^q ↪ C⁰` (`2 a > dim M + 4`, `q ≥ a + 2`) forces every section in the ball to be
fibre-small with a uniform `δ < 1` (so the realized metric stays uniformly non-degenerate and the
`dif` is uniformly the genuine branch), the map is the restriction of the genuine rational-polynomial
functional, which **is** `C^∞`: the inverse-Gram Neumann series converges uniformly on the
non-degenerate ball, so the realized remainder is a uniformly-convergent power series in the metric
`2`-jet, smooth in the `H^q` input; post-composing the *linear continuous* spectral projection
`deTurckG0SpectralN` keeps it `C^∞` into the spectral scale `H^a`.  The validity-ball restriction
is what turns the truncated, globally-non-`C¹` map into a genuinely smooth one.

## The honest scale shape (two derivatives lost)

The second-order Ricci–DeTurck retag is a second-order quasilinear operator in the realized
metric, so the map **loses two derivatives**: it takes the perturbation's order-`(a + 2)`
intrinsic chart-Sobolev content (`q ≥ a + 2`) to the order-`a` *spectral* output `tensorHs g₀ 0 2
(a : ℝ)`.  This is the same `H^{·+2} → H^{·}` accounting established by the on-disk chart-RHS
tower (`exists_realizedRHSRemainder_weightedHa_le_toHs_highOrder`: weighted-`Hᵃ` of the spectral
coordinate difference controlled by the intrinsic `H^{a+2}` perturbation norm) and by the engine
convention (`deTurckGenuineN_firstOrder_operatorLoss`, `DuhamelMildSolutionData`: spectral
`N : H^{a+1} → H^a` with the carrier in `H^{a+2}`).  The map-level differentiability is therefore
phrased with the input living in the intrinsic chart-Sobolev Hilbert space
`TensorPouSobolevHilbert g₀ 0 2 q` (the `toHs q` scale, `q ≥ a + 2`) and the output in the
spectral scale `H^a`, with the smooth extension `Φ` factoring the section-level composite through
`SmoothCcTensor.toHs q`.

## What lives here

* `exists_deTurckRemainderNemytskii_contDiffOn_ball` — **the posit** (body `sorry`): for `q ≥ a +
  2` and supercritical `a`, there is a radius `ρ > 0` and a map
  `Φ : TensorPouSobolevHilbert g₀ 0 2 q → tensorHs g₀ 0 2 (a : ℝ)` that is `ContDiffOn ℝ ∞` on
  the closed `H^q`-ball of radius `ρ`, and which factors the concrete section-level Nemytskii
  composite: `Φ ((T).toHs q) = deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg T)` for
  every smooth section `T` whose `toHs q` lies in the ball (so every such `T` is fibre-small and
  the realized remainder is the genuine branch).  This is the all-order map-level upgrade of the
  on-disk order-`0` ball-continuity node
  `deTurckRealizeRemainderOf_pouToHs_continuous_of_chartJet2Control`.  The rational-polynomial /
  inverse-Gram-Neumann grind discharging the `ContDiffOn` is its own future fill (possibly
  multi-dispatch); the posit is the spatial truth-maker the time bootstrap stands on.

* `deTurckRemainderNemytskii_timePath_contDiffOn` — **proven glue** (the chain-rule corollary the
  per-mode Duhamel bootstrap consumes): if a time-path of smooth sections `T_s : ℝ → SmoothCcTensor
  g₀ 0 2` has its intrinsic `H^q` Sobolev trace `t ↦ (T_s t).toHs q` `ContDiffOn ℝ k` on the slab
  `Icc 0 T` and stays inside the validity ball, then the spectral forcing path
  `t ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (T_s t))` is `ContDiffOn ℝ k`
  into the spectral scale `H^a`.  Proven by `ContDiffOn.comp` of `Φ` (downgraded `∞ → k`) with the
  `H^q` trace path, then `ContDiffOn.congr` along the factoring.

## Vindication of the time bootstrap (closing the `C¹`-kink gap)

The Duhamel mild solution per spectral mode is `u_i(t) = ∫₀ᵗ e^{−λᵢ(t−τ)} N_i(τ) dτ` (the
homogeneous part vanishes since the initial datum is `0`); bootstrapping its time regularity from
order `k` to `k + 1` needs the forcing path `t ↦ N_cont(carrier t)` to be `C^k` in time, which —
since the carrier path's `H^q` trace is `C^k` and stays in the ball — is **exactly** the corollary
here.  Order `k = 1` is the previously-open `C¹`-kink: the bare continuity of the forcing only gave
a `C¹` Duhamel integral; with the *all-order* map-level smoothness `Φ` posited here, every
order-`k` is forced, so the carrier's Sobolev trace is `C^∞`-in-time on the slab
(`realizedPerturbation_timeContDiffTower_uptoZero`), closing the `C¹`-not-`C²` kink gap the
ball-continuity node alone could not.

## Trap screens

* **T6 (no smuggled time-regularity).**  `exists_deTurckRemainderNemytskii_contDiffOn_ball` is a
  purely **spatial** map-level statement: it quantifies no time variable and hypothesizes no
  regularity of any trajectory; the time-path enters only in the *corollary*, as an explicit
  hypothesis on `T_s`.
* **T2 (`g₀`/`g_bg`).**  Both metrics are free parameters tied by the standing closed-manifold
  context, exactly as in `deTurckRealizeRemainderOf`.
* **No packaging.**  The posit's conclusion is the existence of a `ContDiffOn` extension with a
  factoring equation; the corollary's conclusion is a `ContDiffOn` of one real variable derived by
  composition.  Neither hypothesis is (defeq to) its conclusion.
* **Zero-witness sanity.**  The zero perturbation `T = 0` is fibre-small (`gFibreOpBound g₀ 0 0`,
  `0 < 1`), so `deTurckRealizeRemainderOf g₀ g_bg 0` is the *finite* `g₀`-remainder `−2 Ric(g₀)`-type
  section, not a degenerate value; the statement is about **differentiability** of the map, not the
  vanishing of any value, and is non-vacuous there. -/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 3200000

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Map-level all-order Fréchet smoothness of the concrete DeTurck-remainder Nemytskii map on
the fibre-small validity ball (the spatial posit; body `sorry`).**

For a supercritical spectral order `a` (`2 a > dim M + 4`) and an intrinsic chart-Sobolev input
order `q` at least the honest two-derivative loss `q ≥ a + 2`, there is a radius `ρ > 0` and a map
```
Φ : TensorPouSobolevHilbert g₀ 0 2 q → tensorHs g₀ 0 2 (a : ℝ)
```
on the intrinsic order-`q` chart-Sobolev Hilbert space such that:

* (`contDiffOn`) `Φ` is `ContDiffOn ℝ ∞` (`C^∞`) on the closed `H^q`-ball of radius `ρ` about the
  origin; and

* (`factor`) `Φ` factors the concrete section-level Nemytskii composite through `SmoothCcTensor.toHs
  q`: for every smooth compactly-supported `(0,2)`-section `T` whose intrinsic `H^q` class
  `(T).toHs q` lies in that ball,
  ```
  Φ ((T).toHs q) = deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg T) .
  ```

The ball radius `ρ` is part of the existential payload — it is chosen small enough that the
supercritical embedding `H^q ↪ C⁰` makes every section in the ball uniformly fibre-small (uniform
`δ < 1`), so the realized metric `g₀ + ccTensorBilinSymm g₀ T` stays uniformly non-degenerate, the
`deTurckRealizeRemainderOf` `dif`-guard is uniformly the genuine branch, and the inverse-Gram
Neumann series of the retag converges uniformly; the genuine remainder is then a uniformly-convergent
power series in the `H^q` input (rational-polynomial in the metric `≤ 2`-jet), and post-composing
the *linear continuous* spectral projection `deTurckG0SpectralN` yields a `C^∞` map into `H^a`.

**Why the restriction is essential (the truncation litmus, see the module docstring).**  The
analogous *global* claim `ContDiffOn ℝ ∞ … Set.univ` for `T ↦ deTurckG0SpectralN g₀ a
(deTurckRealizeRemainderOf g₀ g_bg T)` is **false**: the finite `dif`-truncation switches the value
to `0` across the fibre-small boundary `δ ↗ 1`, where the genuine remainder does not vanish (the
inverse-Gram blows up), a value jump and hence a non-removable first-order kink — the map is not even
`C¹` globally.  The radius-`ρ` ball restriction excises that boundary, which is exactly what makes
the statement true.

This is the all-order map-level upgrade of the on-disk order-`0` ball-continuity node
`deTurckRealizeRemainderOf_pouToHs_continuous_of_chartJet2Control` (same ball, same
`toHs`-factored shape, `ContinuousOn` lifted to `ContDiffOn ℝ ∞` and stated at the map level for the
chain rule).  T6: it is purely spatial — no time variable, no trajectory regularity.  No packaging:
the conclusion is an existence-of-smooth-extension-with-factoring, structurally distinct from any
hypothesis.

The body is `sorry`: the rational-polynomial / inverse-Gram-Neumann smoothness grind discharging
the `ContDiffOn` is its own future fill (possibly multi-dispatch). -/
theorem exists_deTurckRemainderNemytskii_contDiffOn_ball
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (q : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) (hq : a + 2 ≤ q) :
    ∃ (ρ : ℝ) (Φ : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      0 < ρ ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) Φ
        (Metric.closedBall
          (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ) ∧
      ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q T ∈
            Metric.closedBall
              (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ →
          Φ (IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q T)
            = deTurckG0SpectralN (I := I) g₀ a
                (deTurckRealizeRemainderOf (I := I) g₀ g_bg T) := sorry

/-- **The chain-rule mechanism (sorry-free reusable core).**

For an already-supplied smooth extension `Φ` of the section-level Nemytskii composite on the
radius-`ρ` `H^q`-ball (the data the posit produces), a time-path whose `H^q` trace is `ContDiffOn ℝ
k` and stays in that ball has a `ContDiffOn ℝ k` spectral forcing path.  This is pure
`ContDiffOn.comp` + `ContDiffOn.congr` glue, independent of the supercriticality bookkeeping — the
genuine reusable mechanism the public corollary instantiates with the posit's output. -/
private theorem deTurckRemainderNemytskii_timePath_contDiffOn_of_extension
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (q : ℕ)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {T : ℝ} {k : ℕ}
    {ρ : ℝ}
    (Φ : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q →
        tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hΦ : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φ
        (Metric.closedBall
          (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ))
    (hfactor : ∀ S : Integral.L2.SmoothCcTensor g₀ 0 2,
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q S ∈
            Metric.closedBall
              (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ →
          Φ (IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q S)
            = deTurckG0SpectralN (I := I) g₀ a
                (deTurckRealizeRemainderOf (I := I) g₀ g_bg S))
    (hpath : ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q (T_s t))
        (Set.Icc (0 : ℝ) T))
    (hball : ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q (T_s t) ∈
          Metric.closedBall
            (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ) :
    ContDiffOn ℝ (k : ℕ∞)
      (fun t : ℝ =>
        deTurckG0SpectralN (I := I) g₀ a (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s t)))
      (Set.Icc (0 : ℝ) T) := by
  -- The chart-Sobolev `H^q` trace path of `T_s`, the inner map of the composition.
  set ψ : ℝ → IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q :=
    fun t => IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q (T_s t) with hψ
  -- `Φ ∘ ψ` is `ContDiffOn ℝ k`: `Φ` (downgraded `∞ → k`) composed with the `C^k` path `ψ`, whose
  -- image lands in the validity ball by `hball`.
  have hk_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcomp : ContDiffOn ℝ (k : ℕ∞) (Φ ∘ ψ) (Set.Icc (0 : ℝ) T) :=
    (hΦ.of_le hk_le).comp hpath (fun t ht => hball t ht)
  -- Rewrite the composite to the target spectral forcing path via the factoring equation.
  refine hcomp.congr ?_
  intro t ht
  simp only [Function.comp_apply, hψ]
  exact (hfactor (T_s t) (hball t ht)).symm

/-- **The time-path chain-rule corollary the per-mode Duhamel bootstrap consumes (proven glue over
the map-level posit).**

For a supercritical spectral order `a` (`2 a > dim M + 4`) and chart-Sobolev input order `q ≥ a +
2` (the honest two-derivative loss), there is a validity radius `ρ > 0` such that: any time-path of
smooth compactly-supported `(0,2)`-sections `T_s : ℝ → SmoothCcTensor g₀ 0 2` whose intrinsic
order-`q` chart-Sobolev trace `t ↦ (T_s t).toHs q` is `ContDiffOn ℝ k` on the slab `Icc 0 T`
(`hpath`) and stays inside the radius-`ρ` validity ball (`hball`) has a `ContDiffOn ℝ k` spectral
forcing path
```
t ↦ deTurckG0SpectralN g₀ a (deTurckRealizeRemainderOf g₀ g_bg (T_s t))
```
into the order-`a` spectral scale `tensorHs g₀ 0 2 (a : ℝ)`.

This is **proven glue over** `exists_deTurckRemainderNemytskii_contDiffOn_ball`: the radius `ρ` and
the smooth extension `Φ` come from the posit, and the conclusion is the chain rule `ContDiffOn.comp`
of `Φ` (downgraded `∞ → k`) with the `H^q` trace path (`MapsTo` from `hball`), rewritten along the
factoring by `ContDiffOn.congr` (the sorry-free core
`deTurckRemainderNemytskii_timePath_contDiffOn_of_extension`).  It transitively depends on `sorryAx`
**exactly** through the map-level posit.

This is the all-order forcing-path smoothness the per-mode Duhamel time bootstrap
(`realizedPerturbation_timeContDiffTower_uptoZero`) needs to advance the carrier's Sobolev trace
from order `k` to order `k + 1`, closing the `C¹`-kink gap (see the module docstring).

T6: the time-regularity here is an explicit hypothesis on the supplied path `T_s`, not a property
the spatial posit assumes.  No packaging: the conclusion is a `ContDiffOn` of one real variable
derived by composition from the spatial smoothness. -/
theorem deTurckRemainderNemytskii_timePath_contDiffOn
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) (q : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) (hq : a + 2 ≤ q) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {T : ℝ} {k : ℕ},
        ContDiffOn ℝ (k : ℕ∞)
            (fun t : ℝ =>
              IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q (T_s t))
            (Set.Icc (0 : ℝ) T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
            IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) q (T_s t) ∈
              Metric.closedBall
                (0 : IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 q) ρ) →
        ContDiffOn ℝ (k : ℕ∞)
          (fun t : ℝ =>
            deTurckG0SpectralN (I := I) g₀ a (deTurckRealizeRemainderOf (I := I) g₀ g_bg (T_s t)))
          (Set.Icc (0 : ℝ) T) := by
  obtain ⟨ρ, Φ, hρ, hΦ, hfactor⟩ :=
    exists_deTurckRemainderNemytskii_contDiffOn_ball (I := I) g₀ g_bg a q ha hq
  refine ⟨ρ, hρ, fun T_s {T} {k} hpath hball => ?_⟩
  exact deTurckRemainderNemytskii_timePath_contDiffOn_of_extension (I := I) g₀ g_bg a q T_s
    Φ hΦ hfactor hpath hball

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

end
