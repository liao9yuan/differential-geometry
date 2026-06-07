import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-!
# All-order time regularity of the Duhamel carrier's Sobolev trace

The parabolic up-to-boundary smoothing of the Ricci–DeTurck remainder, in its purely
*temporal* form: the realized perturbation `T_s` of a carrier `u₂` that **is** the Duhamel
mild solution of `∂_t u = Δ_∇ u + N_cont(u)`, `u(0) = 0` (the structural datum
`DuhamelMildSolutionData`, with **ball-continuous** `N_cont`) has, at every supercritical
spatial Sobolev order `2 * m`, a `C^∞`-in-time Sobolev trace on the closed slab `Icc 0 T`
(one-sidedly differentiable at the initial datum `t = 0`).

This is the time-tower R1 of the joint-smoothing program: it strips the spatial and bundle
structure and isolates the genuinely parabolic input — the heat-semigroup smoothing of the
mild solution — as a one-real-variable Banach-valued regularity statement.  Per spectral mode
the Duhamel ODE is the scalar variation-of-constants `u_i(t) = ∫₀ᵗ e^{−λᵢ(t−τ)} N_i(τ) dτ`
(the homogeneous part vanishes since the initial datum is `0`): the heat factor `e^{−λᵢ(t−τ)}`
is `C^∞` in `t`, and the continuous forcing `N_cont` along a continuous field gives a `C¹`
Duhamel integral whose own regularity then bootstraps to all orders; the weighted-summability
(Weyl) of the spectral coordinates packages the per-mode tower into the `H^{2m}` trace.

## Main result

* `realizedPerturbation_timeContDiffTower_uptoZero` — from the Duhamel mild-solution datum
  (with `hcanon` tying `T_s`'s `L²` coordinates to the carrier's spectral coordinates), for
  every `k m : ℕ` the trace `t ↦ (T_s t).toHs (2 * m)` is `ContDiffOn ℝ k` on `Icc 0 T`.

## Why this is not hypothesis-packaging, and why it rejects the kink families

The hypotheses constrain the carrier `u₂` / the realized section `T_s` / the forcing as a
**time-indexed Banach-space integral identity** (`DuhamelMildSolutionData`) together with the
coordinate tie `hcanon`; the conclusion is the `ContDiffOn ℝ k` (a one-real-variable
Banach-valued time-regularity) of the Sobolev trace — a different statement, derived *from*
the identity (the identity does not assume it).  The `C¹`-not-`C²` kink
`T_s t := (t − t₀)|t − t₀| · S₀` cannot satisfy `DuhamelMildSolutionData`: the Duhamel mild
solution with ball-continuous `N_cont` and a continuous-in-time field is `C^∞`-in-time on the
interior, hence is *not* a `C¹`-not-`C²` carrier, so the kink violates the pointwise identity
`ι (u₂ s) = (maxRegDuhamelMap … 0 gforce).toFun s`.  The `C⁰`-kink `|t − t₀| · S₀` violates
already `hreg` (no interior time-derivative). -/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **All-order time regularity of the Duhamel carrier's `H^{2m}` Sobolev trace
(the parabolic time-tower R1).**

For a smooth-section family `T_s : ℝ → SmoothCcTensor g 0 2` realizing a carrier
`u₂ : ℝ → H^{a+2}(g)` whose spectral coordinates are the `L²` coordinates of `T_s` (`hcanon`),
which is time-continuous up to `0` (`hcont`), has the interior strong derivative
`∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` (`hreg`), every supercritical `H^{2k}` trace of `T_s` is
time-continuous up to `0` (`hHk`), and — the structural pinning — `u₂` IS the Duhamel mild
solution of `∂_t u = Δ_∇ u + N_cont(u)`, `u(0) = 0` with ball-continuous `N_cont`
(`hduhamel`): for every order `k` of time-differentiation and every spatial Sobolev exponent
`2 * m`, the Banach-valued trace path `t ↦ (T_s t).toHs (2 * m)` is `C^k` on the closed slab
`Icc 0 T` (one-sidedly at `t = 0`).

The hypotheses pin the carrier to the genuine Duhamel parabolic trajectory; the conclusion is
the all-order time regularity of its Sobolev trace.  These are distinct (one a Banach integral
identity, the other a `ContDiffOn` of one real variable) — no packaging — and the `C¹`-not-`C²`
kink is rejected by `hduhamel` (see the module docstring litmus). -/
theorem realizedPerturbation_timeContDiffTower_uptoZero
    (g : SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {a : ℕ} {T : ℝ} {R : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g 0 2 ((a : ℝ) + 2))
    (N_cont : tensorHs (I := I) (M := M) g 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g 0 2 (a : ℝ))
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (hHk : ∀ (k : ℕ), 2 * k > Module.finrank ℝ E + 4 →
      ContinuousOn (fun s : ℝ =>
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) (T_s s))
        (Set.Icc 0 T))
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hcanon : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hduhamel : DuhamelMildSolutionData (I := I) (M := M) g (a : ℝ) T u₂ N_cont R)
    (k m : ℕ) :
    ContDiffOn ℝ (k : ℕ∞)
      (fun t : ℝ =>
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
      (Set.Icc (0 : ℝ) T) := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
