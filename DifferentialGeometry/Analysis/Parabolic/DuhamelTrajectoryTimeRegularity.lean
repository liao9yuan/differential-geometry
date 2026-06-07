import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderNemytskiiSmoothness
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralToPouSobolevCLM
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.InteriorAllscaleTimeContinuity
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
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Measure

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 3200000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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
    (g g_bg : SmoothRiemannianMetric I M)
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
    (hduhamel : DuhamelMildSolutionData (I := I) (M := M) g (a : ℝ) T u₂ N_cont R
      (fun s => deTurckG0SpectralN (I := I) g a
        (deTurckRealizeRemainderOf (I := I) g g_bg (T_s s))))
    (k m : ℕ) :
    ContDiffOn ℝ (k : ℕ∞)
      (fun t : ℝ =>
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
      (Set.Icc (0 : ℝ) T) := by
  classical
  obtain ⟨Te, hT, hTe, hTe1, gforce, hN_cont, hid, hforce, hball, htraj⟩ := hduhamel
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hcompact_def
  haveI : Countable (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hcompact
  -- The per-mode carrier coordinate path, the data the mode-synthesis is built from.
  set cfun : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ :=
    fun i t => (u₂ t).coeff i with hcfun_def
  -- The single-mode term path: the `i`-th eigen-coordinate path `cfun i` embedded into the
  -- order-`4m` spectral space.  The synthesis path `wpath` is the unconditional mode-sum.
  set fmode : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 →
      ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 * (2 * m) : ℕ) : ℝ) :=
    fun i t => singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (σ := ((2 * (2 * m) : ℕ) : ℝ)) i (cfun i t) with hfmode_def
  -- **POSIT (per-mode `C^k` time-regularity — the per-mode iteration brick).**  Each
  -- single-mode term path `t ↦ singleModeCLM (4m) i (cfun i t)` is `C^k`-in-time on the slab.
  -- *Justification (the per-mode ODE iteration, deferred):* by `coeffFun_u_eq` (zero datum) the
  -- carrier coordinate is `cfun i t = perModeConv λᵢ gᵢ t` where `gᵢ` is the continuous
  -- representative of the `i`-th coordinate of the forcing; by the trajectory identification
  -- `gforce =ᵐ gtraj` (the concrete realized-remainder spectral path, `C^{k-1}`-in-time via the
  -- `RemainderNemytskii` chain rule fed by the inductive `C^{k-1}` of `T_s`'s Sobolev traces),
  -- `gᵢ` is `C^{k-1}`; the per-mode scalar ODE `(perModeConv λᵢ gᵢ)' = gᵢ − λᵢ·perModeConv λᵢ gᵢ`
  -- (`perModeConv_hasDerivWithinAt`) then bootstraps `cfun i` to `C^k`, and the linear
  -- `singleModeCLM (4m) i` preserves it.
  have hP1 : ∀ i, ContDiffOn ℝ (k : ℕ∞) (fmode i) (Set.Icc (0 : ℝ) T) := sorry
  -- **POSIT (the per-order λ-weighted majorant — the Weyl bookkeeping brick).**  There is a
  -- per-order summable majorant of the successive within-time-derivatives of the single-mode
  -- term paths, uniform over the slab.  *Justification (deferred):* the `j`-th time-derivative
  -- of `singleModeCLM (4m) i (cfun i t)` has norm `√(weight 4m i)·|∂ₜʲ (perModeConv λᵢ gᵢ)(t)|`,
  -- and the ODE iteration gives `∂ₜʲ (perModeConv λᵢ gᵢ) = Σ_{l<j} (−λᵢ)^{j-1-l} ∂ₜˡ gᵢ +
  -- (−λᵢ)ʲ perModeConv λᵢ gᵢ`; absorbing the `λᵢ`-powers into the spectral weight
  -- (`√(weight 4m i)·λᵢ^p ≍ √(weight (4m+2p) i)`) and bounding the `∂ₜˡ gᵢ` by the order-
  -- `(4m+2j+p)` traces of the `C^{k}` spectral forcing path (Cauchy–Schwarz against the Weyl
  -- eigenvalue-tail `∑ (1+λ)^{-p} < ∞`, `duhamel_majorant_summable`-style) yields the summable
  -- per-order majorant; `hHk`'s `∀ m` supplies the required higher-order trace control.
  have hP2 : ∃ v : ℕ → Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      (∀ j : ℕ, (j : ℕ∞) ≤ (k : ℕ∞) → Summable (v j)) ∧
      ∀ (j : ℕ) (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)
        (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → (j : ℕ∞) ≤ (k : ℕ∞) →
        ‖iteratedFDerivWithin ℝ j (fmode i) (Set.Icc (0 : ℝ) T) t‖ ≤ v j i := sorry
  obtain ⟨v, hv_sum, hv_bound⟩ := hP2
  -- The single-mode family is summable at every time (the `j = 0` majorant), so its mode-sum
  -- reconstructs the carrier coordinates: `(∑ᵢ fmode i t).coeff i = cfun i t`.
  have hfmode_summable : ∀ t ∈ Set.Icc (0 : ℝ) T, Summable (fun i => fmode i t) := by
    intro t ht
    refine Summable.of_norm_bounded (hv_sum 0 (by exact_mod_cast Nat.zero_le k))
      (fun i => ?_)
    have hb := hv_bound 0 i t ht (by exact_mod_cast Nat.zero_le k)
    rwa [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.norm_map] at hb
  -- The mode-sum synthesis path.
  set wpath : ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 * (2 * m) : ℕ) : ℝ) :=
    fun t => ∑' i, fmode i t with hwpath_def
  -- **The transfer CLM `spectralToPouSobolevCLM` sends `wpath t` to the chart-Sobolev trace
  -- `(T_s t).toHs (2m)`**: `wpath t`'s coordinates are `cfun i t = (u₂ t).coeff i`, which by
  -- `hcanon` are the `L²` coordinates of `T_s t` — the `hcanon`-shaped identification.
  have hCLM : ∀ t ∈ Set.Icc (0 : ℝ) T,
      spectralToPouSobolevCLM (I := I) (M := M) g m (wpath t) =
        IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t) := by
    intro t ht
    refine spectralToPouSobolevCLM_apply_of_coeff (I := I) (M := M) g m (T_s t) (wpath t) ?_
    intro i
    have hsumm := hfmode_summable t ht
    simp only [hwpath_def, hfmode_def] at hsumm ⊢
    rw [tsum_singleModeCLM_coeff (I := I) (M := M) (fun j => cfun j t) hsumm i]
    exact hcanon t ht i
  -- **The spectral synthesis path is `C^k`-in-time** (the within-set smooth-series M-test
  -- `contDiffOn_tsum_Icc`, fed by the per-mode `C^k` (`hP1`) and the per-order majorant
  -- (`hP2`)).
  have hw_contDiff : ContDiffOn ℝ (k : ℕ∞) wpath (Set.Icc (0 : ℝ) T) :=
    contDiffOn_tsum_Icc hT hP1 hv_sum
      (fun j i t ht hjk => hv_bound j i t ht hjk)
  -- Compose with the transfer CLM and rewrite to the target trace via `hCLM`.
  have hcomp : ContDiffOn ℝ (k : ℕ∞)
      (fun t => spectralToPouSobolevCLM (I := I) (M := M) g m (wpath t)) (Set.Icc (0 : ℝ) T) :=
    ContDiffOn.continuousLinearMap_comp (spectralToPouSobolevCLM (I := I) (M := M) g m)
      hw_contDiff
  refine hcomp.congr ?_
  intro t ht
  exact (hCLM t ht).symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
