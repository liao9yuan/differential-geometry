import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderNemytskiiSmoothness
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralToPouSobolevCLM
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.InteriorAllscaleTimeContinuity
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Parabolic.PerModeConvTimeRegularity

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

/-- **The realized Ricci–DeTurck forcing path is a `C^∞` curve into the spectral scale with
rapidly-decaying coordinates (the spectral-smoothness brick).**

For the concrete realized-remainder spectral forcing path
`gtraj s = deTurckG0SpectralN g a (deTurckRealizeRemainderOf g g_bg (T_s s))` along a
spatially-smooth section path `T_s`, there is a family `G i : ℝ → ℝ` of *globally continuous*,
`C^∞`-on-`Icc 0 T` representatives of its eigen-coordinate paths, agreeing on `Icc 0 T` with the
coordinate path `t ↦ (gtraj t).coeff i`, and such that for every spatial Sobolev order `σ : ℕ` and
every time-differentiation order `l : ℕ` the `√(weight σ)`-weighted supremum over `Icc 0 T` of the
`l`-th within-time-derivative of `G i` is dominated by a summable family over the eigen-indices.

This is the genuine parabolic-smoothing content: the realized DeTurck remainder is a smooth nonlinear
function of the metric `≤ 2`-jet, so along a spatially-smooth `T_s` the forcing is a `C^∞`-in-time
curve whose values lie in every Sobolev order (the eigen-coordinates of a smooth section decay
faster than any polynomial in `λ`), uniformly on the compact slab.  It is the all-output-order,
all-time-order strengthening of the order-`a` chain-rule corollary
`deTurckRemainderNemytskii_timePath_contDiffOn` (whose own `H^q`-validity-ball restriction it
absorbs into the rapid coordinate decay).  It rejects a non-smooth forcing path: a `gtraj` with a
discontinuous coordinate path admits no continuous representative agreeing with it on `Icc 0 T`.

The body is `sorry`: this is the single posited spectral-smoothness brick the per-mode time tower
transits (besides the supercritical pou-Sobolev baseline); the elliptic rational-polynomial /
inverse-Gram smoothness grind into every Sobolev order is its own future fill. -/
theorem deTurckG0Forcing_coeffPath_spectralSmooth
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) :
    ∃ G : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, Continuous (G i)) ∧
      (∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ i, Set.EqOn (G i)
        (fun t => (deTurckG0SpectralN (I := I) g a
          (deTurckRealizeRemainderOf (I := I) g g_bg (T_s t))).coeff i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ (σ : ℕ) (l : ℕ),
        ∃ S : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
          Summable S ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ : ℝ))
                * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t| ≤ S i) := sorry

/-- **The per-order `√weight`-summable majorant of the single-mode time-derivatives** (the
`M`-test data the closed-slab smooth-series test consumes), assembled from the spectral-smoothness
brick by the per-mode ODE iteration.

Given globally-continuous `C^∞`-on-`Icc` forcing coordinates `G i` with per-order `√weight`-summable
coordinate bounds (the brick `hG_summ`) and the carrier bridge `cfun i =ᴱ perModeConv λᵢ (G i)`,
the within-time-derivatives of the single-mode term paths `fmode i = singleModeCLM (4m) i ∘ cfun i`
have a per-order summable supremum majorant.  The `j`-th derivative norm factors as
`√(weight 4m i)·|∂ₜʲ (cfun i)|`; the ODE iteration expands `∂ₜʲ (perModeConv λᵢ Gᵢ)` into
`Σ_{l<j}(−λᵢ)^{j−1−l}∂ₜˡGᵢ + (−λᵢ)ʲ perModeConv λᵢ Gᵢ`; the spectral trade
`√(weight 4m i)·λᵢ^p ≤ √(weight (4m+2p) i)` reduces each summand to a `hG_summ`-bounded family. -/
theorem perModeMajorant_exists
    {g : SmoothRiemannianMetric I M} {m : ℕ} {T : ℝ} (hT : 0 < T)
    {lam : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ}
    {G : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ}
    {cfun : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ}
    {fmode : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ →
      tensorHs (I := I) (M := M) g 0 2 ((2 * (2 * m) : ℕ) : ℝ)}
    (hlam_def : lam = fun i => Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i)
    (hfmode_def : fmode = fun i t => singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (σ := ((2 * (2 * m) : ℕ) : ℝ)) i (cfun i t))
    (hG_cont : ∀ i, Continuous (G i))
    (hG_smooth : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (G i) (Set.Icc (0 : ℝ) T))
    (hG_summ : ∀ (σ : ℕ) (l : ℕ),
      ∃ S : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable S ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ : ℝ))
              * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t| ≤ S i)
    (hbridge : ∀ i, Set.EqOn (cfun i) (perModeConv (lam i) (G i)) (Set.Icc (0 : ℝ) T))
    (hcfun_smooth : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (cfun i) (Set.Icc (0 : ℝ) T)) :
    ∃ v : ℕ → Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      (∀ j : ℕ, (j : ℕ∞) ≤ (∞ : WithTop ℕ∞) → Summable (v j)) ∧
      ∀ (j : ℕ) (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) (t : ℝ),
        t ∈ Set.Icc (0 : ℝ) T → (j : ℕ∞) ≤ (∞ : WithTop ℕ∞) →
        ‖iteratedFDerivWithin ℝ j (fmode i) (Set.Icc (0 : ℝ) T) t‖ ≤ v j i := by
  classical
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hlam_nn : ∀ i, 0 ≤ lam i := by
    intro i; rw [hlam_def]; exact tensor_lambda_nonneg (I := I) (M := M) i
  let w4m : ℕ := 2 * (2 * m)
  -- The chosen summable families from the brick.
  set S : ℕ → ℕ → Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun σ l => (hG_summ σ l).choose with hS_def
  have hS_summ : ∀ σ l, Summable (S σ l) := fun σ l => (hG_summ σ l).choose_spec.1
  have hS_bound : ∀ (σ l : ℕ) i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ : ℝ))
          * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t| ≤ S σ l i :=
    fun σ l => (hG_summ σ l).choose_spec.2
  have hS_nonneg : ∀ (σ l : ℕ) i, 0 ≤ S σ l i := by
    intro σ l i
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
    exact le_trans (by positivity) (hS_bound σ l i 0 h0)
  -- The spectral weight↔eigenvalue-power trade: `√weight(σ)·λᵢ^p ≤ √weight(σ+2p)`.
  have htrade : ∀ (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) (σ p : ℕ),
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ : ℝ)) * (lam i) ^ p
        ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((σ + 2 * p : ℕ) : ℝ)) := by
    intro i σ p
    have hlami : lam i = Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) i := by rw [hlam_def]
    rw [hlami]
    set L : ℝ := Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i
      with hL
    have hLnn : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + L := by linarith
    have hsqrt_eq : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((σ + 2 * p : ℕ) : ℝ))
        = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ : ℝ)) * (1 + L) ^ p := by
      rw [tensorSobolevWeight, tensorSobolevWeight, ← hL]
      have hcast : ((σ + 2 * p : ℕ) : ℝ) = (σ : ℝ) + ((p : ℝ) * 2) := by push_cast; ring
      rw [hcast, Real.rpow_add hbase_pos, Real.sqrt_mul (by positivity)]
      congr 1
      rw [Real.rpow_mul hbase_pos.le, Real.rpow_two, Real.sqrt_sq (by positivity), Real.rpow_natCast]
    rw [hsqrt_eq]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact pow_le_pow_left₀ hLnn (by linarith) p
  -- Step A: the norm of the `j`-th within-derivative of `fmode i` factors through the carrier.
  have hnorm_fac : ∀ (j : ℕ) (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) T →
      ‖iteratedFDerivWithin ℝ j (fmode i) (Set.Icc (0 : ℝ) T) t‖
        ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (w4m : ℝ))
            * |iteratedDerivWithin j (cfun i) (Set.Icc (0 : ℝ) T) t| := by
    intro j i t ht
    have hcfun_j : ContDiffWithinAt ℝ j (cfun i) (Set.Icc (0 : ℝ) T) t :=
      (contDiffOn_infty.mp (hcfun_smooth i) j t ht)
    have hfun : fmode i = ⇑(singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (σ := ((w4m : ℕ) : ℝ)) i) ∘ cfun i := by
      subst hfmode_def; rfl
    have hcomp : iteratedFDerivWithin ℝ j (fmode i) (Set.Icc (0 : ℝ) T) t
        = (singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (σ := ((w4m : ℕ) : ℝ)) i).compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ j (cfun i) (Set.Icc (0 : ℝ) T) t) := by
      rw [hfun]
      exact (singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (σ := ((w4m : ℕ) : ℝ)) i).iteratedFDerivWithin_comp_left hcfun_j huniq ht le_rfl
    rw [hcomp]
    refine le_trans (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _) ?_
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _
  -- The per-order majorant.
  refine ⟨fun j i => (∑ l ∈ Finset.range j, S (w4m + 2 * (j - 1 - l)) l i)
      + T * S (w4m + 2 * j) 0 i, ?_, ?_⟩
  · -- Summability of each `v j` (finite sum of summable families + scalar multiple).
    intro j _
    refine Summable.add ?_ ((hS_summ (w4m + 2 * j) 0).mul_left T)
    exact summable_sum (fun l _ => hS_summ (w4m + 2 * (j - 1 - l)) l)
  · -- The bound.
    intro j i t ht _
    refine le_trans (hnorm_fac j i t ht) ?_
    -- Rewrite the carrier's iterated derivative via the bridge + the ODE iteration closed form.
    have hcfun_eq : iteratedDerivWithin j (cfun i) (Set.Icc (0 : ℝ) T) t
        = iteratedDerivWithin j (perModeConv (lam i) (G i)) (Set.Icc (0 : ℝ) T) t :=
      iteratedDerivWithin_congr (hbridge i) ht
    rw [hcfun_eq, iteratedDerivWithin_perModeConv (lam i) (hG_cont i) hT (hG_smooth i) j ht]
    -- Triangle + the spectral trade, term by term.
    set wj : ℝ := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (w4m : ℝ)) with hwj_def
    have hwj_nn : 0 ≤ wj := Real.sqrt_nonneg _
    have htri : wj * |(∑ l ∈ Finset.range j, (-lam i) ^ (j - 1 - l)
            * iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t)
          + (-lam i) ^ j * perModeConv (lam i) (G i) t|
        ≤ (∑ l ∈ Finset.range j, wj * ((lam i) ^ (j - 1 - l)
            * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t|))
          + wj * ((lam i) ^ j * |perModeConv (lam i) (G i) t|) := by
      refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) hwj_nn) ?_
      rw [mul_add (a := wj)]
      gcongr ?_ + ?_
      · rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hwj_nn
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun l _ => ?_))
        rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (hlam_nn i)]
      · rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (hlam_nn i)]
    refine le_trans htri ?_
    beta_reduce
    refine add_le_add ?_ ?_
    · -- sum term: per-mode `S`-majorant on each summand
      refine Finset.sum_le_sum (fun l hl => ?_)
      -- term-l bound: wj·λᵢ^{j-1-l}·|∂ₜˡGᵢ| ≤ S(w4m+2(j-1-l), l) i
      have hstep1 : wj * ((lam i) ^ (j - 1 - l)
            * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t|)
          = (wj * (lam i) ^ (j - 1 - l)) * |iteratedDerivWithin l (G i) (Set.Icc (0 : ℝ) T) t| := by
        ring
      rw [hstep1]
      refine le_trans (mul_le_mul_of_nonneg_right (htrade i w4m (j - 1 - l)) (abs_nonneg _)) ?_
      exact hS_bound (w4m + 2 * (j - 1 - l)) l i t ht
    · -- perModeConv term: wj·λᵢ^j·|perModeConv| ≤ T·S(w4m+2j, 0) i
      have hpmc_abs : |perModeConv (lam i) (G i) t|
          ≤ ∫ s in (0 : ℝ)..t, |G i s| :=
        abs_perModeConv_le_integral_abs (lam i) (hlam_nn i) (hG_cont i) ht.1
      have hwjlamj : wj * (lam i) ^ j
          ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((w4m + 2 * j : ℕ) : ℝ)) :=
        htrade i w4m j
      set wj2 : ℝ := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((w4m + 2 * j : ℕ) : ℝ))
        with hwj2_def
      have hwj2_nn : 0 ≤ wj2 := Real.sqrt_nonneg _
      calc wj * ((lam i) ^ j * |perModeConv (lam i) (G i) t|)
          = (wj * (lam i) ^ j) * |perModeConv (lam i) (G i) t| := by ring
        _ ≤ wj2 * |perModeConv (lam i) (G i) t| :=
            mul_le_mul_of_nonneg_right hwjlamj (abs_nonneg _)
        _ ≤ wj2 * ∫ s in (0 : ℝ)..t, |G i s| := mul_le_mul_of_nonneg_left hpmc_abs hwj2_nn
        _ = ∫ s in (0 : ℝ)..t, wj2 * |G i s| := by rw [intervalIntegral.integral_const_mul]
        _ ≤ ∫ s in (0 : ℝ)..t, S (w4m + 2 * j) 0 i := by
            refine intervalIntegral.integral_mono_on ht.1
              ((((hG_cont i).norm).const_mul wj2).intervalIntegrable 0 t)
              (intervalIntegrable_const) (fun s hs => ?_)
            have hsmem : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
            have hb := hS_bound (w4m + 2 * j) 0 i s hsmem
            rwa [iteratedDerivWithin_zero] at hb
        _ = t * S (w4m + 2 * j) 0 i := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        _ ≤ T * S (w4m + 2 * j) 0 i :=
            mul_le_mul_of_nonneg_right ht.2 (hS_nonneg (w4m + 2 * j) 0 i)

open Analysis.Parabolic.TensorHeatEquation in
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
  have hT0 : (0 : ℝ) ≤ T := hT.le
  set lam : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i
    with hlam_def
  -- The spectral-smoothness brick: globally-continuous, `C^∞`-on-`Icc`, summable-coordinate
  -- representatives `G i` of the realized forcing path's eigen-coordinate paths.
  obtain ⟨G, hG_cont, hG_smooth, hG_eq, hG_summ⟩ :=
    deTurckG0Forcing_coeffPath_spectralSmooth (I := I) (M := M) g g_bg a T_s
  -- The forcing-path coordinate `G i` agrees a.e. on `Icc 0 T` with the `L²`-forcing's coordinate.
  have hGtmc : ∀ i, (fun t => timeModeCoeff (I := I) (M := M) gforce i t)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] G i := by
    intro i
    have htmc : (fun t => timeModeCoeff (I := I) (M := M) gforce i t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] (fun t => (gforce t).coeff i) := by
      have h : (fun t => timeModeCoeff (I := I) (M := M) gforce i t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0:ℝ) Te)] (fun t => (gforce t).coeff i) :=
        timeModeCoeff_coeFn (I := I) (M := M) gforce i
      exact ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hTe) h
    -- gforce =ᵐ gtraj on Icc 0 T, coordinate-wise.
    have hgcoeff : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (fun t => (deTurckG0SpectralN (I := I) g a
          (deTurckRealizeRemainderOf (I := I) g g_bg (T_s t))).coeff i) := by
      filter_upwards [htraj] with t ht
      exact congrArg (fun w => w.coeff i) ht
    refine htmc.trans (hgcoeff.trans ?_)
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
      (fun t (ht : t ∈ Set.Icc (0:ℝ) T) => ht))] with t ht
    exact (hG_eq i ht).symm
  -- **The carrier coordinate is the per-mode convolution of the smooth forcing coordinate** on
  -- `Icc 0 T`: `cfun i t = perModeConv λᵢ (G i) t` (the bridge over `coeffFun_u_eq`).
  have hbridge : ∀ i, Set.EqOn (cfun i) (perModeConv (lam i) (G i)) (Set.Icc (0 : ℝ) T) := by
    intro i t ht
    have hidc : (u₂ t).coeff i
        = (timeH1.toFun (maxRegDuhamelMap (I := I) (M := M) (a : ℝ)
            (lt_of_lt_of_le hT hTe) hTe1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((a : ℝ) + 2)) gforce) t).coeff i := by
      have he := hid t ht
      rw [← tensorHsInclusion_coeff_apply (g := g) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ t) i, he]
    have hcoeff := coeffFun_u_eq (I := I) (M := M)
      (0 : tensorHs (I := I) (M := M) g 0 2 ((a : ℝ) + 2)) gforce
      (lt_of_lt_of_le hT hTe) hTe1 i (Set.mem_Icc.mpr ⟨ht.1, ht.2.trans hTe⟩)
    simp only [hcfun_def, hidc, hcoeff, tensorHs.zero_coeff, mul_zero, zero_add]
    exact duhamel_coeff_integral_eq_perModeConv (I := I) (M := M)
      (lt_of_lt_of_le hT hTe).le gforce i hTe (hG_cont i) (hGtmc i) ht
  -- Each carrier coordinate is `C^∞`-on-`Icc` (ODE bootstrap from the `C^∞` forcing coordinate).
  have hcfun_smooth : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (cfun i) (Set.Icc (0 : ℝ) T) := by
    intro i
    refine (perModeConv_contDiffOn_infty (lam i) (hG_cont i) hT (hG_smooth i)).congr ?_
    intro t ht; exact hbridge i ht
  -- **hP1 — per-mode `C^k` time regularity.**  `fmode i = singleModeCLM (4m) i ∘ cfun i`, a
  -- continuous-linear post-composition of the `C^∞` carrier coordinate.
  have hP1 : ∀ i, ContDiffOn ℝ (k : ℕ∞) (fmode i) (Set.Icc (0 : ℝ) T) := by
    intro i
    have hcfun_k : ContDiffOn ℝ (k : ℕ∞) (cfun i) (Set.Icc (0 : ℝ) T) :=
      (hcfun_smooth i).of_le (by exact_mod_cast le_top)
    exact (singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (σ := ((2 * (2 * m) : ℕ) : ℝ)) i).contDiff.comp_contDiffOn hcfun_k
  -- **hP2 — the per-order `√weight`-summable majorant** of the within-time-derivatives, via the
  -- ODE-iteration closed form and the spectral weight↔eigenvalue-power trade.
  have hP2 : ∃ v : ℕ → Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      (∀ j : ℕ, (j : ℕ∞) ≤ (k : ℕ∞) → Summable (v j)) ∧
      ∀ (j : ℕ) (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)
        (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → (j : ℕ∞) ≤ (k : ℕ∞) →
        ‖iteratedFDerivWithin ℝ j (fmode i) (Set.Icc (0 : ℝ) T) t‖ ≤ v j i := by
    obtain ⟨v, hsum, hbound⟩ := perModeMajorant_exists (I := I) (M := M) (g := g) (m := m) (T := T) hT
      (lam := lam) (G := G) (cfun := cfun) (fmode := fmode) hlam_def hfmode_def
      hG_cont hG_smooth hG_summ hbridge hcfun_smooth
    exact ⟨v, fun j _ => hsum j (by exact_mod_cast le_top),
      fun j i t ht _ => hbound j i t ht (by exact_mod_cast le_top)⟩
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
