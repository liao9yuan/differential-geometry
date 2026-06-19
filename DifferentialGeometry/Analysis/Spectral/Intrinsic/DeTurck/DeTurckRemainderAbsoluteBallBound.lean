import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily

/-!
# The order-`d` ABSOLUTE (single-field) covariant-`L²` ball bound on the Ricci–DeTurck remainder

This file builds the **absolute (single-perturbation) order-`d` covariant-gradient jet-column `L²`
bound** on the genuine Ricci–DeTurck remainder, the single-field analogue of the order-`d`
*difference* tower `deTurckRemainderDiff_iteratedCovGradSum_ballBound_order` of
`DeTurckRemainderTameLipschitz.lean`.  It is the spatial-Sobolev underpinning of the existence-side
spectral coupling consumed by the time-bootstrap of the realized DeTurck–Ricci engine forcing
(`Analysis/Spectral/Intrinsic/HeatSemigroup/ForcingTimeBootstrap.lean`): the Nemytskii image `N(u)`
of a single field `u` at every spatial order `d ≥ a` lifts into `Hᵈ` whenever `u ∈ H^{d+2}`.

## The estimate is AFFINE, not multiplicative

For a `g₀`-fibre-small smooth perturbation `T` whose covariant-`L²` jets up to order `d + 2` lie in a
radius-`R` ball, the entire order-`(≤ d)` covariant-gradient jet column of the genuine remainder
`N(T) := deTurckSmoothRemainder g₀ g_bg T` obeys
```
∑_{q ≤ d} ‖∇^q N(T)‖²  ≤  C · (1 + ∑_{i ≤ d+2} ‖∇^i T‖²).
```
The `1 +` affine factor is **mathematically necessary**: at `T = 0` the right-hand side of the naive
*multiplicative* form `∑_q ‖∇^q N(T)‖² ≤ C · ∑_i ‖∇^i T‖²` would be `C · 0 = 0`, forcing the genuine
background remainder `N(0) = deTurckSmoothRemainder g₀ g_bg 0 = deTurckRHSSection g_bg g₀ =
−2 Ric(g₀) + 𝓛_{W(g₀,g_bg)}(g₀)` to vanish — i.e. forcing `g₀` to be a DeTurck–Ricci steady state,
which is **not** a hypothesis (the consumer flows `g₀ + u` with `g₀` an arbitrary closed metric, so
`N(0) ≠ 0` generically: on the round `S²` with `g_bg = g₀` the DeTurck field `W` vanishes and
`N(0) = −2 Ric(g₀) ≠ 0`).  The multiplicative form is therefore false-as-stated; the affine form is
the honest encoding of `‖N(u)‖_{Hᵈ} ≲ 1 + ‖u‖_{H^{d+1}}` documented at the consumer.

## The route — re-basing the difference tower at `T' = 0`

The genuine remainder is a difference of the affine-zero datum:
`N(T) = (N(T) − N(0)) + N(0)`.  Instantiating the order-`d` *difference* tower
`deTurckRemainderDiff_iteratedCovGradSum_ballBound_order` at `T' = 0` (which is fibre-small with
`δ' = 0 < 1`, `gFibreOpBound g₀ (ccTensorBilinSymm g₀ 0) 0`, and whose every jet vanishes, so it lies
in **every** ball) bounds `∑_{q ≤ d} ‖∇^q (N(T) − N(0))‖²` by `C_diff · ∑_{i ≤ d+2} ‖∇^i T‖²` (using
`T − 0 = T`).  The background term `N(0)` is a **fixed** smooth tensor, so its covariant-`L²` jet
column `K₀ := ∑_{q ≤ d} ‖∇^q N(0)‖²` is a finite constant.  The triangle/AM–GM inequality
`‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` on `∇^q N(T) = ∇^q (N(T) − N(0)) + ∇^q N(0)` and summing the `d + 1` orders
yields `∑_q ‖∇^q N(T)‖² ≤ 2 C_diff · ∑_i ‖∇^i T‖² + 2 K₀ ≤ (2 C_diff + 2 K₀) · (1 + ∑_i ‖∇^i T‖²)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The order-`d` ABSOLUTE (single-field) covariant-`L²` ball bound on the genuine Ricci–DeTurck
remainder, in the honest AFFINE form.**

Fix `g₀`, the DeTurck background `g_bg`, a supercritical base order `a` (`2·finrank E + 10 ≤ a`), an
order `d ≥ a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is one nonnegative ball-uniform
constant `C` (outside `∀ T`) such that for any `g₀`-fibre-small smooth perturbation `T` whose
covariant-`L²` jets up to order `d + 2` lie in the radius-`R` ball, the entire order-`(≤ d)`
covariant-gradient jet column of the genuine remainder `deTurckSmoothRemainder g₀ g_bg T` obeys, at the
squared `L²` level, the affine bound
```
∑_{q ≤ d} ‖∇^q (deTurckSmoothRemainder g₀ g_bg T)‖²  ≤  C · (1 + ∑_{i ≤ d+2} ‖∇^i T‖²).
```

This is the single-field analogue of the order-`d` difference tower
`deTurckRemainderDiff_iteratedCovGradSum_ballBound_order`, re-based at `T' = 0` (whose every covariant
jet vanishes, so it lies in every ball, with `δ' = 0 < 1` and
`gFibreOpBound g₀ (ccTensorBilinSymm g₀ 0) 0`).  The `1 +` affine factor is necessary because the
genuine background remainder `N(0) = deTurckSmoothRemainder g₀ g_bg 0` does **not** vanish in general
(a pure multiplicative form would force `g₀` to be a steady state).  This is the spatial-Sobolev
estimate the existence-side spectral coupling `deTurckForcing_higherOrderRepresentative` should cite to
lift the Nemytskii forcing into `Hᵈ`. -/
theorem deTurckRemainder_iteratedCovGradSum_ballBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∑ q ∈ Finset.range (d + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)‖ ^ 2) ≤
          C * (1 + ∑ i ∈ Finset.range (d + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T‖ ^ 2) := by
  classical
  -- The order-`d` difference tower: its ball-uniform constant `Cdiff` is hoisted outside `∀ T`.
  obtain ⟨Cdiff, hCdiff_nn, hCdiff⟩ :=
    deTurckRemainderDiff_iteratedCovGradSum_ballBound_order (I := I) (M := M) g₀ g_bg a ha_super d
      hda hR
  -- The affine-zero datum `T' = 0` is fibre-small with `δ' = 0 < 1`, and all its jets vanish.
  have hδ0_lt : (0 : ℝ) < 1 := by norm_num
  have hδ0 : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) 0 :=
    gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀
  -- Every covariant jet of the zero tensor is zero.
  have hjet_zero : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) 0
    rw [sub_self] at h
    rw [h, sub_self]
  -- The fixed background remainder `N(0)` and its finite covariant-`L²` jet-column constant `K₀`.
  set N0 : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ0_lt hδ0 with hN0_def
  set K0 : ℝ := ∑ q ∈ Finset.range (d + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 with hK0_def
  have hK0_nn : 0 ≤ K0 := Finset.sum_nonneg fun q _ => sq_nonneg _
  refine ⟨2 * Cdiff + 2 * K0, by positivity, ?_⟩
  intro T δ hδ_lt hδ hTball
  -- The order-`(d+2)` covariant jet column of `T`.
  set Scol : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- The `T' = 0` ball hypothesis: every jet of `0` has norm `0 ≤ R`.
  have hT'ball : ∀ j : ℕ, j ≤ d + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j _
    rw [hjet_zero j, norm_zero]; exact hR
  -- The sealed remainder difference `D := N(T) − N(0)`.
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ - N0 with hD_def
  -- The difference tower at `T' = 0`: `∑_{q ≤ d} ‖∇^q D‖² ≤ Cdiff · ∑_{i ≤ d+2} ‖∇^i (T − 0)‖²`.
  have hdiff := hCdiff T (0 : SmoothCcTensor g₀ 0 2) hδ_lt hδ hδ0_lt hδ0 hTball hT'ball
  -- `T − 0 = T`, so the right-hand column is `Scol`.
  have hdiff' : (∑ q ∈ Finset.range (d + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) ≤ Cdiff * Scol := by
    rw [hD_def, hN0_def, hScol_def]
    simpa only [sub_zero] using hdiff
  -- Per order `q ≤ d`: `∇^q N(T) = ∇^q D + ∇^q N(0)`, so `‖∇^q N(T)‖² ≤ 2‖∇^q D‖² + 2‖∇^q N(0)‖²`.
  have hper : ∀ q ∈ Finset.range (d + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 := by
    intro q _
    have hsplit : iteratedCovGrad (I := I) g₀ 0 2 q
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
          iteratedCovGrad (I := I) g₀ 0 2 q D +
            iteratedCovGrad (I := I) g₀ 0 2 q N0 := by
      rw [hD_def, iteratedCovGrad_sub, sub_add_cancel]
    rw [hsplit]
    have htri := norm_add_le (iteratedCovGrad (I := I) g₀ 0 2 q D)
      (iteratedCovGrad (I := I) g₀ 0 2 q N0)
    have hsumnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q D +
        iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 ≤
          (‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    refine hsq.trans ?_
    nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖)]
  -- Sum the per-order bounds and chain through the difference tower and the affine widening.
  calc (∑ q ∈ Finset.range (d + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)‖ ^ 2)
      ≤ ∑ q ∈ Finset.range (d + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2) := Finset.sum_le_sum hper
    _ = 2 * (∑ q ∈ Finset.range (d + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) +
          2 * K0 := by
        rw [hK0_def, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (Cdiff * Scol) + 2 * K0 := by
        have := hdiff'
        linarith
    _ ≤ (2 * Cdiff + 2 * K0) * (1 + Scol) := by
        have hCS_nn : 0 ≤ Cdiff * Scol := mul_nonneg hCdiff_nn hScol_nn
        nlinarith [hCdiff_nn, hK0_nn, hScol_nn, mul_nonneg hK0_nn hScol_nn]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
