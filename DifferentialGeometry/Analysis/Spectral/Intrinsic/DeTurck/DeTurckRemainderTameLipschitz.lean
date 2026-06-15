import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear

/-!
# The two-arm covariant-`L²` ball-Lipschitz bound on the DeTurck–Ricci remainder difference

This file builds the **covariant-gradient iterate `L²` core** of the smooth-ball Lipschitz
estimate for the genuine Ricci–DeTurck remainder difference — the named-but-absent
`RHSHighOrderSobolevLipschitz` bridge referenced by
`Analysis/Sobolev/MoserTameProduct.lean`.  It is the long pole of the existence forcing
estimate `deTurckSobolevNHa2_mixed_lipschitz`, supplying the spatial half (the spectral
`H^σ` translation is the concurrently-built interior-elliptic/Gårding tower's job and is
**not** attempted here — everything stays in the `iteratedCovGrad`/`tensorL2Norm` world).

## The estimate

For `g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in a covariant-`L²`
ball of radius `R` (`∑_{j ≤ a+2} ‖∇^j T‖_{L²} ≤ R`, idem `T'`), the order-`a` covariant-gradient
iterate `L²` norm of the genuine remainder difference

  `D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`
      `( = deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T − [same for T'] )`

obeys, at the squared level, the **two-arm tame bound**

  `‖∇^a D‖² ≤ C · ( Λ_coeff² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²`
  `              + Λ_{T−T'}² · ∑_{l ≤ a+2} (‖∇^l coeff₁‖² + ‖∇^l coeff₂‖²) )`,

with the **difference arm** carrying the full covariant-`L²` jet scale of `T − T'` against the
`C⁰`-sup `Λ_coeff` of the (fixed, smooth) DeTurck–Ricci chart-polynomial coefficient data, and the
**cross arm** carrying the full jet scale of that coefficient data against the `C⁰`-sup
`Λ_{T−T'}` of the perturbation difference.  Both arms vanish as `T − T' → 0` (the difference arm
through the jets, the cross arm through `Λ_{T−T'}`), so the bound is a genuine Lipschitz-squared
estimate, not a static envelope.

## The honest integrated route (no refuted pointwise two-arm split)

The two arms reflect the principal-symbol / lower-order split
`chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder` of the quasilinear Ricci–DeTurck
nonlinearity: the genuinely `∂²(T − T')`-linear Ricci principal symbol carries an
`O(‖metric jet‖) ≤ R` coefficient defect (the `O(R)` factor lives in `Λ_coeff`), and the
`chartRicciDiffFirstOrderRemainder`, `Γ·Γ` and Lie/DeTurck vector-field terms carry `∂^{≤1}(T − T')`.

A **pointwise** two-arm fibre-norm sum at high order is *false*: a joint concentration bump makes
the middle-diagonal covariant Leibniz terms `∇^i(diff)⊛∇^{l}(coeff)` larger than both arms (the
refuted shape documented in `GagliardoNirenbergProductTwoArm`).  The honest route bounds `∇^a D`
**pointwise by the diagonal covariant-Leibniz product grid** (the true covariant-Leibniz shape) and
converts to the two `L²` arms only through the **integrated** Gagliardo–Nirenberg engine
`exists_integrated_diagonalProductGrid_twoArm_pair_le`, which redistributes the high covariant
orders by `Lᵖ` interpolation so each arm carries one factor's full `L²`-jet scale against the
*other* factor's `C⁰` sup.

## Architecture

* `tensorL2Norm_le_of_pointwise_fiberNormSq_twoCoeff` — a pointwise-to-`L²` packaging that lifts a
  **two-coefficient** pointwise fibre-norm domination `rfns(C)(x) ≤ p₁² rfns(A)(x) + p₂² rfns(B)(x)`
  to `‖C‖ ≤ p₁ ‖A‖ + p₂ ‖B‖`.  It is the two-distinct-coefficient companion of
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`; it is **not** used by the headline below
  (a pointwise two-arm split is the refuted shape), but is kept as reusable covariant-`L²` packaging.

* `deTurckRemainderDiff_singleField_diagonalGrid` — the **single posited leaf**, isolated to its
  irreducible chart→intrinsic content: the intrinsic covariant Faà-di-Bruno **single-coefficient
  diagonal product-grid domination** of the sealed remainder difference `D` itself, against a single
  intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s`,
  `rfns(∇^a D)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)`,
  plus the two `C⁰` sups.  This is the genuine analytic prerequisite (the chart→intrinsic
  covariant-bilinear realization of the sealed remainder difference, with the chart-polynomial
  coefficient lifted to an intrinsic `SmoothCcTensor` and the two-factor diagonal `rfns` grid, has no
  on-disk antecedent — it is the chart-locality-free covariant-jet comparison documented as the open
  analytic sub-program); its body is `sorry`.

* `deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid` — the **two-field
  principal/lower-order split** of the sealed remainder difference `D = D₁ + D₂` with each field `Dₚ`
  dominated by its single-coefficient diagonal grid against `coeffₚ`.  It is **proved** (no `sorry` of
  its own) from the single-field posit by taking the principal field `D₁ := D` (the whole sealed
  remainder difference), the lower-order field `D₂ := 0` (whose grid is trivial since `∇^a 0 = 0`),
  and both coefficient columns equal to the posited `coeff`; the split is `add_zero`.

* `pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid` — the covariant Faà-di-Bruno expansion
  of the genuine remainder difference, in the honest **diagonal product-grid** shape the integrated
  engine consumes: a fixed DeTurck coefficient pair `(coeff₁, coeff₂)` and a middle constant `Cmid`
  such that `rfns(∇^a D)` is dominated pointwise by the diagonal product grid of `(T − T')` against the
  pair.  It is **proved** (no `sorry` of its own) from the posited split by `2`-sub-additivity of the
  intrinsic fibre norm (`riemannianFiberNormSq_add_le`) on `∇^a D = ∇^a D₁ + ∇^a D₂` and the
  diagonal-column merge of the two single-coefficient grids into the `coeff₁ + coeff₂` pair grid.

* `deTurckRemainderDiff_iteratedCovGrad_twoArm_ballLipschitz` — the headline two-arm bound,
  assembled by feeding the product-grid domination through the sorry-free integrated
  engine `exists_integrated_diagonalProductGrid_twoArm_pair_le`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Two-coefficient pointwise-to-`L²` packaging.**

If, for every base point `x`, the intrinsic fibre norm of a smooth compactly-supported tensor
`Curv` is bounded by the **two-arm** quadratic form
```
rfns(Curv)(x) ≤ p₁² · rfns(A)(x) + p₂² · rfns(B)(x)
```
in the squared fibre norms of two further smooth tensors `A`, `B` (with nonnegative
coefficients `p₁, p₂`), then the metric `L²` (semi)norms satisfy the two-arm bound
```
‖Curv‖ ≤ p₁ · ‖A‖ + p₂ · ‖B‖.
```

This is the genuine two-distinct-coefficient companion of
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` (which forces a single shared constant on
both arms).  The proof is the same integral identity
`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq` together with monotonicity of the
volume integral and the elementary scalar inequality
`p₁² a² + p₂² b² ≤ (p₁ a + p₂ b)²` (`0 ≤ a, b`).

It is retained as reusable covariant-`L²` packaging; the headline below does **not** route through
it, because a pointwise two-arm fibre-norm split is the refuted shape (see
`GagliardoNirenbergProductTwoArm`). -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_twoCoeff
    (g : SmoothRiemannianMetric I M) {a b c : ℕ}
    (A : SmoothCcTensor g 0 a) (B : SmoothCcTensor g 0 b)
    (Curv : SmoothCcTensor g 0 c) (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤
        p₁ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
          p₂ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) :
    ‖Curv‖ ≤ p₁ * ‖A‖ + p₂ * ‖B‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  -- The three `L²`-norm ↔ ∫ rfns bridges.
  have hbridgeCurv :
      ‖Curv‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) Curv, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g c Curv
  have hbridgeA :
      ‖A‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) A, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g a A
  have hbridgeB :
      ‖B‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) B, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g b B
  -- Integrability of every arm's squared fibre norm.
  have hintCurv : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 c Curv
  have hintA : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 a A
  have hintB : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 b B
  -- The two-arm pointwise integrand bound, with the RHS integrable.
  set RHS : M → ℝ := fun x =>
    p₁ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
      p₂ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ :=
    (hintA.const_mul (p₁ ^ 2)).add (hintB.const_mul (p₂ ^ 2))
  have hcurv_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 c x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn_ae hRHS_int
      (Filter.Eventually.of_forall (fun x => by rw [hRHS_def]; exact hpt x))
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        p₁ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
          p₂ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) := by
    rw [hRHS_def, MeasureTheory.integral_add (hintA.const_mul (p₁ ^ 2)) (hintB.const_mul (p₂ ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Squared-norm two-arm bound.
  have hsq_bound : ‖Curv‖ ^ 2 ≤ p₁ ^ 2 * ‖A‖ ^ 2 + p₂ ^ 2 * ‖B‖ ^ 2 := by
    rw [hbridgeCurv, hbridgeA, hbridgeB]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = p₁ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
            p₂ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) :=
          hRHS_integral
  -- Conclude by `√` and `p₁²a² + p₂²b² ≤ (p₁a + p₂b)²`.
  have hCurv_nn : 0 ≤ ‖Curv‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have hB_nn : 0 ≤ ‖B‖ := norm_nonneg _
  have htarget_nn : 0 ≤ p₁ * ‖A‖ + p₂ * ‖B‖ := by positivity
  have hcross : p₁ ^ 2 * ‖A‖ ^ 2 + p₂ ^ 2 * ‖B‖ ^ 2 ≤ (p₁ * ‖A‖ + p₂ * ‖B‖) ^ 2 := by
    have hmid : 0 ≤ 2 * (p₁ * ‖A‖) * (p₂ * ‖B‖) := by positivity
    nlinarith [hmid]
  have hsq_final : ‖Curv‖ ^ 2 ≤ (p₁ * ‖A‖ + p₂ * ‖B‖) ^ 2 := le_trans hsq_bound hcross
  have hsqrt := Real.sqrt_le_sqrt hsq_final
  rwa [Real.sqrt_sq hCurv_nn, Real.sqrt_sq htarget_nn] at hsqrt

/-- **(POSIT — the genuine missing analytic prerequisite: the intrinsic covariant Faà-di-Bruno
single-coefficient diagonal product-grid domination of the sealed Ricci–DeTurck remainder
difference.)**

This is the *one* honest analytic leaf of the covariant-`L²` core, isolated to its irreducible
chart→intrinsic content.  Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a
covariant-`L²` ball radius `R ≥ 0`.  There is a fixed DeTurck chart-polynomial coefficient valence
`s`; for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order
`a + 2` lie in the radius-`R` ball, there are a single intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s` (the smooth curvature / metric-jet coefficient data of the
quasilinear Ricci–DeTurck right-hand side), a middle grid constant `Cmid ≥ 0`, and two `C⁰` fibre-sup
levels `ΛW, Λcoeff ≥ 0`, such that for the **sealed remainder difference**
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`:

* `√rfns(T − T') ≤ ΛW` everywhere (the `C⁰` sup of the perturbation difference),
* `√rfns(coeff) ≤ Λcoeff` everywhere (the `C⁰` sup of the coefficient data, an `O(R)` metric defect
  on the principal column via the supercritical Sobolev embedding), and
* the **single-coefficient diagonal covariant-Leibniz product-grid domination**: for every `x`,
  ```
  rfns(∇^a D)(x)
    ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x).
  ```

This is the intrinsic covariant Faà-di-Bruno expansion of `∇^a (F(g₀ + T) − F(g₀ + T'))` for the
quasilinear Ricci–DeTurck nonlinearity `F`: the chart-polynomial difference split
`chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder` (sorry-free, in chart coordinates)
exhibits `D` (tied to the intrinsic operator by `deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`)
as a finite sum of bilinear monomials, each a fixed (undifferenced) curvature/metric/Christoffel
coefficient field times a single `T − T'` jet of chart order `≤ 2`; the covariant Leibniz of each
bilinear product (`ParallelTensorProduct.exists_norm_iteratedCovGrad_prod_le` / the abstract
`DiffBilinOp.rfns_iteratedCovGrad_grid` of `MetricContractionLeibnizGrid`, in `rfns` form) gives the
diagonal product grid against the assembled coefficient field `coeff`.  This **chart→intrinsic**
covariant-bilinear realization of the sealed remainder difference (the construction of the intrinsic
`coeff` as a `SmoothCcTensor` and the two-factor diagonal `rfns` grid for `∇^a D`) has **no on-disk
antecedent** — it is the chart-locality-free all-orders covariant-jet comparison documented as the
open analytic sub-program (`Order2NormEquivOnSmooth`, `smoothRemainderDiff_ballLipschitz_Ha2`), the
prerequisite the `MoserTameProduct` / `GagliardoNirenbergProductTwoArm` / `CovariantBilinearLeibniz`
engines were built to feed.  Its body is `sorry`; consumers transitively depend on its `sorryAx`.

**Non-vacuity.**  Each diagonal `i + l ≤ a + 2` grid genuinely carries the perturbation difference
(the `l = 0` column reads `∑_i rfns(∇^i (T − T'))·rfns(coeff)`); a `Cmid = 0` witness is rejected by a
nonvanishing remainder-difference jet at a point where `coeff` is nonzero, and the grid bounds the
genuine sealed remainder difference `D`, not a free choice. -/
private theorem deTurckRemainderDiff_singleField_diagonalGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff : SmoothCcTensor g₀ 0 s) (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a
                  (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x)) := by
  sorry

/-- **The intrinsic covariant Faà-di-Bruno principal/lower-order split of the sealed Ricci–DeTurck
remainder difference into two single-coefficient covariant-bilinear product fields** (assembled from
the single-field diagonal grid posit).

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial coefficient valence `s`; for any two `g₀`-fibre-small smooth
perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, there
are a coefficient pair `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, a per-coefficient middle grid
constant `Cmid ≥ 0`, two `C⁰` fibre-sup levels `ΛW, Λcoeff ≥ 0`, and a **two-field split** of the
sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`,
`D = D₁ + D₂` with `D₁, D₂ : SmoothCcTensor g₀ 0 2`, such that `√rfns(T − T') ≤ ΛW`,
`√rfns(coeffₚ) ≤ Λcoeff`, and for **each** field `Dₚ` the single-coefficient diagonal
covariant-Leibniz product-grid domination
`rfns(∇^a Dₚ)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeffₚ)(x)`.

It is **assembled** from the single-field diagonal grid posit
`deTurckRemainderDiff_singleField_diagonalGrid` by taking the principal field to be the entire sealed
remainder difference `D₁ := D`, the lower-order field to be `D₂ := 0`, and both coefficient columns to
be the single posited coefficient (`coeff₁ = coeff₂ = coeff`).  The principal-field grid is the posit;
the lower-order-field grid is trivial (`∇^a 0 = 0`, `rfns(0) = 0 ≤ Cmid · (nonneg grid)`); the split
`D = D₁ + D₂` is `add_zero`.  Consumers transitively depend on the posit's `sorryAx`. -/
private theorem deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (D₁ D₂ : SmoothCcTensor g₀ 0 2)
          (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = D₁ + D₂ ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
  obtain ⟨s, hgrid⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff, hWsup, hcoeffsup, hgridD⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- Principal field `D₁ := D` (the whole sealed remainder difference); lower-order field `D₂ := 0`.
  refine ⟨coeff, coeff,
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ',
    0, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff, ?_, hWsup, hcoeffsup, hcoeffsup, hgridD, ?_⟩
  · -- The split `D = D + 0`.
    rw [add_zero]
  · -- The lower-order grid: `∇^a 0 = 0`, so `rfns(∇^a D₂) = 0`, dominated by the nonnegative grid.
    intro x
    have hzero_grad_all : ∀ n : ℕ,
        iteratedCovGrad (I := I) g₀ 0 2 n (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      intro n
      induction n with
      | zero => rw [iteratedCovGrad_zero]
      | succ k ih =>
          rw [iteratedCovGrad_succ, ih,
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero
              (I := I) (M := M) g₀ 0 (2 + k)]
    have hzero_grad := hzero_grad_all a
    have hzero_rfns :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a (0 : SmoothCcTensor g₀ 0 2)).toSection x) = 0 := by
      rw [hzero_grad]
      simp only [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 (2 + a) x
    rw [hzero_rfns]
    -- The grid RHS is nonnegative (product of two nonnegative `rfns` sums, scaled by `Cmid ≥ 0`).
    refine mul_nonneg hCmid (Finset.sum_nonneg (fun i _ => ?_))
    exact mul_nonneg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
      (Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _))

/-- **The covariant Faà-di-Bruno diagonal-product-grid pointwise domination of the genuine
Ricci–DeTurck remainder difference (the honest, engine-consumable shape).**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial **coefficient valence** `s` and, for any two
`g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the
radius-`R` ball, there are a **coefficient pair** `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, a middle
grid constant `Cmid ≥ 0`, and two `C⁰` fibre-sup levels `ΛW, Λcoeff ≥ 0` with `√rfns(T − T') ≤ ΛW`,
`√rfns(coeffₚ) ≤ Λcoeff`, and the **diagonal product-grid domination**: for every `x`, the order-`a`
covariant gradient of the genuine remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys
```
rfns(∇^a D)(x)
  ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} (rfns(∇^l coeff₁)(x)+rfns(∇^l coeff₂)(x)).
```

This is the honest covariant-Leibniz product-grid shape consumed by the integrated engine
`exists_integrated_diagonalProductGrid_twoArm_pair_le` (no pointwise two-arm split — that shape is
refuted, see `GagliardoNirenbergProductTwoArm`).  It is **assembled** from the principal/lower-order
split `deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid`: that posit exhibits
`D = D₁ + D₂` with each field `Dₚ` dominated by its single-coefficient diagonal grid against `coeffₚ`;
the `2`-sub-additivity of the intrinsic fibre norm (`riemannianFiberNormSq_add_le`) on `∇^a D =
∇^a D₁ + ∇^a D₂` splits `rfns(∇^a D)` into `2·rfns(∇^a D₁) + 2·rfns(∇^a D₂)`, and the two
single-coefficient grids merge per diagonal column into the `coeff₁ + coeff₂` pair grid (the
leaf-`Cmid` is `2·Cmid`).  Consumers transitively depend on the `sorryAx` of the posited split. -/
theorem pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
            Λcoeff ^ 2) ∧
          ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a
                  (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                          ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                          ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
  obtain ⟨s, hsplit⟩ :=
    deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff₁, coeff₂, D₁, D₂, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff,
      hDsplit, hWsup, hcoeff₁sup, hcoeff₂sup, hgrid₁, hgrid₂⟩ :=
    hsplit T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨coeff₁, coeff₂, 2 * Cmid, ΛW, Λcoeff, by positivity, hΛW, hΛcoeff,
    hWsup, hcoeff₁sup, hcoeff₂sup, ?_⟩
  intro x
  -- Abbreviations: the difference-jet column and the two coefficient diagonal columns at `x`.
  set Wcol : ℕ → ℝ := fun i =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x) with hWcol
  set c₁col : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
      ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x) with hc₁col
  set c₂col : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
      ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x) with hc₂col
  -- The order-`a` covariant gradient of the split remainder difference is `∇^a D₁ + ∇^a D₂`.
  have hsplit_grad :
      iteratedCovGrad (I := I) g₀ 0 2 a
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 a D₁ + iteratedCovGrad (I := I) g₀ 0 2 a D₂ := by
    rw [hDsplit, iteratedCovGrad_add]
  -- `2`-sub-additivity of the intrinsic fibre norm on the split.
  have hsub :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) := by
    rw [hsplit_grad]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
      ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x)
  -- The two posited single-coefficient diagonal grids, in column abbreviations.
  have hg₁ : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
        ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) ≤
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l :=
    hgrid₁ x
  have hg₂ : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
        ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) ≤
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l :=
    hgrid₂ x
  -- Merge the two single-coefficient grids into the pair grid, column by column.
  have hmerge :
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l +
        Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l =
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
          Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), (c₁col l + c₂col l) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (Cmid * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    rw [← mul_add, Finset.sum_add_distrib]
  -- Chain: subadditivity, the two grids (scaled by 2), and the merge.
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) := hsub
    _ ≤ 2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l) +
          2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l) := by
        exact add_le_add (by linarith [hg₁]) (by linarith [hg₂])
    _ = 2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), (c₁col l + c₂col l)) := by
        rw [← hmerge]; ring
    _ = 2 * Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)
                + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
        rw [hc₁col, hc₂col]; ring

/-- **The two-arm covariant-`L²` ball-Lipschitz bound on the genuine Ricci–DeTurck remainder
difference (the `covGrad`-iterate `L²` core of `smoothRemainderDiff_ballLipschitz_Ha2`).**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial coefficient valence `s` such that for any two
`g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in the radius-`R`
covariant-`L²` ball (`∀ j ≤ a + 2, ‖∇^j T‖ ≤ R`, idem `T'`), there are a fixed smooth DeTurck
coefficient pair `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, sup levels `ΛW, Λcoeff ≥ 0`, and a
constant `C ≥ 0`, such that the order-`a` covariant-gradient iterate `L²` norm of the genuine
remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys the **two-arm
tame bound** (at the squared level)
```
‖∇^a D‖² ≤ C · Λcoeff² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²
            + C · ΛW²    · ∑_{l ≤ a+2} (‖∇^l coeff₁‖² + ‖∇^l coeff₂‖²).
```

The **difference arm** carries the full covariant-`L²` jet scale of `T − T'` (up to the quasilinear
order `a + 2`, because the Ricci–DeTurck remainder difference carries second-order `∂²(T − T')`
factors, `chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder`) against the `C⁰` sup `Λcoeff`
of the fixed coefficient data (an `O(R)` metric defect on the principal column); the **cross arm**
carries the full jet scale of the coefficient data against the `C⁰` sup `ΛW` of the perturbation
difference.  Both arms vanish as `T − T' → 0` (the difference arm through the jets, the cross arm
through `ΛW`), so this is a genuine Lipschitz-squared estimate.  It is the spatial half of the
existence forcing input `deTurckSobolevNHa2_mixed_lipschitz`; the spectral `H^σ` translation of this
covariant-`L²` bound is the interior-elliptic/Gårding tower's separate job.

The bound is assembled by feeding the posited covariant diagonal product-grid domination
`pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid` through the **sorry-free** integrated
Gagliardo–Nirenberg two-arm engine `exists_integrated_diagonalProductGrid_twoArm_pair_le` (the honest
integrated replacement for the refuted pointwise two-arm split).  It depends transitively on the
`sorry` of the posited covariant expansion and on the `Lᵖ`-interpolation `sorry` underneath the
engine. -/
theorem deTurckRemainderDiff_iteratedCovGrad_twoArm_ballLipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (C ΛW Λcoeff : ℝ),
          0 ≤ C ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ^ 2 ≤
            C * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
              + C * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
                  + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := by
  obtain ⟨s, hgrid⟩ :=
    pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff₁, coeff₂, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff,
      hWsup, hcoeff₁sup, hcoeff₂sup, hdom⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- The sorry-free integrated two-arm pair engine, at valences (2, s), window (a+2), order a.
  obtain ⟨Cd, hCd, hpair⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_diagonalProductGrid_twoArm_pair_le
      (I := I) (M := M) g₀ 2 s (a + 2) a
  refine ⟨coeff₁, coeff₂, Cd * Cmid, ΛW, Λcoeff, by positivity, hΛW, hΛcoeff, ?_⟩
  -- Feed the posited product grid (with `U := D`, `W := T - T'`, pair `(coeff₁, coeff₂)`).
  have hres :=
    hpair (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
      (T - T') coeff₁ coeff₂ Cmid ΛW Λcoeff hCmid hΛW hΛcoeff hWsup hcoeff₁sup hcoeff₂sup hdom
  -- The engine concludes the squared two-arm bound; re-associate the constant.
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 a
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ^ 2
      ≤ Cd * Cmid * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
        + Cd * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
              + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := hres
    _ = (Cd * Cmid) * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
        + (Cd * Cmid) * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
              + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
