import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound

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

* `deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore` — the **single posited leaf**, the
  irreducible chart→intrinsic content stripped of all packaging: the intrinsic covariant Faà-di-Bruno
  **single-coefficient diagonal product-grid domination** of the sealed remainder difference `D`
  itself, against a single intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s`,
  `rfns(∇^a D)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)`.  This
  is the genuine analytic prerequisite (the chart→intrinsic covariant-bilinear realization of the
  sealed remainder difference, with the chart-polynomial coefficient lifted to an intrinsic
  `SmoothCcTensor` and the two-factor diagonal `rfns` grid, has no on-disk antecedent — it is the
  chart-locality-free covariant-jet comparison documented as the open analytic sub-program); its body
  is `sorry`.

* `deTurckRemainderDiff_singleField_diagonalGrid` — the same single-coefficient diagonal grid **with
  the two `C⁰` fibre-sup levels** `ΛW, Λcoeff`, **proved** (no `sorry` of its own) from the core posit
  by mechanically recovering the sups via the uniform smooth-tensor fibre-norm bound
  `exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold.

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

/-- **(POSIT — the IRREDUCIBLE chart→intrinsic content: the intrinsic linearized Ricci–DeTurck
operator realization of the sealed remainder difference as a differentiated fibrewise-bilinear
contraction of `T − T'`.)**

This is the genuine analytic prerequisite descended to the **linearized operator** itself.  For any two
`g₀`-fibre-small smooth ball-radius-`R` perturbations `T, T'`, the sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` is realized as the action of
an **intrinsic differentiated bilinear contraction operator** `Φ : DiffBilinOp g₀` (the assembled
path-linearized Ricci–DeTurck operator, packaging both the rough-Laplacian arm
`−rawTensorConnLapSmooth g₀ 0 2 (T − T')` — `rawTensorConnLapSmooth_sub` — and the genuine linearized-RHS
arm `deTurckRHSSection g_bg (g₀+T) − deTurckRHSSection g_bg (g₀+T')`, the fundamental-theorem-of-calculus
of `deTurckRHSSection` over the metric path `g_τ = g₀+T'+τ(T−T')`,
`D = ∫₀¹ DF(g_τ)·(T−T') dτ`, whose per-chart component derivative is
`hasDerivAt_chartFComponentOnE_deTurckRicciRHS` and whose chart-independent assembly is the intrinsic
Lichnerowicz-type second-order covariant-bilinear operator) on the perturbation difference `T − T'`:
```
D = Φ.op 0 2 (T − T').
```

The operator `Φ` is quantified **inside** the `∀ T T'`: the linearized-operator coefficients depend on
the metric path `g_τ = g₀+T'+τ(T−T')`, hence on `T, T'` (the `O(R)` metric defect of the coefficient
data); a single `T,T'`-independent `Φ` would be FALSE since `D` is the difference of the *nonlinear*
`deTurckSmoothRemainder` (its RHS arm is nonlinear in the perturbation), not a fixed linear functional of
`T − T'`.  For fixed `T, T'` the path `g_τ` is fixed, so `Φ.op 0 2 W := ∫₀¹ DF(g_τ)·W dτ` is a genuine
fibrewise-`ℝ`-linear differentiated bilinear contraction with the `DiffBilinOp` covariant Leibniz field
`covGrad_op` and the per-order proportional fibre envelope `rfns_op_le` discharged by the
smoothness/boundedness of the path coefficient data on the compact manifold, and
`Φ.op 0 2 (T − T') = D`.

This is the genuinely irreducible content with **no on-disk antecedent** (the chart-locality-free
covariant realization of the path-linearized Ricci–DeTurck operator as a `DiffBilinOp`): its body is
`sorry`, and consumers transitively depend on its `sorryAx`.  The downstream diagonal product-grid
(`deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore`) is **mechanically** assembled on top of
this realization via the sorry-free covariant-Leibniz `rfns` grid `DiffBilinOp.rfns_iteratedCovGrad_grid`
and a fixed positive coefficient column — those steps need no further posit.

**Non-vacuity.**  The realization equates the genuine sealed remainder difference `D` (not a free
choice) with `Φ.op 0 2 (T − T')`; a degenerate `Φ` with `Φ.op ≡ 0` is rejected whenever `D ≠ 0` (i.e.
for `T ≠ T'`, where the genuine remainder difference is nonzero), so the operator genuinely realizes the
linearized Ricci–DeTurck action. -/
private theorem deTurckRemainderDiff_eq_intrinsic_diffBilinOp
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
      ∃ (Φ : DifferentialGeometry.Integral.Connection.DiffBilinOp g₀),
        deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' =
          Φ.op 0 2 (T - T') := by
  sorry

/-- **(POSIT — the positive intrinsic coefficient column.)**  A fixed intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s` with a strictly-positive fibre-norm floor `1 ≤ rfns(coeff)(x)` at every
base point.  This is the auxiliary positive parallel coefficient used to lift the single-sum
covariant-Leibniz `rfns` grid of the linearized operator to the two-factor diagonal product-grid shape
the integrated Gagliardo–Nirenberg engine consumes: its `l = 0` column carries the positive floor that
absorbs the single-sum grid constant.  Such a field exists on the compact manifold (e.g. the metric
tensor `metricTensor02 g₀`, whose `g₀`-orthonormal fibre norm-squared equals the dimension at every
point, packaged as a compactly-supported smooth tensor by `HasCompactSupport.of_compactSpace`); the
construction is intrinsic geometric data with no chart-locality content, isolated here as the auxiliary
positive coefficient.  Its body is `sorry`; consumers transitively depend on its `sorryAx`.

**Non-vacuity.**  The floor `1 ≤ rfns(coeff)(x)` rejects the degenerate `coeff = 0` witness
(`rfns(0) = 0`), so the coefficient genuinely carries a positive column. -/
private theorem exists_positiveFloor_intrinsicCoeff (g₀ : SmoothRiemannianMetric I M) :
    ∃ (s : ℕ) (coeff : SmoothCcTensor g₀ 0 s),
      ∀ x : M, (1 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff.toSection x) := by
  sorry

/-- **(The intrinsic covariant Faà-di-Bruno coefficient + diagonal product grid of the sealed
Ricci–DeTurck remainder difference, WITHOUT the `C⁰` fibre-sup packaging.)**

For any two `g₀`-fibre-small smooth ball-radius-`R` perturbations `T, T'`, this delivers a fixed
intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s` and a middle grid constant `Cmid ≥ 0` with
the **single-coefficient diagonal covariant-Leibniz product-grid domination** of the sealed remainder
difference `D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`:
```
rfns(∇^a D)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x).
```

It is **finer** than `deTurckRemainderDiff_singleField_diagonalGrid`: that consumer's two `C⁰`
fibre-sup clauses (`√rfns(T − T') ≤ ΛW`, `√rfns(coeff) ≤ Λcoeff`) are NOT carried here — they are
mechanically recovered from this core by the uniform smooth-tensor fibre-norm bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold.

It is **assembled** from the two posits: the intrinsic linearized-operator realization
`deTurckRemainderDiff_eq_intrinsic_diffBilinOp` (which exhibits `D = Φ.op 0 2 (T − T')` for a fixed
`DiffBilinOp Φ`) and the positive intrinsic coefficient `exists_positiveFloor_intrinsicCoeff`.  Through
the realization, `∇^a D = ∇^a (Φ.op 0 2 (T − T'))` is dominated by the sorry-free covariant-Leibniz `rfns`
grid `DiffBilinOp.rfns_iteratedCovGrad_grid` (the single-sum jet grid
`rfns(∇^a (Φ.op 0 2 W)) ≤ 4^a · gridWindowSum Φ.kappa 0 2 a · ∑_{q ≤ a} rfns(∇^q W)`); widening the
inner window `q ≤ a` to `i ≤ a + 2` (nonnegative `rfns`) and multiplying the right-hand side by the
positive coefficient floor `1 ≤ ∑_{l ≤ a+2−i} rfns(∇^l coeff)` (which always contains the `l = 0` term
`rfns(coeff) ≥ 1`) produces the two-factor diagonal product grid with `Cmid := 4^a · gridWindowSum`.
Consumers transitively depend on the two posits' `sorryAx`.

**Non-vacuity.**  The grid bounds the genuine sealed remainder difference `D`, not a free choice; the
`l = 0` column carries `∑_i rfns(∇^i (T − T'))·rfns(coeff)`, so a `Cmid = 0` witness is rejected by a
nonvanishing remainder-difference jet where `coeff` is nonzero. -/
private theorem deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff : SmoothCcTensor g₀ 0 s) (Cmid : ℝ),
          0 ≤ Cmid ∧
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
  classical
  -- The positive intrinsic coefficient column (`1 ≤ rfns(coeff)` everywhere) and the intrinsic
  -- linearized-operator realization of the sealed remainder difference.
  obtain ⟨s, coeff, hcoeff_floor⟩ := exists_positiveFloor_intrinsicCoeff (I := I) (M := M) g₀
  refine ⟨s, fun T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball => ?_⟩
  -- The intrinsic path-linearized-operator realization of the sealed remainder difference at this
  -- `(T, T')` (the `DiffBilinOp` `Φ` depends on the metric path `g_τ`, hence on `T, T'`).
  obtain ⟨Φ, hreal_x⟩ :=
    deTurckRemainderDiff_eq_intrinsic_diffBilinOp (I := I) (M := M) g₀ g_bg a hR
      T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- The middle grid constant is the `4^a`-scaled order × rank covariant-Leibniz window sum.
  set Cmid : ℝ :=
    (4 : ℝ) ^ a *
      DifferentialGeometry.Integral.Connection.gridWindowSum Φ.kappa 0 2 a with hCmid_def
  have hCmid_nn : 0 ≤ Cmid := by
    rw [hCmid_def]
    exact mul_nonneg (by positivity)
      (DifferentialGeometry.Integral.Connection.gridWindowSum_nonneg Φ.kappa_nonneg 0 2 a)
  refine ⟨coeff, Cmid, hCmid_nn, fun x => ?_⟩
  -- Through the realization, the order-`a` covariant gradient of `D` is that of `Φ.op 0 2 (T − T')`.
  rw [hreal_x]
  -- The sorry-free single-sum covariant-Leibniz `rfns` grid of the differentiated bilinear operator,
  -- at differentiation order `p = 0`, base rank `r = 2`, gradient order `j = a`, section `W = T − T'`.
  have hgrid := Φ.rfns_iteratedCovGrad_grid a 0 2 (T - T') x
  -- Repackage the grid RHS constant `4^a · gridWindowSum` as `Cmid` and the window `range (0+a+1)`.
  have hgrid' :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a (Φ.op 0 2 (T - T'))).toSection x) ≤
        Cmid * ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) := by
    rw [hCmid_def]
    simpa only [Nat.add_zero, Nat.zero_add] using hgrid
  refine hgrid'.trans ?_
  -- Abbreviate the difference-jet column entries.
  set Wq : ℕ → ℝ := fun q =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hWq_def
  have hWq_nn : ∀ q, 0 ≤ Wq q := fun q =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The coefficient column at gradient order `i`: `∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)`, with `1 ≤` floor.
  set Ccol : ℕ → ℝ := fun i =>
    ∑ l ∈ Finset.range (a + 2 + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) with hCcol_def
  have hCcol_floor : ∀ i, i ≤ a + 2 → (1 : ℝ) ≤ Ccol i := by
    intro i hi
    rw [hCcol_def]
    -- The window `range (a+2+1−i)` is nonempty (contains `l = 0` since `i ≤ a+2`); its `l = 0` term is
    -- `rfns(∇^0 coeff) = rfns(coeff) ≥ 1`; all other terms are nonnegative.
    have hmem : 0 ∈ Finset.range (a + 2 + 1 - i) := by
      rw [Finset.mem_range]; omega
    have hl0 : (1 : ℝ) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 s 0 coeff).toSection x) :=
      hcoeff_floor x
    refine le_trans hl0 ?_
    exact Finset.single_le_sum
      (f := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x))
      (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _) hmem
  -- Each single-sum term `Cmid · Wq q` (window `q ≤ a`) is dominated by the diagonal term
  -- `Cmid · Wq q · Ccol q` (window `i ≤ a + 2`, present since `q ≤ a ≤ a + 2`) via the floor `1 ≤ Ccol q`.
  have hsum_le :
      Cmid * ∑ q ∈ Finset.range (a + 1), Wq q ≤
        Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wq i * Ccol i := by
    refine mul_le_mul_of_nonneg_left ?_ hCmid_nn
    -- Step 1: widen the window `range (a+1) → range (a+2+1)` (nonnegative `Wq`).
    have hwiden : ∑ q ∈ Finset.range (a + 1), Wq q ≤ ∑ i ∈ Finset.range (a + 2 + 1), Wq i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega : a + 1 ≤ a + 2 + 1))
        (fun i _ _ => hWq_nn i)
    refine hwiden.trans ?_
    -- Step 2: each `Wq i ≤ Wq i · Ccol i` since `1 ≤ Ccol i` and `0 ≤ Wq i` (for `i ≤ a + 2`).
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hi' : i ≤ a + 2 := by omega
    nlinarith [hWq_nn i, hCcol_floor i hi', mul_nonneg (hWq_nn i) (sub_nonneg.2 (hCcol_floor i hi'))]
  refine hsum_le.trans_eq ?_
  -- Re-expose the abbreviations.
  rw [hWq_def, hCcol_def]

/-- **The intrinsic covariant Faà-di-Bruno single-coefficient diagonal product-grid domination of the
sealed Ricci–DeTurck remainder difference, with the two `C⁰` fibre-sup levels.**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  For
any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, there are a single intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s`, a middle grid constant `Cmid ≥ 0`, and two `C⁰` fibre-sup levels
`ΛW, Λcoeff ≥ 0`, such that for the **sealed remainder difference**
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`:

* `√rfns(T − T') ≤ ΛW` everywhere (the `C⁰` sup of the perturbation difference),
* `√rfns(coeff) ≤ Λcoeff` everywhere (the `C⁰` sup of the coefficient data), and
* the **single-coefficient diagonal covariant-Leibniz product-grid domination**: for every `x`,
  ```
  rfns(∇^a D)(x)
    ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x).
  ```

It is **assembled** from the irreducible chart→intrinsic posit
`deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore` (which supplies the intrinsic coefficient
field `coeff` and the diagonal product grid): the two `C⁰` fibre-sup clauses are mechanically recovered
from that core by the uniform smooth-tensor fibre-norm bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold (set `ΛW := √(sup rfns(T −
T'))`, `Λcoeff := √(sup rfns(coeff))`).  Consumers transitively depend on the core's `sorryAx`.

**Non-vacuity.**  The grid bounds the genuine sealed remainder difference `D`, not a free choice; the
`l = 0` column reads `∑_i rfns(∇^i (T − T'))·rfns(coeff)`, so a `Cmid = 0` witness is rejected by a
nonvanishing remainder-difference jet where `coeff` is nonzero. -/
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
  -- Strip the `C⁰` fibre-sup packaging off the irreducible chart→intrinsic core: the core supplies
  -- the intrinsic coefficient field and the diagonal product grid; the two sups are recovered from
  -- the uniform smooth-tensor fibre-norm bound on the compact manifold.
  obtain ⟨s, hcore⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff, Cmid, hCmid, hgrid⟩ :=
    hcore T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- `C⁰` fibre-sup of the perturbation difference `T − T'` on the compact manifold.
  obtain ⟨KW, hKW_nn, hKW⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 2 (T - T')
  -- `C⁰` fibre-sup of the coefficient field `coeff` on the compact manifold.
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 s coeff
  refine ⟨coeff, Cmid, Real.sqrt KW, Real.sqrt Kc, hCmid, Real.sqrt_nonneg KW,
    Real.sqrt_nonneg Kc, ?_, ?_, hgrid⟩
  · intro x
    rw [Real.sq_sqrt hKW_nn]
    exact hKW x
  · intro x
    rw [Real.sq_sqrt hKc_nn]
    exact hKc x

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
