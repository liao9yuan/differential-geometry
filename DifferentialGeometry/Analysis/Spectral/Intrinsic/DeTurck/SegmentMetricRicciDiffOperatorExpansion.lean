import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDifferenceFdBTermTree

/-! # The Hamilton/Moser two-product pointwise-to-`L²` lift

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **reusable analytic lift** turning a *pointwise*
Hamilton/Moser **two-product** squared-fibre-norm (`riemannianFiberNormSq`, `rfns`) domination of a
tensor section into the corresponding **global-`L²` two-arm bound** with *separate* per-arm constants.

This is exactly the pointwise-to-`L²` step the covariant Faà-di-Bruno expansion of the
Ricci–DeTurck right-hand-side difference needs: the deep covariant-curvature-jet content produces a
pointwise bound

```
rfns(Curv)(x) ≤ Λ² · ∑_i rfns(wⱼₑₜ i)(x)  +  (∑_i (rfns(c₁ⱼₑₜ i)(x) + rfns(c₂ⱼₑₜ i)(x))) · D₀²,
```

with `Curv` the `j`-th covariant gradient of the curvature-summand difference, `wⱼₑₜ i = ∇^i` of the
difference factor (the high derivative on the *difference*, controlled in `L²`), `Λ` a ball-uniform
`≤2`-jet coefficient sup, the `cₖⱼₑₜ i = ∇^i` of the *fixed-pair endpoints* (carrying the unbounded
top coefficient jet in `L²` mass), and `D₀` the difference's `C⁰` mass.  The lift concludes the
**Hamilton/Moser tame** bound

```
‖Curv‖_{L²} ≤ Λ · ∑_i ‖wⱼₑₜ i‖_{L²}  +  D₀ · ∑_i (‖c₁ⱼₑₜ i‖_{L²} + ‖c₂ⱼₑₜ i‖_{L²}),
```

keeping `Λ` and `D₀` as *separate* coefficients — `Λ` on the difference arm, `D₀` on the fixed-pair
arm — which is essential: the `D₀` factor (the difference `C⁰` mass, depending on the perturbation
difference) may **not** be allowed to multiply the difference-`L²`-jet arm.

The proof is the genuine `L²` arithmetic: the squared metric `L²` norm is the integral of `rfns`
(`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq`), the two-product pointwise bound integrates
termwise (each `rfns` term is integrable on the compact base,
`integrable_riemannianFiberNormSq_toSection`) to `Λ²·∑‖wⱼₑₜ‖² + D₀²·∑(‖c₁ⱼₑₜ‖²+‖c₂ⱼₑₜ‖²)`, and the
square root is dominated by the two-arm sum via `√(α+β) ≤ √α + √β`, `√(Λ²·∑aᵢ²) = Λ·√(∑aᵢ²) ≤ Λ·∑aᵢ`,
and Cauchy–Schwarz `√(∑aᵢ²) ≤ ∑aᵢ` (`Finset.sum`-nonneg).  All conclusions are real-valued `L²`/`rfns`
inequalities; no `sorry`, no packaging. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **Cauchy–Schwarz square-root collapse.**  For a nonnegative finite family `a : ℕ → ℝ`,
`√(∑_{i < N} a i ^ 2) ≤ ∑_{i < N} a i`.  (Each `a i ≥ 0`, so `∑ a i ^ 2 ≤ (∑ a i) ^ 2`, and the
square root is monotone.) -/
private theorem sqrt_sum_sq_le_sum (N : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i ∈ Finset.range N, a i ^ 2) ≤ ∑ i ∈ Finset.range N, a i := by
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range N, a i := Finset.sum_nonneg fun i _ => ha i
  have hle : ∑ i ∈ Finset.range N, a i ^ 2 ≤ (∑ i ∈ Finset.range N, a i) ^ 2 := by
    -- `(∑ a)² = ∑ᵢ aᵢ·(∑ⱼ aⱼ) ≥ ∑ᵢ aᵢ·aᵢ = ∑ aᵢ²` by nonneg cross terms.
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact Finset.single_le_sum
      (f := fun k => a i * a k) (fun k _ => mul_nonneg (ha i) (ha k)) hi
  calc Real.sqrt (∑ i ∈ Finset.range N, a i ^ 2)
      ≤ Real.sqrt ((∑ i ∈ Finset.range N, a i) ^ 2) := Real.sqrt_le_sqrt hle
    _ = ∑ i ∈ Finset.range N, a i := by rw [Real.sqrt_sq hsum_nn]

omit [CompleteSpace E] in
/-- **The Hamilton/Moser two-product pointwise-to-`L²` lift.**

Let `Curv : SmoothCcTensor g₀ 0 c`, let `wjet : ∀ i, SmoothCcTensor g₀ 0 (vw i)` be the
difference-jet family, `cjet₁ cjet₂ : ∀ i, SmoothCcTensor g₀ 0 (vc i)` the two fixed-pair
endpoint-jet families, and `Λ, D₀ ≥ 0`.  If, for every base point `x`, the squared fibre norm of
`Curv` is dominated by the Hamilton/Moser two-product
```
rfns(Curv)(x) ≤ Λ² · ∑_{i < N} rfns(wjet i)(x)
              + (∑_{i < N} (rfns(cjet₁ i)(x) + rfns(cjet₂ i)(x))) · D₀²,
```
then the metric `L²` (semi)norms satisfy the **two-arm tame bound**
```
‖Curv‖ ≤ Λ · ∑_{i < N} ‖wjet i‖ + D₀ · ∑_{i < N} (‖cjet₁ i‖ + ‖cjet₂ i‖).
```

The genuine `L²` arithmetic of the pointwise-to-`L²` step, with the two constants kept on their
*separate* arms.  Proved outright from the integral characterization of the metric `L²` norm; no
posit. -/
theorem tensorL2Norm_le_of_pointwise_twoProduct_rfns_bound
    (g₀ : SmoothRiemannianMetric I M) {c : ℕ} (N : ℕ) (vw vc : ℕ → ℕ)
    (wjet : ∀ i, Integral.L2.SmoothCcTensor g₀ 0 (vw i))
    (cjet₁ cjet₂ : ∀ i, Integral.L2.SmoothCcTensor g₀ 0 (vc i))
    (Curv : Integral.L2.SmoothCcTensor g₀ 0 c) (Λ D₀ : ℝ) (hΛ : 0 ≤ Λ) (hD₀ : 0 ≤ D₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Curv.toSection x) ≤
        Λ ^ 2 * ∑ i ∈ Finset.range N,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vw i) x ((wjet i).toSection x)
          + (∑ i ∈ Finset.range N,
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₁ i).toSection x)
                + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₂ i).toSection x)))
            * D₀ ^ 2) :
    ‖Curv‖ ≤ Λ * ∑ i ∈ Finset.range N, ‖wjet i‖
      + D₀ * ∑ i ∈ Finset.range N, (‖cjet₁ i‖ + ‖cjet₂ i‖) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  -- Per-term `L²` norms (as `‖·‖`) and their squares (as integrals of `rfns`).
  set nw : ℕ → ℝ := fun i => ‖wjet i‖ with hnw_def
  set nc₁ : ℕ → ℝ := fun i => ‖cjet₁ i‖ with hnc₁_def
  set nc₂ : ℕ → ℝ := fun i => ‖cjet₂ i‖ with hnc₂_def
  have hnw_nn : ∀ i, 0 ≤ nw i := fun i => norm_nonneg _
  have hnc₁_nn : ∀ i, 0 ≤ nc₁ i := fun i => norm_nonneg _
  have hnc₂_nn : ∀ i, 0 ≤ nc₂ i := fun i => norm_nonneg _
  -- The integral bridge for each family member: `‖S‖² = ∫ rfns(S)`.
  have hbridge_w : ∀ i, nw i ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vw i) x ((wjet i).toSection x) ∂μ := by
    intro i
    simp only [hnw_def]
    rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) (wjet i), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (vw i) (wjet i)
  have hbridge_c₁ : ∀ i, nc₁ i ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₁ i).toSection x) ∂μ := by
    intro i
    simp only [hnc₁_def]
    rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) (cjet₁ i), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (vc i) (cjet₁ i)
  have hbridge_c₂ : ∀ i, nc₂ i ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₂ i).toSection x) ∂μ := by
    intro i
    simp only [hnc₂_def]
    rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) (cjet₂ i), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (vc i) (cjet₂ i)
  -- The `Curv` bridge.
  set nCurv : ℝ := ‖Curv‖ with hnCurv_def
  have hnCurv_nn : 0 ≤ nCurv := norm_nonneg _
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) Curv, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ c Curv
  -- Integrability of every `rfns` term.
  have hint_w : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vw i) x ((wjet i).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (vw i) (wjet i)
  have hint_c₁ : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₁ i).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (vc i) (cjet₁ i)
  have hint_c₂ : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₂ i).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (vc i) (cjet₂ i)
  -- The RHS integrand is integrable (finite sums of integrable, plus constants).
  set Fw : M → ℝ := fun x => ∑ i ∈ Finset.range N,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vw i) x ((wjet i).toSection x) with hFw_def
  set Fc : M → ℝ := fun x => ∑ i ∈ Finset.range N,
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₁ i).toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₂ i).toSection x)) with hFc_def
  have hint_Fw : MeasureTheory.Integrable Fw μ :=
    MeasureTheory.integrable_finset_sum (Finset.range N) (fun i _ => hint_w i)
  have hint_Fc : MeasureTheory.Integrable Fc μ :=
    MeasureTheory.integrable_finset_sum (Finset.range N) (fun i _ => (hint_c₁ i).add (hint_c₂ i))
  set RHS : M → ℝ := fun x => Λ ^ 2 * Fw x + Fc x * D₀ ^ 2 with hRHS_def
  have hint_RHS : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def]; exact (hint_Fw.const_mul (Λ ^ 2)).add (hint_Fc.mul_const (D₀ ^ 2))
  have hint_Curv : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Curv.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 c Curv
  -- Integrate the pointwise two-product bound.
  have hint_le : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 c x (Curv.toSection x) ∂μ)
      ≤ ∫ x, RHS x ∂μ := by
    refine MeasureTheory.integral_mono hint_Curv hint_RHS ?_
    intro x; rw [hRHS_def, hFw_def, hFc_def]; exact hpt x
  -- Evaluate `∫ RHS = Λ²·∑‖wjet‖² + D₀²·∑(‖cjet₁‖²+‖cjet₂‖²)`.
  have hintFw_eq : (∫ x, Fw x ∂μ) = ∑ i ∈ Finset.range N, nw i ^ 2 := by
    rw [hFw_def, MeasureTheory.integral_finset_sum (Finset.range N) (fun i _ => hint_w i)]
    exact Finset.sum_congr rfl fun i _ => (hbridge_w i).symm
  have hint_csum : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₁ i).toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (vc i) x ((cjet₂ i).toSection x)) μ :=
    fun i => (hint_c₁ i).add (hint_c₂ i)
  have hintFc_eq : (∫ x, Fc x ∂μ) = ∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2) := by
    rw [hFc_def, MeasureTheory.integral_finset_sum (Finset.range N) (fun i _ => hint_csum i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_add (hint_c₁ i) (hint_c₂ i), ← hbridge_c₁ i, ← hbridge_c₂ i]
  have hintRHS_eq : (∫ x, RHS x ∂μ) =
      Λ ^ 2 * (∑ i ∈ Finset.range N, nw i ^ 2)
        + (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D₀ ^ 2 := by
    rw [hRHS_def, MeasureTheory.integral_add (hint_Fw.const_mul (Λ ^ 2)) (hint_Fc.mul_const (D₀ ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, hintFw_eq, hintFc_eq]
  -- `nCurv² ≤ Λ²·∑nw² + (∑(nc₁²+nc₂²))·D₀²`.
  have hnCurvSq : nCurv ^ 2 ≤
      Λ ^ 2 * (∑ i ∈ Finset.range N, nw i ^ 2)
        + (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D₀ ^ 2 := by
    rw [hbridgeCurv]; exact le_trans hint_le (le_of_eq hintRHS_eq)
  -- Square-root domination by the two-arm sum.
  set Sw : ℝ := ∑ i ∈ Finset.range N, nw i with hSw_def
  set Sc : ℝ := ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) with hSc_def
  have hSw_nn : 0 ≤ Sw := Finset.sum_nonneg fun i _ => hnw_nn i
  have hSc_nn : 0 ≤ Sc := Finset.sum_nonneg fun i _ => add_nonneg (hnc₁_nn i) (hnc₂_nn i)
  -- `∑ nw² ≤ Sw²` and `∑(nc₁²+nc₂²) ≤ Sc²`, via the Cauchy–Schwarz collapse.
  have harm1 : Λ ^ 2 * (∑ i ∈ Finset.range N, nw i ^ 2) ≤ (Λ * Sw) ^ 2 := by
    have hcs : Real.sqrt (∑ i ∈ Finset.range N, nw i ^ 2) ≤ Sw := by
      rw [hSw_def]; exact sqrt_sum_sq_le_sum N nw hnw_nn
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range N, nw i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : ∑ i ∈ Finset.range N, nw i ^ 2 ≤ Sw ^ 2 := by
      have := Real.sq_sqrt hsum_nn
      nlinarith [Real.sqrt_nonneg (∑ i ∈ Finset.range N, nw i ^ 2), hcs, hSw_nn, this]
    calc Λ ^ 2 * (∑ i ∈ Finset.range N, nw i ^ 2) ≤ Λ ^ 2 * Sw ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Λ * Sw) ^ 2 := by ring
  have harm2 : (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D₀ ^ 2 ≤ (D₀ * Sc) ^ 2 := by
    -- `∑(nc₁²+nc₂²) ≤ ∑(nc₁+nc₂)² ≤ Sc²`.
    have hstep1 : (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2))
        ≤ ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [mul_nonneg (hnc₁_nn i) (hnc₂_nn i)]
    have hcs : Real.sqrt (∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2) ≤ Sc := by
      rw [hSc_def]; exact sqrt_sum_sq_le_sum N (fun i => nc₁ i + nc₂ i)
        (fun i => add_nonneg (hnc₁_nn i) (hnc₂_nn i))
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : ∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2 ≤ Sc ^ 2 := by
      have := Real.sq_sqrt hsum_nn
      nlinarith [Real.sqrt_nonneg (∑ i ∈ Finset.range N, (nc₁ i + nc₂ i) ^ 2), hcs, hSc_nn, this]
    have hsum_le : (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) ≤ Sc ^ 2 :=
      le_trans hstep1 hsq
    calc (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D₀ ^ 2 ≤ Sc ^ 2 * D₀ ^ 2 :=
          mul_le_mul_of_nonneg_right hsum_le (sq_nonneg _)
      _ = (D₀ * Sc) ^ 2 := by ring
  -- Combine: `nCurv² ≤ (Λ·Sw)² + (D₀·Sc)² ≤ (Λ·Sw + D₀·Sc)²`, hence `nCurv ≤ Λ·Sw + D₀·Sc`.
  have hΛSw_nn : 0 ≤ Λ * Sw := mul_nonneg hΛ hSw_nn
  have hD₀Sc_nn : 0 ≤ D₀ * Sc := mul_nonneg hD₀ hSc_nn
  have hcombine : nCurv ^ 2 ≤ (Λ * Sw + D₀ * Sc) ^ 2 := by
    have hcross : (Λ * Sw) ^ 2 + (D₀ * Sc) ^ 2 ≤ (Λ * Sw + D₀ * Sc) ^ 2 := by
      nlinarith [mul_nonneg hΛSw_nn hD₀Sc_nn]
    calc nCurv ^ 2 ≤ Λ ^ 2 * (∑ i ∈ Finset.range N, nw i ^ 2)
          + (∑ i ∈ Finset.range N, (nc₁ i ^ 2 + nc₂ i ^ 2)) * D₀ ^ 2 := hnCurvSq
      _ ≤ (Λ * Sw) ^ 2 + (D₀ * Sc) ^ 2 := add_le_add harm1 harm2
      _ ≤ (Λ * Sw + D₀ * Sc) ^ 2 := hcross
  have hfinal : nCurv ≤ Λ * Sw + D₀ * Sc := by
    nlinarith [hcombine, hnCurv_nn, add_nonneg hΛSw_nn hD₀Sc_nn,
      sq_nonneg (nCurv - (Λ * Sw + D₀ * Sc))]
  rw [hnCurv_def] at hfinal
  rw [hSw_def, hSc_def] at hfinal
  exact hfinal

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
