import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovTrivProjNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `L^2` integration of the chart-twist-inverted covariant-derivative norm sum

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base
point `α : M`, this file integrates the pointwise sum-over-directions bound
on the chart-twist-inverted covariant derivative (the headline of the
companion module `CovTrivProjNormBound`) against the Riemannian volume
measure on `M`. The resulting `L^2` estimate controls the partition-of-unity-
weighted Euclidean norm of the sum-over-directions by the `H^1` seminorm of
the underlying smooth compactly-supported tensor section.

## Strategy

The pointwise bound from `CovTrivProjNormBound` gives, for every smooth
compactly-supported `(r, s)`-tensor section `S` and every `b ∈ tsupport ρ_α`
(the chart-atlas partition-of-unity weight at `α`):

```
∑ i, ‖chartRSTwistInv α b r s (toModel (∇S(b)(e_i' b)))‖^2 ≤
  C · tensorCovDerivPointwiseInner g r s S S b,
```

where `e_i' b := chartBasisVecFiber α i b`. Off `tsupport ρ_α`, the partition-
of-unity weight `ρ_α(b)` vanishes, so multiplying the LHS by `ρ_α(b)` gives a
globally valid pointwise estimate, using `0 ≤ ρ_α ≤ 1`:

```
(ρ_α(b) · √(∑ i, ‖chartRSTwistInv α b r s (toModel (∇S(b)(e_i' b)))‖^2))^2 ≤
  C · tensorCovDerivPointwiseInner g r s S S b   (∀ b ∈ M).
```

Integrating this pointwise inequality against `riemannianVolumeMeasure g`
and using

```
∫ tensorCovDerivPointwiseInner g r s S S ≤
  tensorL2Inner g r s S.toFun S.toFun +
    ∫ tensorCovDerivPointwiseInner g r s S S =
  tensorH1Inner g r s S S = ‖S‖^2
```

(for `S : SmoothCcTensorH1 g r s`) gives the squared `L^2` bound by
`C · ‖S‖^2`. Taking the square root in `ENNReal` produces the headline
`eLpNorm (..) 2 (riemannianVolumeMeasure g) ≤ ENNReal.ofReal (√C) · ‖S‖₊`.

## Public theorems

* `exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm`
  — uniform-in-`S` `L^2` bound for the partition-of-unity-weighted
  Euclidean norm of the chart-twist-inverted covariant-derivative
  sum-over-directions, controlled by the `H^1` seminorm of `S`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Pointwise bound including the partition-of-unity factor

The headline of the companion module gives the sum-over-directions estimate
only on `tsupport ρ_α`. To obtain a global pointwise bound suitable for
integration over all of `M`, we multiply the LHS by `ρ_α(b)`: inside
`tsupport ρ_α` we use `0 ≤ ρ_α ≤ 1`; outside, `ρ_α(b) = 0` makes the LHS
vanish, while the RHS remains non-negative. -/

private lemma chartPou_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ^ 2 *
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨C, hC_nn, h_sum⟩ :=
    exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S b
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SqSum : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ‖chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 with hSqSum_def
  set Q : ℝ :=
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b with hQ_def
  have hSqSum_nn : 0 ≤ SqSum := by
    rw [hSqSum_def]
    refine Finset.sum_nonneg ?_
    intro i _
    exact sq_nonneg _
  have hQ_nn : 0 ≤ Q := by
    rw [hQ_def]
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S b
  by_cases hb : b ∈ tsupport ρ
  · -- Inside the support: chain `SqSum ≤ C · Q` from the headline with
    -- `ρ b ^ 2 ≤ 1` from `0 ≤ ρ b ≤ 1`.
    have hρ_nn : 0 ≤ ρ b := (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ρ b ≤ 1 := (chartAtlasPOU I M).le_one α b
    have hρ_sq_le_one : ρ b ^ 2 ≤ 1 := by
      have hsq : ρ b * ρ b ≤ 1 * 1 :=
        mul_le_mul hρ_le_one hρ_le_one hρ_nn (by linarith)
      have hsq' : ρ b * ρ b ≤ 1 := by linarith
      rw [sq]; exact hsq'
    have hSqSum_le : SqSum ≤ C * Q := by
      rw [hSqSum_def, hQ_def]
      exact h_sum S hb
    have hCQ_nn : 0 ≤ C * Q := mul_nonneg hC_nn hQ_nn
    calc ρ b ^ 2 * SqSum
        ≤ 1 * (C * Q) :=
          mul_le_mul hρ_sq_le_one hSqSum_le hSqSum_nn (by linarith)
      _ = C * Q := one_mul _
  · -- Outside the support: `ρ b = 0`, so LHS = 0.
    have hρ_zero : ρ b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    have hLHS_zero : ρ b ^ 2 * SqSum = 0 := by
      rw [hρ_zero]; ring
    rw [hLHS_zero]
    exact mul_nonneg hC_nn hQ_nn

/-! ## `eLpNorm` conversion helpers (private, file-local)

Mirrors of the helpers in `ComponentL2BoundUniform`: convert
`(eLpNorm f 2 μ)^2` to a lintegral of `‖f x‖ₑ^2`, bound it by
`ENNReal.ofReal (∫ |f x|^2 dμ)`, then take square roots. -/

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

/-! ## Coercion helper for `nnnorm` ↔ `ofReal` -/

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

/-! ## Integrated bound: the gradient term integrates below the `H^1` norm-sq -/

private lemma integral_tensorCovDerivPointwiseInner_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ∫ b, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        S.toCcTensor S.toCcTensor b
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ‖S‖ ^ 2 := by
  classical
  -- Expand `‖S‖^2 = tensorH1Inner = tensorL2Inner + ∫ grad`.
  have h_norm_sq :
      ‖S‖ ^ 2 =
        tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor :=
    SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
            S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  rw [h_norm_sq, tensorH1Inner_def]
  linarith

/-! ## Headline integrated bound

The squared `L^2(volume)` seminorm of the partition-of-unity-weighted
Euclidean norm of the sum-over-directions of the chart-twist-inverted
covariant derivative is controlled by `C · ‖S‖^2`. -/

private lemma sq_eLpNorm_chartPou_mul_sqrt_sum_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        (eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ i : Fin (Module.finrank ℝ E),
                    ‖chartRSTwistInv (I := I) (M := M) α b r s
                        (TensorRSSpace.toModel
                          (tensorCovDerivAt (I := I) (M := M) g r s
                            S.toCcTensor b
                            (chartBasisVecFiber (I := I) α i b)))‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C * ‖S‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    chartPou_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  -- Set notation for the integrand and the measure.
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SqSum : M → ℝ := fun b : M =>
    ∑ i : Fin (Module.finrank ℝ E),
      ‖chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S.toCcTensor b
              (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 with hSqSum_def
  set f : M → ℝ := fun b : M => ρ b * Real.sqrt (SqSum b) with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  -- Pointwise non-negativity of `SqSum`.
  have hSqSum_nn : ∀ b : M, 0 ≤ SqSum b := by
    intro b
    rw [hSqSum_def]
    refine Finset.sum_nonneg ?_
    intro i _
    exact sq_nonneg _
  -- Pointwise: `(ρ b * √SqSum b)^2 = ρ b^2 * SqSum b ≤ C * tensorCovDerivPointwiseInner`.
  have h_pt_sq : ∀ b : M, (f b) ^ 2 ≤
      C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        S.toCcTensor S.toCcTensor b := by
    intro b
    have h_eq : (f b) ^ 2 = ρ b ^ 2 * SqSum b := by
      rw [hf_def, mul_pow]
      rw [show Real.sqrt (SqSum b) ^ 2 = SqSum b from Real.sq_sqrt (hSqSum_nn b)]
    rw [h_eq]
    exact h_pt S.toCcTensor b
  -- ENNReal-valued pointwise bound.
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt_sq b)
  -- Convert `(eLpNorm f 2 μ)^2` to a lintegral.
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  -- Bound the lintegral by the lintegral of the RHS.
  have h_grad_int :
      Integrable (tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) μ :=
    tensorCovDerivPointwiseInner_integrable
      (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          S.toCcTensor S.toCcTensor b) μ :=
    h_grad_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          S.toCcTensor S.toCcTensor b) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s _ b)
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  -- Convert the RHS lintegral to `ofReal` of an integral.
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  -- Pull `C` out of the integral.
  have h_int_const_mul :
      ∫ b, C * tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ =
        C * ∫ b, tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ :=
    integral_const_mul _ _
  rw [h_int_const_mul] at h_lint_le
  -- Bound `∫ grad ≤ ‖S‖^2` and reassemble.
  have h_int_le :
      ∫ b, tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ ≤
      ‖S‖ ^ 2 :=
    integral_tensorCovDerivPointwiseInner_le_h1NormSq
      (I := I) (M := M) g r s S
  have h_norm_sq_nn : 0 ≤ ‖S‖ ^ 2 := sq_nonneg _
  have h_RHS_le :
      ENNReal.ofReal (C *
        ∫ b, tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ) ≤
        ENNReal.ofReal (C * ‖S‖ ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left h_int_le hC_nn
  exact h_lint_le.trans h_RHS_le

/-! ## Headline `L^2` estimate

The `L^2(riemannianVolumeMeasure g)` seminorm of the partition-of-unity-
weighted Euclidean norm of the sum-over-directions of the chart-twist-
inverted covariant derivative is uniformly bounded by `ENNReal.ofReal (√C)`
times the `H^1` seminorm of `S`, for a constant `C` depending only on
`(g, r, s, α)`. -/

/-- **Headline `L²` integration of the chart-twist-inverted covariant
derivative norm sum.** For a closed Riemannian manifold `(M, g)`, ranks
`(r, s)`, and a chart base point `α : M`, there is a non-negative real
constant `C` (depending only on `(g, r, s, α)`) such that for every smooth
compactly-supported `H^1` tensor section `S : SmoothCcTensorH1 g r s`,

```
eLpNorm
    (fun b => ρ_α(b) * √(∑_i ‖chartRSTwistInv α b r s
                          (toModel (∇S(b)(e_i' b)))‖²))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * ‖S‖₊,
```

where `e_i' b := chartBasisVecFiber α i b` is the chart-`α` basis fibre at
`b` and `ρ_α` is the chart-atlas partition-of-unity weight at `α`. The
constant `C` is independent of `S`. -/
theorem exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ i : Fin (Module.finrank ℝ E),
                    ‖chartRSTwistInv (I := I) (M := M) α b r s
                        (TensorRSSpace.toModel
                          (tensorCovDerivAt (I := I) (M := M) g r s
                            S.toCcTensor b
                            (chartBasisVecFiber (I := I) α i b)))‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_chartPou_mul_sqrt_sum_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S
  -- `C · ‖S‖^2 ≥ 0`; take sqrt-form of the squared bound.
  set T : ℝ := C * ‖S‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ T := mul_nonneg hC_nn (sq_nonneg _)
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hT_nn (h_sq S)
  -- `√(C · ‖S‖^2) = √C · ‖S‖`.
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_factor :
      Real.sqrt T = Real.sqrt C * ‖S‖ := by
    rw [hT_def, Real.sqrt_mul hC_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring,
      Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  -- Convert `ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞)`.
  rw [show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
    (coe_nnnorm_eq_ofReal_norm S).symm] at h_eLpNorm_le
  exact h_eLpNorm_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
