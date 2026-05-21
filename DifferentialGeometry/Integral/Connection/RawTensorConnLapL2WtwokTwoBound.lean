import DifferentialGeometry.Integral.Connection.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.FderivToWkpNormBridge

/-!
# Order-zero bound: chart-target POU-weighted L² of the chart-pulled
# tensor representation by the sum of chart-component L² norms

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, and a
chart base point `α : M`, this file ships a uniform bound for the
chart-α-target partition-of-unity-weighted L² norm-squared of the chart-pulled
model-fibre representation `tensorRSChartE_section_repr r s α T.toSection ∘
(extChartAt I α).symm ∘ toEuclidean.symm` of a smooth compactly-supported
`(r, s)`-tensor section `T`, in terms of the L² (= `wkpNorm 0 2`) norms of the
chart-frame scalar components `tensorChartComp g r s T α Idx Jdx` over the
chart-target image `chartTargetEuclid α`.

Concretely:

```
∫⁻ y in chartTargetEuclid α,
    ENNReal.ofReal (POU(symm y)² · ‖repr T (symm y)‖²) dvol ≤
  ENNReal.ofReal K *
    ∑ Idx, Σ Jdx,
      (wkpNorm 0 2 (tensorChartComp g r s T α Idx Jdx) (chartTargetEuclid α))²
```

with `K = (cardinality of (Idx, Jdx)) · basisNormConstant²` depending only on
`(g, r, s)` and the model space; in particular `K` is independent of `T`.

## Strategy

1. Pointwise on `M`: `‖tensorRSChartE_section_repr r s α T.toSection b‖² ≤
   K_basis · Σ Idx Σ Jdx |tensorChartComponentRaw α Idx Jdx b|²` via
   `reprNorm_le_sum_components` squared (Cauchy-Schwarz finite sum).

2. Multiply both sides by `POU(b)²` and rewrite `POU(b)² · |raw α Idx Jdx b|² =
   |POU(b) · raw α Idx Jdx b|² = |tensorChartComponentPou α Idx Jdx b|²`.

3. Pull through `ENNReal.ofReal` (LHS argument is non-negative) and integrate
   over `chartTargetEuclid α`.

4. For `y ∈ chartTargetEuclid α`, `tensorChartComp α Idx Jdx y =
   tensorChartComponentPou α Idx Jdx ((extChartAt I α).symm (toEuclidean.symm y))`.

5. The integral `∫⁻ y in chartTargetEuclid α, ENNReal.ofReal (|tensorChartComp y|²) dvol`
   equals `(eLpNorm tensorChartComp 2 (volume.restrict (chartTargetEuclid α)))² =
   (wkpNorm 0 2 tensorChartComp (chartTargetEuclid α))²` via
   `eLpNorm_eq_lintegral_rpow_enorm_toReal` and `wkpNorm_zero`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Pointwise squared bound from `reprNorm_le_sum_components` -/

/-- Pointwise squared bound: the squared model-fibre norm of the
chart-α-trivialised representation of `T.toSection` is bounded by a uniform
constant `K_basis` times the finite double sum of the squares of the raw
chart-frame scalar components. The constant `K_basis` depends only on the
ranks `(r, s)` and the model space. -/
private lemma reprNormSq_le_sum_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  -- The basic linear bound from `reprNorm_le_sum_components`.
  have h_lin := reprNorm_le_sum_components (I := I) (M := M) g r s T α b
  -- Rewrite RHS of `h_lin` as `(Σ pairs |raw|) * Bnorm`.
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_rhs_rewrite : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| * Bnorm) =
      (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm := by
    rw [Finset.sum_mul, hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| * Bnorm)]
  rw [hBnorm_def.symm] at h_lin
  rw [h_rhs_rewrite] at h_lin
  -- Now `h_lin : ‖R‖ ≤ (Σ pairs |raw|) * Bnorm`.
  -- Square both sides (using nonnegativity).
  have h_sum_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_sq : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 := by
    have := mul_le_mul h_lin h_lin (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  -- Apply Cauchy-Schwarz: `(Σ |raw|)² ≤ N · Σ |raw|²`.
  have hCS : (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p => |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by
      simp
    rw [show (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| ^ 2) =
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 from
      Finset.sum_congr rfl (fun _ _ => by rw [sq_abs]), h_sum_one] at hbase
    exact hbase
  -- Combine: `‖R‖² ≤ ((Σ |raw|) · Bnorm)² ≤ N · Σ |raw|² · Bnorm²`.
  set sumSq : ℝ := ∑ p ∈ V,
    (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2
  have h_sumSq_nn : 0 ≤ sumSq :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_combined : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 * sumSq := by
    -- `((Σ |raw|) * Bnorm)² = (Σ |raw|)² * Bnorm²`.
    have h_sq_eq : ((∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 = (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    have h_bound : (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
          Bnorm ^ 2 ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_mul
    calc ‖tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) b‖ ^ 2
        ≤ (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_bound
      _ = (V.card : ℝ) * Bnorm ^ 2 * sumSq := by ring
  -- Rewrite the sumSq from the pair-sum form back to the nested double-sum form.
  have h_sumSq_eq : sumSq = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
    change (∑ p ∈ V, _) = _
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2)]
  rw [h_sumSq_eq] at h_combined
  exact h_combined

/-! ## Squared L² identity: `(eLpNorm f 2 μ)² = ∫⁻ ‖f‖ₑ² dμ` for real-valued `f` -/

/-- For a real-valued function `f` and a measure `μ`, the square of `eLpNorm f 2 μ`
equals the lintegral of `‖f x‖ₑ ^ 2`. -/
private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  -- Reduce the integrand's rpow to a natural pow.
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
  -- Show `(I ^ (1/2)) ^ 2 = I` via `ENNReal.rpow_natCast`, `ENNReal.rpow_mul`.
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

/-! ## The headline -/

/-- **Order-0 chart-target POU-weighted L² bound for the chart-pulled tensor
representation by the sum of chart-component L² norms.** For a smooth closed
Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, and a chart base point
`α : M`, there is a non-negative constant `K` (depending only on `(g, r, s)`
and the model space; independent of `T`) such that for every smooth
compactly-supported `(r, s)`-tensor section `T`, the chart-target Lebesgue
integral of the partition-of-unity-weighted squared model-fibre norm of the
chart-pulled representation of `T.toSection` is bounded by `K` times the
finite double sum of the squared `L²`-norms (= `wkpNorm 0 2`) of the
chart-frame scalar components `tensorChartComp g r s T α Idx Jdx` over the
chart target. -/
theorem chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (wkpNorm (d := Module.finrank ℝ E) 0 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
  classical
  -- The constant: `N · Bnorm²` where `N` is the cardinality of the (Idx, Jdx)
  -- pair set and `Bnorm` is the chart-basis-norm constant.
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set N : ℝ := (V.card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * Bnorm ^ 2, mul_nonneg hN_nn (sq_nonneg _), ?_⟩
  intro T
  -- Notation for the chart-symm composition.
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  -- LHS integrand.
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) (sym y)‖ ^ 2) with hlhs_def
  -- RHS sum-integrand: use `tensorChartComp` directly to avoid measurability issues.
  set rhsIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
    with hrhs_def
  -- Step 1: Pointwise bound `lhsIntegrand y ≤ ofReal(N · Bnorm²) * Σ Σ rhsIntegrand`
  -- on `chartTargetEuclid α`.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y := by
    intro y _hy
    -- POU(b) ≥ 0; ‖repr‖² ≥ 0.
    set b : M := sym y
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b
    set V_norm : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b‖
    have hρ_nn : 0 ≤ ρ :=
      (chartAtlasPOU I M).nonneg α b
    have hV_norm_nn : 0 ≤ V_norm := norm_nonneg _
    -- Pointwise squared bound from `reprNormSq_le_sum_components_sq`.
    have h_sq := reprNormSq_le_sum_components_sq (I := I) (M := M) g r s T α b
    -- Multiply both sides by ρ² ≥ 0.
    have h_scaled : ρ ^ 2 * V_norm ^ 2 ≤ ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
    -- Distribute ρ² inside the double sum.
    have h_distrib : ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
      rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ρ ^ 2 * (∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring
    rw [h_distrib] at h_scaled
    -- Now lift to ENNReal via `ENNReal.ofReal_le_ofReal`.
    have hLHS_eq : lhsIntegrand y = ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) := by
      change ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (V_norm ^ 2) = _
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hLHS_eq]
    -- Refactor RHS in ENNReal.
    have h_ennreal :
        ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) ≤
        ENNReal.ofReal (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      ENNReal.ofReal_le_ofReal h_scaled
    refine le_trans h_ennreal ?_
    -- Decompose `ofReal(N · Bnorm² · Σ Σ ρ² · raw²) =
    --   ofReal(N · Bnorm²) · ofReal(Σ Σ ρ² · raw²)`.
    rw [ENNReal.ofReal_mul (mul_nonneg hN_nn (sq_nonneg _))]
    -- Distribute ofReal through the double sum.
    have h_ofReal_double_sum :
        ENNReal.ofReal
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg
          (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [h_ofReal_double_sum]
    -- Match each summand `ofReal(ρ² · raw²) = rhsIntegrand Idx Jdx y`.
    -- For y ∈ chartTargetEuclid α: tensorChartComp y = POU(b) · raw α Idx Jdx b.
    have h_sum_eq :
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2)) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y := by
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (ρ ^ 2 *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
      have h_apply := tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx _hy
      rw [h_apply]
      -- tensorChartComponentPou α Idx Jdx b = ρ * raw α Idx Jdx b
      have h_pou_eq : tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx b =
          ρ * tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
        unfold tensorChartComponentPou
        rfl
      rw [h_pou_eq]
      congr 1
      ring
    rw [h_sum_eq]
  -- Step 2: integrate the pointwise bound over chartTargetEuclid α.
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal (N * Bnorm ^ 2) *
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rhsIntegrand Idx Jdx y
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  -- Pull the constant out and swap sum/integral.
  rw [show (fun y : EuclN =>
      ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y) =
      (fun y : EuclN =>
        ENNReal.ofReal (N * Bnorm ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) from rfl] at h_int_mono
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_int_mono
  -- Each rhsIntegrand Idx Jdx is measurable since tensorChartComp is continuous.
  have h_rhsIntegrand_meas : ∀ Idx Jdx,
      Measurable (fun y : EuclN => rhsIntegrand Idx Jdx y) := by
    intro Idx Jdx
    -- rhsIntegrand Idx Jdx y = ENNReal.ofReal ((tensorChartComp y)^2).
    refine ENNReal.measurable_ofReal.comp ?_
    refine (continuous_pow 2).measurable.comp ?_
    exact (tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx).measurable
  -- Distribute integral over the double finite sum.
  have h_int_double_sum :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.lintegral_finset_sum _
      (fun Idx _ => by
        exact Finset.measurable_sum _ (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact MeasureTheory.lintegral_finset_sum _
      (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx)
  rw [h_int_double_sum] at h_int_mono
  -- Identify each chart-target rhsIntegrand integral with (wkpNorm 0 2 ...)².
  have h_per_idx_jdx : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    -- rhsIntegrand Idx Jdx y = ENNReal.ofReal ((tensorChartComp y)^2) = ‖tensorChartComp y‖ₑ ^ 2.
    -- Identify `ENNReal.ofReal (x^2) = (ENNReal.ofReal |x|)^2 = ‖x‖ₑ^2`.
    have h_rhs_eq_enorm :
        (fun y : EuclN => rhsIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2) := by
      funext y
      change ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
        ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
      rw [show ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
          ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
      rw [show ENNReal.ofReal
          (‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2) =
            (ENNReal.ofReal
              ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖) ^ 2 from
        ENNReal.ofReal_pow (norm_nonneg _) 2]
      rw [ofReal_norm_eq_enorm]
    rw [h_rhs_eq_enorm]
    -- And the L²-sq identity.
    have h_sq_eLp :=
      sq_eLpNorm_two_eq_lintegral_enorm_sq
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
    rw [show ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂(volume : Measure EuclN) =
          ∫⁻ y,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from rfl]
    rw [← h_sq_eLp]
    rw [show wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) =
          eLpNorm (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from
      wkpNorm_zero (d := Module.finrank ℝ E) 2 _ _]
  -- Bound the per-(Idx, Jdx) integral and finish.
  refine le_trans h_int_mono ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  refine Finset.sum_le_sum (fun Idx _ => ?_)
  refine Finset.sum_le_sum (fun Jdx _ => ?_)
  exact h_per_idx_jdx Idx Jdx

/-! ## Order-1 chart-pushed POU and its globally-smooth extension -/

/-- The chart-pushed POU weight: the EuclN-side function
`y ↦ POU(extChartAt.symm (toEuclidean.symm y))`, extended by `0` off
`chartTargetEuclid α`. -/
private noncomputable def chartPouEucl (α : M) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

private lemma chartPouEucl_apply_of_mem (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold chartPouEucl; exact if_pos hy

private lemma chartPouEucl_apply_of_notMem (α : M) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y = 0 := by
  classical
  unfold chartPouEucl; exact if_neg hy

/-- The chart-pushed POU weight is `ContDiff ℝ ∞` on EuclN. The proof mirrors
`tensorChartComponent_contMDiff`: inside chartTargetEuclid the formula gives
smoothness, and outside, the function vanishes on an open neighborhood. -/
private lemma chartPouEucl_contDiff (α : M) :
    ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞ f :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hformula_smooth :
        ContDiffOn ℝ ∞
          (fun z : EuclN =>
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
        ContinuousLinearEquiv.contDiff _
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
          (chartTargetEuclid (I := I) (M := M) α)
          (extChartAt I α).target := by
        intro z hz
        rcases hz with ⟨w, hw_target, hwz⟩
        have h_eq : (toEuclidean (E := E)).symm z = w := by
          rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) y := hformula_smooth y hy_target
    have hformula_at : ContDiffAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
      hwithin.contDiffAt (hOpen.mem_nhds hy_target)
    refine hformula_at.congr_of_eventuallyEq ?_
    filter_upwards [hOpen.mem_nhds hy_target] with z hz
    -- f (symm (toEuc.symm z)) = chartPouEucl z when z ∈ chartTargetEuclid α.
    exact (chartPouEucl_apply_of_mem (I := I) (M := M) α hz)
  · -- Off chartTargetEuclid α: locally constant 0.
    have hcarrier_subset_target :
        K ⊆ chartTargetEuclid (I := I) (M := M) α := by
      intro z hz_carrier
      rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
      have hx_src : x ∈ (extChartAt I α).source := hsub_target hx_supp
      have hw_target : w ∈ (extChartAt I α).target := by
        rw [← hxw]; exact (extChartAt I α).map_source hx_src
      exact ⟨w, hw_target, hwz⟩
    have hy_off : y ∉ K := fun hy_in =>
      hy_target (hcarrier_subset_target hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    by_cases hz_target :
        z ∈ chartTargetEuclid (I := I) (M := M) α
    · -- z ∈ chart target but not in K: f vanishes at the preimage.
      obtain ⟨w, hw_target, hwz⟩ := hz_target
      have hz_target' :
          z ∈ chartTargetEuclid (I := I) (M := M) α := ⟨w, hw_target, hwz⟩
      have h_eq : (toEuclidean (E := E)).symm z = w := by
        rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hz_target']
      -- Show: f ((extChartAt I α).symm (toEuclidean.symm z)) = 0.
      by_contra hne_f
      apply hz
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          tsupport f := subset_tsupport _ hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwz⟩
    · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hz_target

/-- The chart-pushed POU weight has compact support. -/
private lemma chartPouEucl_hasCompactSupport (α : M) :
    HasCompactSupport (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- Show tsupport chartPouEucl ⊆ K.
  apply HasCompactSupport.intro (K := K) hK_compact
  intro y hy_notK
  -- y ∉ K ⇒ chartPouEucl y = 0.
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- y ∈ chartTargetEuclid α but ∉ K: f vanishes at preimage.
    obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [chartPouEucl_apply_of_mem (I := I) (M := M) α
        ⟨w, hw_target, hwy⟩]
    -- Show f ((extChartAt I α).symm (toEuclidean.symm y)) = 0.
    by_contra hne_f
    apply hy_notK
    have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport f := subset_tsupport _ hne_f
    rw [h_eq] at hin_supp
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
  · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hy_target

/-- The Fréchet derivative of the chart-pushed POU weight is bounded on EuclN. -/
private lemma exists_chartPouEucl_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ y : EuclN, ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α) y‖ ≤ K_pou := by
  classical
  have hCD : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have hHCS : HasCompactSupport (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_hasCompactSupport (I := I) (M := M) α
  -- The Fréchet derivative is continuous and has compact support.
  have h_fderiv_cont : Continuous (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hCD.continuous_fderiv (by norm_num)
  have h_fderiv_compactSupport : HasCompactSupport (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hHCS.fderiv ℝ
  -- A continuous compactly-supported function on a metric space has bounded norm.
  obtain ⟨K_raw, hK_bound⟩ := h_fderiv_cont.bounded_above_of_compact_support
    h_fderiv_compactSupport
  refine ⟨max K_raw 0, le_max_right _ _, ?_⟩
  intro y
  exact le_trans (hK_bound y) (le_max_left _ _)

/-! ## Differentiability of `tensorChartComponentRaw α Idx Jdx ∘ extChartAt.symm`
on a chart-target point -/

/-- The chart-pulled raw component is `ContDiffOn ℝ ∞` on the chart target. -/
private lemma tensorChartComponentRaw_symm_contDiffOn_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro e he_tgt
    have hsrc : (extChartAt I α).symm e ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target he_tgt
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  exact hcomp.contDiffOn

/-- The chart-pulled POU is `ContDiffOn ℝ ∞` on the chart target. -/
private lemma chartAtlasPOU_symm_contDiffOn_target (α : M) :
    ContDiffOn ℝ ∞
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  -- Use `scalarOnE_contDiffOn` for the POU function viewed as a smooth M → ℝ.
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I) α hf_smooth

/-- Differentiability of the chart-pulled POU function at any chart-target point. -/
private lemma chartAtlasPOU_symm_differentiableAt
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) e := by
  have hcd := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

/-- Differentiability of the chart-pulled raw component at any chart-target point. -/
private lemma tensorChartComponentRaw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e := by
  have hcd := tensorChartComponentRaw_symm_contDiffOn_target
    (I := I) (M := M) g r s T α Idx Jdx
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

/-! ## Identification on the chart target via toEuclidean -/

/-- For `y ∈ chartTargetEuclid α`, the chart component on EuclN equals the
chart-pulled POU-weighted raw scalar on M, pulled back via `extChartAt.symm` and
`toEuclidean.symm`. -/
private lemma tensorChartComp_eq_pou_mul_raw_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
  -- `tensorChartComponentPou α IJ b = POU(b) · raw IJ(b)`.
  unfold tensorChartComponentPou
  rfl

/-- For `e ∈ (extChartAt I α).target`, the chart component on EuclN evaluated at
`toEuclidean e` equals the chart-pulled POU-weighted raw scalar evaluated at the
manifold point. -/
private lemma tensorChartComp_toEuclidean_eq_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [tensorChartComp_eq_pou_mul_raw_pulled
    (I := I) (M := M) g r s T α Idx Jdx hy, h_eq]

/-- For `e ∈ (extChartAt I α).target`, the chart-pulled POU-weighted raw
component, expressed via the EuclN-side `tensorChartComp` and `toEuclidean`. -/
private lemma pou_mul_raw_eq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) =
      tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) :=
  (tensorChartComp_toEuclidean_eq_pou_mul_raw
    (I := I) (M := M) g r s T α Idx Jdx he).symm

/-- For `e ∈ (extChartAt I α).target`, the chart-pulled POU function equals the
EuclN-side chartPouEucl at `toEuclidean e`. -/
private lemma chartPouEucl_toEuclidean_eq_pou_symm
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    chartPouEucl (I := I) (M := M) α ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hy, h_eq]

/-! ## Identification of `(POU · raw IJ) ∘ symm` with the EuclN-side
`tensorChartComp ∘ toEuclidean` and its differentiability -/

/-- The pointwise pre-product identity, lifted from the chart-target to a
function-level eventual equality near a target point. -/
private lemma pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e') *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact pou_mul_raw_eq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he'

/-- The pointwise pre-product fderiv identity, on the chart target. -/
private lemma fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e :=
  (pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he).fderiv_eq

/-- The Fréchet derivative of `tensorChartComp ∘ toEuclidean` on E equals the
composition of the EuclN-side Fréchet derivative with `toEuclidean`. -/
private lemma fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (e : E) :
    fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hcomp_smooth : ContDiff ℝ ∞
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
  have h_chain : fderiv ℝ
      ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hcomp_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) =
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  -- `fderiv ℝ toEuclidean e = toEuclidean` as a CLM.
  congr 1
  exact (toEuclidean (E := E)).fderiv

/-- Similarly, the Fréchet derivative of `chartPouEucl ∘ toEuclidean` on E. -/
private lemma fderiv_chartPouEucl_toEuclidean (α : M) (e : E) :
    fderiv ℝ
        (fun e' : E => chartPouEucl (I := I) (M := M) α
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hpou_smooth : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have h_chain : fderiv ℝ
      ((chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hpou_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) =
      (chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  congr 1
  exact (toEuclidean (E := E)).fderiv

/-! ## The chart-pulled POU function expressed via EuclN-side chartPouEucl -/

/-- The chart-pulled POU function equals `chartPouEucl ∘ toEuclidean` on the
chart target. -/
private lemma pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact (chartPouEucl_toEuclidean_eq_pou_symm (I := I) (M := M) α he').symm

/-- The Fréchet derivative of the chart-pulled POU function equals
`fderiv chartPouEucl (toEuclidean e) ∘ toEuclidean` on the chart target. -/
private lemma fderiv_pou_symm_eq
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [(pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (I := I) (M := M) α he).fderiv_eq]
  exact fderiv_chartPouEucl_toEuclidean (I := I) (M := M) α e

/-! ## Uniform bound on the chart-pulled POU Fréchet derivative on E -/

/-- The chart-pulled POU Fréchet derivative is uniformly bounded on
`(extChartAt I α).target`. -/
private lemma exists_pou_symm_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ e ∈ (extChartAt I α).target,
        ‖fderiv ℝ
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ≤ K_pou := by
  classical
  -- Use the EuclN-side K_pou bound and the chain rule.
  obtain ⟨K_eucl, hK_nn, hK_bound⟩ :=
    exists_chartPouEucl_fderiv_uniform_bound (I := I) (M := M) α
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  refine ⟨K_eucl * NtoE, mul_nonneg hK_nn hNtoE_nn, ?_⟩
  intro e he
  rw [fderiv_pou_symm_eq (I := I) (M := M) α he]
  -- Bound the operator norm of the composition.
  have hbound : ‖(fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ≤
      ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)‖ *
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  refine le_trans hbound ?_
  exact mul_le_mul_of_nonneg_right (hK_bound _) hNtoE_nn

/-! ## Topological-support bound for the chart-α component on EuclN -/

/-- The topological support of `tensorChartComp g r s T α Idx Jdx` is contained in
`chartTargetEuclid α`. Since `tensorChartComp` equals `0` outside the chart target
and is identified with the chart-Euclidean push of `tensorChartComponentPou`,
whose carrier is contained in the compact `toEuclidean`-image of the chart of
`tsupport (POU * raw)` — itself a subset of `chartTargetEuclid α`. -/
lemma tensorChartComp_tsupport_subset_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  -- Reuse the explicit compact-support carrier from
  -- `tensorChartComponent_hasCompactSupport`.
  set f : M → ℝ := tensorChartComponentPou (I := I) (M := M)
    g r s T α Idx Jdx with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  set K : Set EuclN :=
    (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_src : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_src
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- `K ⊆ chartTargetEuclid α`.
  have hK_subset_target : K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro z hz_carrier
    rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
    have hx_src : x ∈ (extChartAt I α).source := hsub_src hx_supp
    have hw_target : w ∈ (extChartAt I α).target := by
      rw [← hxw]; exact (extChartAt I α).map_source hx_src
    exact ⟨w, hw_target, hwz⟩
  -- Show that `support tensorChartComp ⊆ K`.
  have h_supp_K : Function.support
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ⊆ K := by
    intro y hy_supp
    by_contra hyK
    apply hy_supp
    by_cases hy_target :
        y ∈ chartTargetEuclid (I := I) (M := M) α
    · rcases hy_target with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      -- `tensorChartComp y = tensorChartComponentPou (symm w)`, but we want
      -- this to equal 0 to derive the contradiction.
      rw [tensorChartComp_def, tensorChartComponent_def,
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α f ⟨w, hw_target, hwy⟩]
      by_contra hne_f
      apply hyK
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
          tsupport f := by
        apply subset_tsupport
        exact hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      exact ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
    · rw [tensorChartComp_def, tensorChartComponent_def]
      exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α f hy_target
  -- `tsupport = closure support ⊆ K` (closed) `⊆ chartTargetEuclid α`.
  refine (closure_minimal h_supp_K hK_closed).trans hK_subset_target

/-! ## Order-1 chart-target POU-weighted L² of the chart-pulled tensor
representation by chart-component data -/

/-- The squared `eLpNorm` identity: for a real-valued function `f` and a measure `μ`,
`(eLpNorm f 2 μ)² = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ`. -/
private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq f μ]
  refine lintegral_congr ?_
  intro x
  rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs],
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm_eq_enorm]

/-- The chart-α-pulled `repr T` is differentiable at any chart-target point. -/
lemma repr_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e := by
  classical
  -- Reduce `e` to `extChartAt I α b` for `b := (extChartAt I α).symm e`.
  set b : M := (extChartAt I α).symm e
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  -- The fderiv bound is at `extChartAt I α b`, but
  -- `extChartAt I α b = extChartAt I α ((extChartAt I α).symm e) = e`.
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  -- Differentiability at `extChartAt I α b` from the per-component lemma.
  -- We need to construct the result at `e`.
  -- Use `fderiv_repr_opNorm_le_sum_fderiv_components` to get differentiability:
  -- actually we need DifferentiableAt directly. Build it from the structure of
  -- the sum of `(scalar ∘ symm) • basis` terms.
  -- Each scalar term `tensorChartComponentRaw α Idx Jdx ∘ (extChartAt I α).symm`
  -- is DifferentiableAt at `e` via `chart_pulled_component_differentiableAt`
  -- applied at b (since `extChartAt I α b = e`).
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  refine DifferentiableAt.fun_sum (fun Idx _ => ?_)
  refine DifferentiableAt.fun_sum (fun Jdx _ => ?_)
  refine DifferentiableAt.smul_const ?_ _
  -- `chart_pulled_component_differentiableAt` provides differentiability at
  -- `extChartAt I α b = e`.
  have hdiff := chart_pulled_component_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx hb_chart
  rwa [he_eq] at hdiff

/-- The chart-pulled `tensorChartComponentRaw α Idx Jdx ∘ symm` is differentiable at
any chart-target point. (A renaming of an existing helper for ergonomic reuse.) -/
private lemma raw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e :=
  tensorChartComponentRaw_symm_differentiableAt
    (I := I) (M := M) g r s T α Idx Jdx he

/-- The fderiv of `(POU · raw_IJ) ∘ symm` at a chart-target point factors via
the EuclN-side `tensorChartComp`: it equals `fderiv tensorChartComp_IJ (toEucl e)
∘ toEucl`. -/
private lemma fderiv_pou_raw_symm_eq_chain
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he]
  exact fderiv_tensorChartComp_toEuclidean (I := I) (M := M) g r s T α Idx Jdx e

/-- The Leibniz expansion of `fderiv (POU · raw_IJ ∘ symm)` at a chart-target
point. -/
private lemma fderiv_pou_raw_symm_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e) •
          fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e +
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e) •
          fderiv ℝ
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e := by
  classical
  -- Apply `fderiv_fun_mul` to the product of two differentiable functions.
  have hP_diff : DifferentiableAt ℝ
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) e :=
    chartAtlasPOU_symm_differentiableAt (I := I) (M := M) α he
  have hR_diff : DifferentiableAt ℝ
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) e :=
    raw_symm_differentiableAt (I := I) (M := M) g r s T α Idx Jdx he
  -- `fderiv_fun_mul`: fderiv (c · d) = c x • fderiv d + d x • fderiv c.
  exact fderiv_fun_mul hP_diff hR_diff

/-! ## Pointwise quadratic bound on `‖fderiv (repr ∘ symm)‖²` -/

/-- Pointwise (squared) bound: at any chart-target point, the squared operator
norm of `fderiv (repr T ∘ symm)` is bounded by `N · Bnorm²` times the finite
double sum of `‖fderiv (raw_IJ ∘ symm)‖²`. -/
lemma fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {e : E}
    (he : e ∈ (extChartAt I α).target) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        e‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  -- Reduce `e` to `extChartAt I α b`.
  set b : M := (extChartAt I α).symm e with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target he
  have hb_chart : b ∈ (chartAt H α).source := by
    rwa [← extChartAt_source_eq_chartAt_source (I := I)]
  have he_eq : extChartAt I α b = e := (extChartAt I α).right_inv he
  have hbasis_le : ∀ Idx Jdx, ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤ Bnorm := by
    intro Idx Jdx
    exact tensorChartBasisElement_norm_le (E := E) r s Idx Jdx
  -- Apply existing per-component fderiv decomposition at `extChartAt I α b = e`.
  have h_lin :=
    fderiv_repr_opNorm_le_sum_fderiv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
  rw [he_eq] at h_lin
  -- Bound the RHS of `h_lin` by `(Σ_IJ ‖fderiv (raw_IJ ∘ symm) e‖) · Bnorm`.
  have h_rhs_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ *
              ‖tensorChartBasisElement (E := E) r s Idx Jdx‖) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact mul_le_mul_of_nonneg_left (hbasis_le Idx Jdx) (norm_nonneg _)
  have h_norm_le : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ Idx, ∑ Jdx,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := h_lin.trans h_rhs_le
  -- Rewrite double sum as sum over `V`.
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_sum_pair_eq :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)]
  -- Square both sides.
  have h_sum_nn :
      0 ≤ (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_le' : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [← h_sum_pair_eq] at h_norm_le; exact h_norm_le
  have h_norm_sq : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ((∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 := by
    have := mul_le_mul h_norm_le' h_norm_le' (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  -- Cauchy-Schwarz on the sum.
  have hCS :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    exact hbase
  -- Combine.
  have h_combined : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 *
        ∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have h_sq_eq : ((∑ p ∈ V,
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 = (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    calc ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ (∑ p ∈ V,
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * (∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) * Bnorm ^ 2 := h_mul
      _ = (V.card : ℝ) * Bnorm ^ 2 *
            ∑ p ∈ V,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by ring
  -- Rewrite the pair sum back as nested double-sum.
  have h_pair_to_nest :
      (∑ p ∈ V,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2)]
  rw [h_pair_to_nest] at h_combined
  exact h_combined

/-! ## Pointwise scaled bound combining the chart-pulled repr fderiv with
    the chart-component fderiv and the raw component -/

/-- **Pointwise scaled bound.** On the chart target, the POU²-scaled squared
chart-pulled-repr Fréchet-derivative norm is bounded by `C1` times the sum of
squared Fréchet-derivative norms of `tensorChartComp_IJ` at `toEuclidean e`,
plus `C2` times the sum of squared raw component values at
`(extChartAt I α).symm e`, with explicit constants:

```
C1 = 2 * N * Bnorm² * ‖toEuclidean‖²
C2 = 2 * N * Bnorm² * K_pou²
```

where `N` is the cardinality of the `(Idx, Jdx)` pair set, `Bnorm` is the
chart-basis norm constant, and `K_pou` is a uniform upper bound on the
operator norm of the Fréchet derivative of the chart-pulled
partition-of-unity. This is the pointwise core of the order-`1` chart-target
POU-weighted `L²` bound on the chart-pulled repr Fréchet derivative. -/
lemma pou_sq_fderiv_repr_sq_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (K_pou : ℝ) (hK_pou_nn : 0 ≤ K_pou)
    (hK_pou_bound : ∀ e ∈ (extChartAt I α).target,
      ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm e)) ^ 2) *
      (‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2 * K_pou ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e)
  -- ρ ≥ 0.
  have hρ_nn : 0 ≤ ρ := by
    have := (chartAtlasPOU I M).nonneg α ((extChartAt I α).symm e); exact this
  -- Use h_sq from `fderiv_repr_opNormSq_le_sum_fderiv_components_sq`.
  have h_sq := fderiv_repr_opNormSq_le_sum_fderiv_components_sq
    (I := I) (M := M) g r s T α (e := e) he
  -- Multiply both sides by ρ².
  have h_scaled : ρ ^ 2 *
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  -- Bound ρ² · ‖fderiv (raw_IJ ∘ symm) e‖² per IJ.
  have h_per_IJ : ∀ Idx Jdx,
      ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2 := by
    intro Idx Jdx
    -- Leibniz: `fderiv (P · R) e = ρ • fderiv R + raw • fderiv P`
    -- ⇒ `ρ • fderiv R = fderiv (P · R) e - raw • fderiv P`
    -- ⇒ `‖ρ • fderiv R‖ ≤ ‖fderiv (P · R) e‖ + |raw| · ‖fderiv P‖`
    set raw_val : ℝ := tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e)
    set FR : E →L[ℝ] ℝ := fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) e
    set FP : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e
    set L : E →L[ℝ] ℝ := fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e
    have hleibniz : L = ρ • FR + raw_val • FP := by
      simpa [L, FR, FP, raw_val, ρ] using
        fderiv_pou_raw_symm_leibniz (I := I) (M := M) g r s T α Idx Jdx he
    -- ρ • FR = L - raw_val • FP
    have h_eq : ρ • FR = L - raw_val • FP := by
      rw [hleibniz]; abel
    -- Take norms and squares.
    have hnorm : ‖ρ • FR‖ ≤ ‖L‖ + |raw_val| * ‖FP‖ := by
      rw [h_eq]
      refine le_trans (norm_sub_le _ _) ?_
      refine add_le_add le_rfl ?_
      rw [norm_smul, Real.norm_eq_abs]
    have hρFR : ‖ρ • FR‖ = ρ * ‖FR‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ_nn]
    rw [hρFR] at hnorm
    have hρFR_nn : 0 ≤ ρ * ‖FR‖ := mul_nonneg hρ_nn (norm_nonneg _)
    have hLraw_nn : 0 ≤ ‖L‖ + |raw_val| * ‖FP‖ :=
      add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    have hsq : (ρ * ‖FR‖) ^ 2 ≤ (‖L‖ + |raw_val| * ‖FP‖) ^ 2 := by
      exact pow_le_pow_left₀ hρFR_nn hnorm 2
    -- (a + b)² ≤ 2 a² + 2 b².
    have hexp : (‖L‖ + |raw_val| * ‖FP‖) ^ 2 ≤ 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 := by
      have h := sq_nonneg (‖L‖ - |raw_val| * ‖FP‖)
      nlinarith [h]
    have hρ_sq_FR_sq : ρ ^ 2 * ‖FR‖ ^ 2 = (ρ * ‖FR‖) ^ 2 := by ring
    rw [hρ_sq_FR_sq]
    refine le_trans hsq (le_trans hexp ?_)
    -- Bound ‖L‖² and (|raw_val| · ‖FP‖)².
    -- L = fderiv tensorChartComp_IJ (toEucl e) ∘ toEucl, so ‖L‖ ≤ ‖fderiv tensorChartComp_IJ (toEucl e)‖ · NtoE.
    have hL_eq := fderiv_pou_raw_symm_eq_chain (I := I) (M := M)
      g r s T α Idx Jdx he
    have hL_bound : ‖L‖ ≤
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ * NtoE := by
      change ‖fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e‖ ≤ _
      rw [hL_eq]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hL_nn : 0 ≤ ‖L‖ := norm_nonneg _
    have hLsq : ‖L‖ ^ 2 ≤
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 :=
      pow_le_pow_left₀ hL_nn hL_bound 2
    -- ‖FP‖ ≤ K_pou.
    have hFP_bound : ‖FP‖ ≤ K_pou := hK_pou_bound e he
    have hFP_nn : 0 ≤ ‖FP‖ := norm_nonneg _
    have hraw_abs_nn : 0 ≤ |raw_val| := abs_nonneg _
    have h_raw_fp_nn : 0 ≤ |raw_val| * ‖FP‖ := mul_nonneg hraw_abs_nn hFP_nn
    have h_raw_K_nn : 0 ≤ |raw_val| * K_pou := mul_nonneg hraw_abs_nn hK_pou_nn
    have h_raw_fp_le : |raw_val| * ‖FP‖ ≤ |raw_val| * K_pou :=
      mul_le_mul_of_nonneg_left hFP_bound hraw_abs_nn
    have h_raw_fp_sq_le : (|raw_val| * ‖FP‖) ^ 2 ≤ (|raw_val| * K_pou) ^ 2 :=
      pow_le_pow_left₀ h_raw_fp_nn h_raw_fp_le 2
    have h_raw_K_sq : (|raw_val| * K_pou) ^ 2 = raw_val ^ 2 * K_pou ^ 2 := by
      rw [mul_pow]; rw [sq_abs]
    -- Bound the RHS expression.
    have hL_NtoE_sq : (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 =
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by ring
    have h_total : 2 * ‖L‖ ^ 2 + 2 * (|raw_val| * ‖FP‖) ^ 2 ≤
        2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
        2 * raw_val ^ 2 * K_pou ^ 2 := by
      have h1 : 2 * ‖L‖ ^ 2 ≤ 2 *
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
        calc 2 * ‖L‖ ^ 2 ≤ 2 * (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ * NtoE) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left hLsq (by norm_num)
            _ = 2 *
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 := by
              rw [hL_NtoE_sq]; ring
      have h2 : 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * raw_val ^ 2 * K_pou ^ 2 := by
        calc 2 * (|raw_val| * ‖FP‖) ^ 2 ≤ 2 * (|raw_val| * K_pou) ^ 2 := by
                  exact mul_le_mul_of_nonneg_left h_raw_fp_sq_le (by norm_num)
            _ = 2 * raw_val ^ 2 * K_pou ^ 2 := by
              rw [h_raw_K_sq]; ring
      linarith
    exact h_total
  -- Sum over IJ to obtain the bound.
  have h_sum_per :
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
          ∑ Idx, ∑ Jdx,
            ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              ((toEuclidean (E := E)) e)‖ ^ 2 +
        (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
          ∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 := by
    -- Distribute ρ² into the inner sum, then apply h_per_IJ termwise.
    rw [show ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) = (N * Bnorm ^ 2) *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
      rw [show (∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
            ρ ^ 2 * ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring]
    -- Bound each summand using h_per_IJ.
    have hNBsq_nn : 0 ≤ N * Bnorm ^ 2 :=
      mul_nonneg hN_nn (sq_nonneg _)
    calc N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ N * Bnorm ^ 2 *
            (∑ Idx, ∑ Jdx,
              (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
              2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNBsq_nn
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = (2 * N * Bnorm ^ 2 * NtoE ^ 2) *
            ∑ Idx, ∑ Jdx,
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                ((toEuclidean (E := E)) e)‖ ^ 2 +
          (2 * N * Bnorm ^ 2 * K_pou ^ 2) *
            ∑ Idx, ∑ Jdx,
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 := by
          have h_inner_sum : ∀ Idx,
              (∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := fun Idx => by
            rw [Finset.sum_add_distrib]
          have h_outer_sum :
              (∑ Idx, ∑ Jdx,
                (2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2 +
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2)) =
              (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) +
              (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) := by
            rw [Finset.sum_congr rfl (fun Idx _ => h_inner_sum Idx)]
            rw [Finset.sum_add_distrib]
          rw [h_outer_sum]
          rw [show (∑ Idx, ∑ Jdx,
                2 * ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    ((toEuclidean (E := E)) e)‖ ^ 2 * NtoE ^ 2) =
            2 * NtoE ^ 2 *
              ∑ Idx, ∑ Jdx,
                ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  ((toEuclidean (E := E)) e)‖ ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          rw [show (∑ Idx, ∑ Jdx,
                2 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e)) ^ 2 * K_pou ^ 2) =
            2 * K_pou ^ 2 *
              ∑ Idx, ∑ Jdx,
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e)) ^ 2 from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Idx _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Jdx _ => ?_)
            ring]
          ring
  exact le_trans h_scaled h_sum_per

/-! ## The headline: order-1 chart-target POU-weighted L² bound on the
    chart-pulled tensor representation Fréchet derivative by chart-component
    Sobolev data -/

/-- AEMeasurability of `y ↦ ofReal((raw α Idx Jdx (sym y))^2)` on the chart-
target restriction. The composition `(raw α Idx Jdx) ∘ (extChartAt I α).symm ∘
toEuclidean.symm` is continuous on `chartTargetEuclid α` (a chain of two
continuous-on-target maps and one CLE), so by `ContinuousOn.aemeasurable` it is
AEMeasurable w.r.t. `volume.restrict chartTargetEuclid α`. -/
private lemma raw_sym_sq_ofReal_aeMeasurable_restrict
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN =>
        ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  -- `raw ∘ extChartAt.symm` is ContDiffOn on (extChartAt I α).target.
  have h_raw_symm_contDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) :=
    tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_symm_cont : ContinuousOn
      (fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e')) (extChartAt I α).target :=
    h_raw_symm_contDiffOn.continuousOn
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_raw_sym_cont : ContinuousOn
      (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine h_raw_symm_cont.comp h_toEucl_symm_cont.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  -- AEMeasurability of `raw ∘ sym` from ContinuousOn.
  have h_raw_sym_ae :
      AEMeasurable
        (fun y : EuclN => tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_cont.aemeasurable h_chartTarget_meas
  -- AEMeasurability of `(raw ∘ sym)^2` via `AEMeasurable.pow_const`.
  have h_sq_ae : AEMeasurable
      (fun y : EuclN => (tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_raw_sym_ae.pow_const 2
  -- AEMeasurability of `ofReal((raw ∘ sym)^2)` via `AEMeasurable.const_arith`.
  exact ENNReal.measurable_ofReal.comp_aemeasurable h_sq_ae

/-- AEMeasurability of `y ↦ ofReal(‖fderiv tensorChartComp_IJ y‖^2)`. Since
`tensorChartComp_IJ` is `ContDiff ℝ ∞`, `fderiv tensorChartComp_IJ` is continuous,
so the entire integrand is continuous, hence measurable on the whole space (and
a fortiori AEMeasurable on any restriction). -/
private lemma fderiv_tensorChartComp_sq_ofReal_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (fun y : EuclN =>
        ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine (continuous_pow 2).measurable.comp ?_
  have h_fderiv_cont : Continuous
      (fun y : EuclN =>
        fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    have := (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx)
    exact this.continuous_fderiv (by simp)
  exact h_fderiv_cont.norm.measurable

/-- **Order-1 chart-target POU-weighted L² bound for the Fréchet derivative of
the chart-pulled tensor representation.** For a smooth closed Riemannian
manifold `(M, g)`, fixed ranks `(r, s)`, and a chart base point `α : M`, there
is a non-negative constant `K` (depending only on `(g, r, s, α)` and the model
space; independent of `T`) such that for every smooth compactly-supported
`(r, s)`-tensor section `T`, the chart-target Lebesgue integral of the
partition-of-unity-weighted squared operator norm of the Fréchet derivative
`fderiv (tensorRSChartE_section_repr r s α T.toSection ∘ (extChartAt I α).symm)`
is bounded by `K` times the sum of two pieces:

* the sum of the squared `wkpNorm 1 2`-norms of the chart-frame scalar
  components `tensorChartComp g r s T α Idx Jdx`, and
* the sum of the squared `L²`-norms (over the chart target) of the chart-pulled
  raw components `raw_IJ ∘ (extChartAt I α).symm ∘ toEuclidean.symm`.

The first term packages the gradient contribution into Sobolev-style norms via
the order-`1` chart-target Fréchet-derivative `L²`-bound. The second term, the
unweighted `L²` of the raw components, is the controlled correction coming
from the partition-of-unity multiplier. -/
theorem chartTargetPouWeightedL2NormSq_fderiv_repr_le_sum_chartComp_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖fderiv ℝ
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) 1 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                    (chartTargetEuclid (I := I) (M := M) α) ^ 2 +
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  eLpNorm
                      (fun y : EuclN =>
                        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
                      ((volume : Measure EuclN).restrict
                        (chartTargetEuclid (I := I) (M := M) α)) ^ 2) := by
  classical
  -- The chart-pulled POU Fréchet-derivative uniform bound.
  obtain ⟨K_pou, hK_pou_nn, hK_pou_bound⟩ :=
    exists_pou_symm_fderiv_uniform_bound (I := I) (M := M) α
  -- The constants from the pointwise bound.
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set C1 : ℝ := 2 * N * Bnorm ^ 2 * NtoE ^ 2 with hC1_def
  set C2 : ℝ := 2 * N * Bnorm ^ 2 * K_pou ^ 2 with hC2_def
  have hC1_nn : 0 ≤ C1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  have hC2_nn : 0 ≤ C2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    exact by norm_num
  refine ⟨C1 + C2, add_nonneg hC1_nn hC2_nn, ?_⟩
  intro T
  -- Notation for the symm composition.
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  -- LHS integrand.
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2) with hlhs_def
  -- RHS-fderiv integrand (per (Idx, Jdx)).
  set fIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)
    with hfInt_def
  -- RHS-raw integrand (per (Idx, Jdx)).
  set rIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
    with hrInt_def
  -- Step 1: Pointwise bound on chartTargetEuclid α via `pou_sq_fderiv_repr_sq_pointwise`.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fIntegrand Idx Jdx y) +
        ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rIntegrand Idx Jdx y) := by
    intro y hy
    -- Identify e := toEuclidean.symm y ∈ (extChartAt I α).target.
    set e : E := (toEuclidean (E := E)).symm y with he_def
    have he_target : e ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    -- Real-valued pointwise bound from `pou_sq_fderiv_repr_sq_pointwise`.
    have h_real := pou_sq_fderiv_repr_sq_pointwise
      (I := I) (M := M) g r s T α K_pou hK_pou_nn hK_pou_bound (e := e) he_target
    -- `toEuclidean e = y`.
    have h_toEucl_e : (toEuclidean (E := E)) e = y := by
      simp [he_def, (toEuclidean (E := E)).apply_symm_apply]
    -- Set ρ := POU(symm e) = POU(sym y).
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e) with hρ_def
    have hρ_sym : ρ = (chartAtlasPOU I M α : M → ℝ) (sym y) := by
      simp [hρ_def, hsym_def, he_def]
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    -- Set FRsq := ‖fderiv (repr ∘ symm) e‖².
    set FRsq : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 with hFRsq_def
    have hFRsq_nn : 0 ≤ FRsq := sq_nonneg _
    -- Set the fderiv tensorChartComp sum (RHS first piece without C1).
    set fSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)‖ ^ 2 with hfSum_def
    have hfSum_nn : 0 ≤ fSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    -- Set the raw sum (RHS second piece without C2).
    set rSum : ℝ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 with hrSum_def
    have hrSum_nn : 0 ≤ rSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    -- Real bound: ρ² · FRsq ≤ C1 · fSum + C2 · rSum.
    have h_real' : ρ ^ 2 * FRsq ≤ C1 * fSum + C2 * rSum := by
      simpa [ρ, FRsq, fSum, rSum, C1, C2, Bnorm, NtoE, N, hC1_def, hC2_def,
        hBnorm_def, hNtoE_def, hN_def] using h_real
    -- Lift to ENNReal.
    have h_LHS_eq : lhsIntegrand y =
        ENNReal.ofReal (ρ ^ 2 * FRsq) := by
      simp only [hlhs_def, ← hρ_sym, FRsq]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_LHS_eq]
    -- Bound `ofReal(ρ² · FRsq) ≤ ofReal(C1 · fSum + C2 · rSum)`.
    refine le_trans (ENNReal.ofReal_le_ofReal h_real') ?_
    -- Decompose `ofReal(C1 · fSum + C2 · rSum) = ofReal(C1 · fSum) + ofReal(C2 · rSum)`.
    have h_C1fSum_nn : 0 ≤ C1 * fSum := mul_nonneg hC1_nn hfSum_nn
    have h_C2rSum_nn : 0 ≤ C2 * rSum := mul_nonneg hC2_nn hrSum_nn
    rw [ENNReal.ofReal_add h_C1fSum_nn h_C2rSum_nn]
    -- Decompose each `ofReal(Ci · sum_i) = ofReal Ci · ofReal sum_i`.
    rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn]
    -- Decompose `ofReal fSum = ∑∑ fIntegrand Idx Jdx y`.
    have h_fSum_eq :
        ENNReal.ofReal fSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y := by
      simp only [hfSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            ((toEuclidean (E := E)) e)‖ ^ 2) =
        fIntegrand Idx Jdx y
      rw [h_toEucl_e]
    -- Decompose `ofReal rSum = ∑∑ rIntegrand Idx Jdx y`.
    have h_rSum_eq :
        ENNReal.ofReal rSum =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y := by
      simp only [hrSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg (fun Jdx _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun Jdx _ => sq_nonneg _)]
    rw [h_fSum_eq, h_rSum_eq]
  -- Step 2: integrate the pointwise bound.
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y) +
              ENNReal.ofReal C2 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rIntegrand Idx Jdx y))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  -- Step 3: Pull constants out and distribute sums.
  -- Measurability of fIntegrand (everywhere on EuclN).
  have h_fInt_meas : ∀ Idx Jdx, Measurable (fIntegrand Idx Jdx) := fun Idx Jdx =>
    fderiv_tensorChartComp_sq_ofReal_measurable
      (I := I) (M := M) g r s T α Idx Jdx
  -- AEMeasurability of rIntegrand on the restricted measure.
  have h_rInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (rIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    have := raw_sym_sq_ofReal_aeMeasurable_restrict
      (I := I) (M := M) g r s T α Idx Jdx
    simpa [hrInt_def, hsym_def] using this
  -- AEMeasurability of the inner sum of fIntegrand.
  have h_fInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    have : Measurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y) := by
      refine Finset.measurable_sum _ (fun Idx _ => ?_)
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx
    exact this.aemeasurable
  -- AEMeasurability of the inner sum of rIntegrand.
  have h_rInt_sum_aeMeas :
      AEMeasurable
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    -- Finset sum of AEMeasurables is AEMeasurable.
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    have h_funsum_ae : AEMeasurable
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      Finset.aemeasurable_sum _ (fun Idx _ => h_inner_ae Idx)
    have h_eq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) =
        (fun y : EuclN =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
      funext y
      simp [Finset.sum_apply]
    rwa [h_eq] at h_funsum_ae
  -- Distribute the integral over the binary sum.
  have h_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y) +
            ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y))
          ∂(volume : Measure EuclN) =
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal C1 *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN)) +
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal C2 *
                (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                  ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                    rIntegrand Idx Jdx y)
              ∂(volume : Measure EuclN)) := by
    -- Use lintegral_add_left' for the left summand AEMeasurable.
    have h_lhs_aeMeas : AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      exact AEMeasurable.const_mul h_fInt_sum_aeMeas _
    exact lintegral_add_left' h_lhs_aeMeas _
  rw [h_split] at h_int_mono
  -- Pull the constants out of each lintegral.
  have h_const_C1 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C1 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C1 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                fIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h_const_C2 :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal C2 *
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C2 *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                rIntegrand Idx Jdx y)
            ∂(volume : Measure EuclN) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [h_const_C1, h_const_C2] at h_int_mono
  -- Distribute integral over the inner double sum, for f and r.
  have h_dist_f :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              fIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [lintegral_finset_sum _ (fun Idx _ => by
      refine Finset.measurable_sum _ (fun Jdx _ => ?_)
      exact h_fInt_meas Idx Jdx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum _ (fun Jdx _ => h_fInt_meas Idx Jdx)
  have h_dist_r :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    -- The inner-sum-of-Jdx is AEMeasurable (rewriting via `Finset.sum_apply`).
    have h_inner_ae : ∀ Idx,
        AEMeasurable
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
      have h_eq : (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            fun y : EuclN => rIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rIntegrand Idx Jdx y) := by
        funext y
        simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    rw [lintegral_finset_sum' _ (fun Idx _ => h_inner_ae Idx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum' _ (fun Jdx _ => h_rInt_aeMeas Idx Jdx)
  rw [h_dist_f, h_dist_r] at h_int_mono
  -- Step 4: Bound each `∫⁻ fIntegrand` by `(wkpNorm 1 2 tensorChartComp)^2`.
  have h_per_f : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          fIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        wkpNorm (d := Module.finrank ℝ E) 1 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    intro Idx Jdx
    -- ∫⁻ ofReal(‖fderiv ...‖²) ∂vol.restrict = (eLpNorm (‖fderiv ...‖) 2 (vol.restrict))²
    have h_chartTarget_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    have h_tcc_smooth : ContDiff ℝ ∞
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_compactSupport : HasCompactSupport
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
      tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
    have h_tcc_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ⊆ chartTargetEuclid (I := I) (M := M) α :=
      tensorChartComp_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) g r s T α Idx Jdx
    -- The bridge.
    have h_brg :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_fderiv_eLpNorm_le_wkpNorm_one_two
        (d := Module.finrank ℝ E) h_chartTarget_open
        (h_tcc_smooth.of_le (by simp)) h_tcc_compactSupport h_tcc_supp
    -- Identify ∫⁻ fIntegrand = (eLpNorm (‖fderiv ...‖) 2 (vol.restrict))².
    have h_lp_sq :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              fIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
      have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
        (fun y : EuclN =>
          ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      rw [h_eLp_sq]
    -- (eLpNorm)² ≤ (wkpNorm 1 2)².
    have h_sq_le :
        (eLpNorm
            (fun y : EuclN =>
              ‖fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          wkpNorm (d := Module.finrank ℝ E) 1 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
      exact pow_le_pow_left' h_brg 2
    rw [← h_lp_sq]; exact h_sq_le
  -- Step 5: Bound each `∫⁻ rIntegrand` by `(eLpNorm raw_sym 2 (vol.restrict))^2`.
  have h_per_r : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rIntegrand Idx Jdx y ∂(volume : Measure EuclN) =
        eLpNorm
            (fun y : EuclN =>
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    have h_eLp_sq := sq_eLpNorm_two_eq_lintegral_ofReal_sq
      (fun y : EuclN =>
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
    -- `∫⁻ y, ofReal((raw(sym y))^2) ∂vol.restrict = ∫⁻ y in chartTarget α, rIntegrand`.
    have h_eq_lhs :
        ∫⁻ y,
            ENNReal.ofReal
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            rIntegrand Idx Jdx y ∂(volume : Measure EuclN) := rfl
    rw [h_eq_lhs] at h_eLp_sq
    exact h_eLp_sq.symm
  -- Combine.
  -- h_int_mono : ∫⁻ lhsIntegrand ≤ ofReal C1 · (∑∑ ∫⁻ fIntegrand) + ofReal C2 · (∑∑ ∫⁻ rIntegrand)
  -- We bound the f-side and rewrite the r-side.
  -- Goal: ∫⁻ lhsIntegrand ≤ ofReal (C1 + C2) * (∑∑ (wkpNorm)² + ∑∑ (eLpNorm raw_sym)²)
  -- Strategy: bound ∫⁻ fIntegrand by wkpNorm² (h_per_f); replace ∫⁻ rIntegrand by eLpNorm² (h_per_r).
  -- Then ofReal C1 · X1 + ofReal C2 · X2 ≤ ofReal (C1 + C2) · (X1 + X2) since X1, X2 ≥ 0 and Ci ≥ 0.
  refine h_int_mono.trans ?_
  -- Replace ∫⁻ fIntegrand by wkpNorm² (using ≤ from h_per_f).
  have h_f_total_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) ≤
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) 1 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) ^ 2 := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact h_per_f Idx Jdx
  have h_r_total_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rIntegrand Idx Jdx y ∂(volume : Measure EuclN)) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
                (fun y : EuclN =>
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact h_per_r Idx Jdx
  -- The combined bound.
  set Xf : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) 1 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ^ 2 with hXf_def
  set Xr : ℝ≥0∞ := ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      eLpNorm
          (fun y : EuclN =>
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 with hXr_def
  -- After substitution: bound is `ofReal C1 · Xf' + ofReal C2 · Xr'` where
  -- Xf' = ∑∑ ∫⁻ fIntegrand ≤ Xf and Xr' = ∑∑ ∫⁻ rIntegrand = Xr.
  -- We want this ≤ ofReal(C1 + C2) · (Xf + Xr).
  -- Bound via: ofReal C1 · Xf' ≤ ofReal C1 · Xf ≤ ofReal(C1+C2) · Xf;
  -- and ofReal C2 · Xr' = ofReal C2 · Xr ≤ ofReal(C1+C2) · Xr.
  have h_C1_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hC2_nn)
  have h_C2_le : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2) :=
    ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hC1_nn)
  calc
    ENNReal.ofReal C1 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
      ENNReal.ofReal C2 *
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  rIntegrand Idx Jdx y ∂(volume : Measure EuclN))
        ≤ ENNReal.ofReal C1 * Xf + ENNReal.ofReal C2 * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_right h_f_total_le (ENNReal.ofReal C1)
          · exact le_of_eq (by rw [h_r_total_eq])
      _ ≤ ENNReal.ofReal (C1 + C2) * Xf + ENNReal.ofReal (C1 + C2) * Xr := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_left h_C1_le Xf
          · exact mul_le_mul_left h_C2_le Xr
      _ = ENNReal.ofReal (C1 + C2) * (Xf + Xr) := by
          rw [mul_add]

end Connection
end Integral
end DifferentialGeometry

end
