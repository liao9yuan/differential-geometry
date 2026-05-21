import DifferentialGeometry.Integral.Connection.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Integral.Connection.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartTargetSqBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartL2PouBridge
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.FderivToWkpNormBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedFderivToWkpNormBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound

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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

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

/-! ## Order-2 Leibniz inequality (scalar product) -/

/-- **Order-2 Leibniz inequality.** For two real-valued functions
`f, g : E → ℝ` that are `ContDiffAt ℝ 2` at a point `x`, the iterated
Fréchet derivative satisfies the triangle bound
`|f x| · ‖∇²g x‖ ≤ ‖∇²(f·g) x‖ + |g x| · ‖∇²f x‖ + 2 · ‖∇f x‖ · ‖∇g x‖`.

The proof works at the `fderiv (fderiv ·)` level, using the order-1
Leibniz equality (`fderiv_fun_mul`) twice. We unfold both `iteratedFDeriv 2 f`
and `iteratedFDeriv 2 (fg)` to `fderiv (fderiv ·)` via
`iteratedFDeriv_two_apply`. -/
private lemma scalar_iteratedFDeriv_two_mul_norm_le
    (f g : E → ℝ) {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    |f x| * ‖iteratedFDeriv ℝ 2 g x‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x‖ +
        |g x| * ‖iteratedFDeriv ℝ 2 f x‖ +
        2 * ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  classical
  -- Differentiability information for `f` and `g` near `x`.
  have h1_ne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h2_ne : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hf_diffAt : DifferentiableAt ℝ f x :=
    hf.differentiableAt h2_ne
  have hg_diffAt : DifferentiableAt ℝ g x :=
    hg.differentiableAt h2_ne
  have h2_ne_top : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have hf_diff_at_eventually : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually h2_ne_top] with y hy
    exact hy.differentiableAt h2_ne
  have hg_diff_at_eventually : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually h2_ne_top] with y hy
    exact hy.differentiableAt h2_ne
  -- ContDiffAt 1 for `fderiv f`, `fderiv g`.
  have hf_fderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
    have := hf.fderiv_right
      (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    simpa using this
  have hg_fderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ g) x := by
    have := hg.fderiv_right
      (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    simpa using this
  have hf_fderiv_diffAt : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hf_fderiv_contDiffAt.differentiableAt h1_ne
  have hg_fderiv_diffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
    hg_fderiv_contDiffAt.differentiableAt h1_ne
  -- Step 1: order-1 Leibniz: fderiv (fg) y = f y · fderiv g y + g y · fderiv f y.
  -- Step 2: Apply fderiv again to the RHS. Using `fderiv_fun_smul` (scalar smul of fderiv):
  -- fderiv (fun y => f y • fderiv g y) x = f x • fderiv (fderiv g) x +
  --     (fderiv f x).smulRight (fderiv g x)
  -- fderiv (fun y => g y • fderiv f y) x = g x • fderiv (fderiv f) x +
  --     (fderiv g x).smulRight (fderiv f x)
  -- Step 3: Sum and rearrange.
  -- This step is non-trivial because we need to show `fderiv (fderiv (fg)) x =
  -- fderiv (fun y => f y · fderiv g y + g y · fderiv f y) x`.
  -- We use `Filter.EventuallyEq.fderiv_eq`.
  have h_fderiv_fg_eventually :
      (fun y : E => fderiv ℝ (fun z : E => f z * g z) y) =ᶠ[nhds x]
        (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hf_diff_at_eventually, hg_diff_at_eventually]
      with y hfy hgy
    exact fderiv_fun_mul hfy hgy
  -- Show `fderiv (fderiv (fg)) x = fderiv (fun y => f y • fderiv g y + g y • fderiv f y) x`.
  have h_step3 :
      fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x =
        fderiv ℝ (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) x :=
    h_fderiv_fg_eventually.fderiv_eq
  -- Apply fderiv_add to split.
  have h_split :
      fderiv ℝ (fun y : E => f y • fderiv ℝ g y + g y • fderiv ℝ f y) x =
        fderiv ℝ (fun y : E => f y • fderiv ℝ g y) x +
        fderiv ℝ (fun y : E => g y • fderiv ℝ f y) x := by
    apply fderiv_fun_add
    · exact hf_diffAt.smul hg_fderiv_diffAt
    · exact hg_diffAt.smul hf_fderiv_diffAt
  -- Apply fderiv_fun_smul to each.
  have h_f_smul : fderiv ℝ (fun y : E => f y • fderiv ℝ g y) x =
      f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x) :=
    fderiv_fun_smul hf_diffAt hg_fderiv_diffAt
  have h_g_smul : fderiv ℝ (fun y : E => g y • fderiv ℝ f y) x =
      g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x) :=
    fderiv_fun_smul hg_diffAt hf_fderiv_diffAt
  -- Combine.
  have h_total :
      fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x =
        f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x) +
        (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
    rw [h_step3, h_split, h_f_smul, h_g_smul]
  -- We want: |f x| * ‖iteratedFDeriv 2 g x‖ ≤ ‖iteratedFDeriv 2 (fg) x‖ +
  --                                            |g x| * ‖iteratedFDeriv 2 f x‖ +
  --                                            2 * ‖∇f x‖ * ‖∇g x‖
  -- Use norm relation: ‖iteratedFDeriv 2 F x‖ = ‖fderiv (fderiv F) x‖ for any F.
  -- (Same proof as `norm_fderiv_fderiv_eq_iteratedFDeriv_two` from
  --  `IntrinsicPieceFderivBound`.)
  have h_norm_iter_f : ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  have h_norm_iter_g : ‖iteratedFDeriv ℝ 2 g x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ g) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  have h_norm_iter_fg :
      ‖iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x‖ =
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ := by
    rw [show ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y : E => f y * g y)) x‖ from
      (norm_iteratedFDeriv_one (𝕜 := ℝ)
        (fderiv ℝ (fun y : E => f y * g y)) (x := x)).symm]
    rw [norm_iteratedFDeriv_fderiv]
  -- Triangle inequality on `fderiv (fderiv (fg)) x = f x • ∇²g + smulRight + g x • ∇²f + smulRight`.
  -- Goal: |f x| * ‖∇²g x‖ ≤ ‖∇²(fg) x‖ + |g x| * ‖∇²f x‖ + 2 * ‖∇f x‖ * ‖∇g x‖.
  -- Equivalent: ‖f x • ∇²g x‖ ≤ ‖∇²(fg) x‖ + ‖g x • ∇²f x‖ + 2 * ‖∇f x‖ * ‖∇g x‖.
  -- Rearrangement: f x • ∇²g x = ∇²(fg) x - g x • ∇²f x - 2 * smulRight terms (norm-wise).
  have h_iso :
      f x • fderiv ℝ (fderiv ℝ g) x =
        fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x -
        ((fderiv ℝ f x).smulRight (fderiv ℝ g x) +
         (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) := by
    rw [h_total]
    abel
  -- Norms.
  have h_fx_smul_norm :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ =
        |f x| * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_gx_smul_norm :
      ‖g x • fderiv ℝ (fderiv ℝ f) x‖ =
        |g x| * ‖fderiv ℝ (fderiv ℝ f) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_smulRight_norm_fg :
      ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ =
        ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
  have h_smulRight_norm_gf :
      ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ =
        ‖fderiv ℝ g x‖ * ‖fderiv ℝ f x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
  -- Triangle:
  have h_tri :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ +
          ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x) +
           (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))‖ := by
    rw [h_iso]
    exact norm_sub_le _ _
  -- Expand the second norm with successive triangle inequalities.
  have h_tri2 :
      ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x) +
       (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))‖ ≤
        ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ +
          ‖g x • fderiv ℝ (fderiv ℝ f) x +
           (fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ :=
    norm_add_le _ _
  have h_tri3 :
      ‖g x • fderiv ℝ (fderiv ℝ f) x +
       (fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ ≤
        ‖g x • fderiv ℝ (fderiv ℝ f) x‖ +
          ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ :=
    norm_add_le _ _
  -- Combine triangle inequalities.
  have h_combined :
      ‖f x • fderiv ℝ (fderiv ℝ g) x‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun y : E => f y * g y)) x‖ +
          (‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ +
           (‖g x • fderiv ℝ (fderiv ℝ f) x‖ +
            ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖)) :=
    h_tri.trans
      (add_le_add le_rfl
        (h_tri2.trans (add_le_add le_rfl h_tri3)))
  -- Substitute norm identities.
  rw [h_fx_smul_norm] at h_combined
  rw [h_gx_smul_norm] at h_combined
  rw [h_smulRight_norm_fg] at h_combined
  rw [h_smulRight_norm_gf] at h_combined
  -- LHS: |f x| * ‖∇²g x‖ = |f x| * ‖fderiv (fderiv g) x‖ via h_norm_iter_g
  -- RHS: ‖∇²(fg) x‖ + 2 * ‖∇f‖ * ‖∇g‖ + |g x| * ‖∇²f x‖
  -- Replace ‖fderiv (fderiv ...) x‖ with ‖iteratedFDeriv 2 ... x‖.
  rw [← h_norm_iter_g, ← h_norm_iter_f, ← h_norm_iter_fg] at h_combined
  -- h_combined: |f x| * ‖∇²g‖ ≤ ‖∇²(fg)‖ + (‖∇f‖·‖∇g‖ + (|g x|·‖∇²f‖ + ‖∇g‖·‖∇f‖))
  -- Goal: |f x| * ‖∇²g‖ ≤ ‖∇²(fg)‖ + |g x| * ‖∇²f‖ + 2 * ‖∇f‖ * ‖∇g‖
  nlinarith [h_combined,
    mul_nonneg (norm_nonneg (fderiv ℝ f x)) (norm_nonneg (fderiv ℝ g x)),
    mul_nonneg (norm_nonneg (fderiv ℝ g x)) (norm_nonneg (fderiv ℝ f x))]

/-! ## Order-2 squared basis decomposition at chart-target points -/

/-- **Order-2 squared basis decomposition.** Pointwise (squared) bound: at any
chart-target point, the squared operator norm of `iteratedFDeriv 2 (repr T ∘
symm) e` is bounded by `N · Bnorm²` times the finite double sum of
`‖iteratedFDeriv 2 (raw_IJ ∘ symm) e‖²`. -/
lemma iteratedFDeriv_two_repr_opNormSq_le_sum_iteratedFDeriv_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {e : E}
    (he : e ∈ (extChartAt I α).target) :
    ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        e‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
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
  -- Apply existing per-component iteratedFDeriv 2 decomposition at `extChartAt I α b = e`.
  have h_lin :=
    iteratedFDeriv_two_tensorRepr_opNorm_le_sum_iteratedFDeriv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart
  rw [he_eq] at h_lin
  -- Bound the RHS of `h_lin` by `(Σ_IJ ‖∇²(raw_IJ ∘ symm) e‖) · Bnorm`.
  have h_rhs_le :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ *
              ‖tensorChartBasisElement (E := E) r s Idx Jdx‖) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact mul_le_mul_of_nonneg_left (hbasis_le Idx Jdx) (norm_nonneg _)
  have h_norm_le : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖) * Bnorm := h_lin.trans h_rhs_le
  -- Rewrite double sum as sum over `V`.
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_sum_pair_eq :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)]
  -- Square both sides.
  have h_sum_nn :
      0 ≤ (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      ‖iteratedFDeriv ℝ 2
        (tensorChartComponentRaw (I := I) (M := M) g r s T α
          p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_le' : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ≤
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm := by
    rw [← h_sum_pair_eq] at h_norm_le; exact h_norm_le
  have h_norm_sq : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ((∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 := by
    have := mul_le_mul h_norm_le' h_norm_le' (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  -- Cauchy-Schwarz on the sum.
  have hCS :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    exact hbase
  -- Combine.
  have h_combined : ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 *
        ∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    have h_sq_eq : ((∑ p ∈ V,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖) * Bnorm) ^ 2 = (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    calc ‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) e‖ ^ 2
        ≤ (∑ p ∈ V,
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                p.1 p.2 ∘ (extChartAt I α).symm) e‖) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * (∑ p ∈ V,
              ‖iteratedFDeriv ℝ 2
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) * Bnorm ^ 2 := h_mul
      _ = (V.card : ℝ) * Bnorm ^ 2 *
            ∑ p ∈ V,
              ‖iteratedFDeriv ℝ 2
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2 := by ring
  -- Rewrite the pair sum back as nested double-sum.
  have h_pair_to_nest :
      (∑ p ∈ V,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            p.1 p.2 ∘ (extChartAt I α).symm) e‖ ^ 2)]
  rw [h_pair_to_nest] at h_combined
  exact h_combined

/-! ## Uniform bound on the chart-pulled POU iteratedFDeriv 2 on E -/

/-- The chart-pulled POU iterated-Fréchet-derivative (order 2) is uniformly
bounded on `(extChartAt I α).target` (and globally on `E`, since the
chart-pushed POU `chartPouEucl` is `ContDiff ℝ ∞` with compact support).

We use the chain-rule decomposition `iteratedFDeriv 2 (chartPouEucl ∘ toEucl)
e = (composition with toEucl twice)` to transfer the bound from EuclN to E. -/
private lemma exists_chartPouEucl_iteratedFDeriv_two_uniform_bound (α : M) :
    ∃ K_pou2 : ℝ, 0 ≤ K_pou2 ∧
      ∀ y : EuclN, ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y‖ ≤ K_pou2 := by
  classical
  have hCD : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have hHCS : HasCompactSupport (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_hasCompactSupport (I := I) (M := M) α
  -- The order-2 iteratedFDeriv is continuous and has compact support.
  have h_iter_cont : Continuous (fun y : EuclN =>
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y) := by
    have hm : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact hCD.continuous_iteratedFDeriv hm
  have h_iter_compactSupport : HasCompactSupport (fun y : EuclN =>
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) y) :=
    hHCS.iteratedFDeriv 2
  -- A continuous compactly-supported function on a metric space has bounded norm.
  obtain ⟨K_raw, hK_bound⟩ := h_iter_cont.bounded_above_of_compact_support
    h_iter_compactSupport
  refine ⟨max K_raw 0, le_max_right _ _, ?_⟩
  intro y
  exact le_trans (hK_bound y) (le_max_left _ _)

/-- The chart-pulled POU function (composed with `(extChartAt I α).symm`) has a
uniformly bounded `iteratedFDeriv 2` on `(extChartAt I α).target`.

The proof: the function equals `chartPouEucl ∘ toEucl` on the chart target
(via `chartPouEucl_toEuclidean_eq_pou_symm`). Since `chartPouEucl` is `ContDiff
ℝ ∞` and `toEucl` is a continuous linear equivalence (in particular `ContDiff
ℝ ∞`), the chain rule gives `‖iteratedFDeriv 2 (chartPouEucl ∘ toEucl) e‖ ≤
‖iteratedFDeriv 2 chartPouEucl (toEucl e)‖ · NtoE²` (since `toEucl` is linear,
so `iteratedFDeriv toEucl` is `toEucl` itself at order 1 and 0 at higher
orders). We use `ContinuousLinearMap.iteratedFDeriv_comp_left` (composition
with a CLM) to derive this bound. -/
private lemma exists_pou_symm_iteratedFDeriv_two_uniform_bound (α : M) :
    ∃ K_pou2 : ℝ, 0 ≤ K_pou2 ∧
      ∀ e ∈ (extChartAt I α).target,
        ‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ≤ K_pou2 := by
  classical
  -- Use the EuclN-side bound and the chain rule via `chartPouEucl ∘ toEucl`.
  obtain ⟨K_eucl, hK_nn, hK_bound⟩ :=
    exists_chartPouEucl_iteratedFDeriv_two_uniform_bound (I := I) (M := M) α
  -- The continuous linear coercion of the equiv.
  let toEucl_CLM : E →L[ℝ] EuclN := (toEuclidean (E := E) : E →L[ℝ] EuclN)
  set NtoE : ℝ := ‖toEucl_CLM‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  have hCD_pou : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  refine ⟨K_eucl * NtoE ^ 2, mul_nonneg hK_nn (sq_nonneg _), ?_⟩
  intro e he
  -- Show: ‖∇² (POU ∘ symm) e‖ = ‖∇² (chartPouEucl ∘ toEucl) e‖ ≤ NtoE² · K_eucl.
  have h_eventuallyEq :
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) =ᶠ[nhds e]
        (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) :=
    pou_symm_eventuallyEq_chartPouEucl_toEuclidean (I := I) (M := M) α he
  have h_iter_eq : iteratedFDeriv ℝ 2
      (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e')) e =
        iteratedFDeriv ℝ 2
          (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) e :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ h_eventuallyEq 2).eq_of_nhds
  rw [h_iter_eq]
  -- Use ContinuousLinearMap.iteratedFDeriv_comp_right.
  have h_comp_eq :
      iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α ∘ toEucl_CLM) e =
        ContinuousMultilinearMap.compContinuousLinearMap
          (iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) (toEucl_CLM e))
          (fun _ : Fin 2 => toEucl_CLM) :=
    toEucl_CLM.iteratedFDeriv_comp_right hCD_pou e h2_le
  have h_fn_eq : (fun e' : E => chartPouEucl (I := I) (M := M) α (toEucl_CLM e')) =
      chartPouEucl (I := I) (M := M) α ∘ toEucl_CLM := rfl
  rw [h_fn_eq, h_comp_eq]
  -- Apply `norm_compContinuousLinearMap_le`.
  have h_norm_bound :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (g := iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α) (toEucl_CLM e))
      (fun _ : Fin 2 => toEucl_CLM)
  -- h_norm_bound: ‖compContinuousLinearMap g f‖ ≤ ‖g‖ * ∏_i ‖f_i‖ = ‖g‖ * ‖toEucl_CLM‖^2.
  have h_prod_eq : ∏ _i : Fin 2, ‖toEucl_CLM‖ = ‖toEucl_CLM‖ ^ 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_prod_eq] at h_norm_bound
  -- Bound the right-hand side.
  refine h_norm_bound.trans ?_
  have hK_eval : ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α)
      (toEucl_CLM e)‖ ≤ K_eucl := hK_bound _
  calc ‖iteratedFDeriv ℝ 2 (chartPouEucl (I := I) (M := M) α)
            (toEucl_CLM e)‖ * NtoE ^ 2
      ≤ K_eucl * NtoE ^ 2 :=
        mul_le_mul_of_nonneg_right hK_eval (sq_nonneg _)

/-! ## Order-2 pointwise scaled bound -/

/-- **Order-2 pointwise scaled bound.** On the chart target, the POU²-scaled
squared chart-pulled-repr iterated-Fréchet-derivative norm (order 2) is bounded
by `C1` times the sum of squared `iteratedFDeriv 2` norms of `(POU·raw_IJ) ∘
symm`, plus `C2` times the sum of squared raw component values at
`(extChartAt I α).symm e`, plus `C3` times the sum of `‖fderiv POU∘symm‖² ·
‖fderiv raw_IJ∘symm‖²`. -/
lemma pou_sq_iteratedFDeriv_two_repr_sq_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (K_pou2 : ℝ) (_hK_pou2_nn : 0 ≤ K_pou2)
    (hK_pou2_bound : ∀ e ∈ (extChartAt I α).target,
      ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou2)
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm e)) ^ 2) *
      (‖iteratedFDeriv ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2) ≤
      (3 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ 2
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e') *
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e')) e‖ ^ 2 +
        (3 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2 * K_pou2 ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 +
        (12 * ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
          (tensorChartBasisNormConstant (E := E) r s) ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖fderiv ℝ
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e')) e‖ ^ 2 *
              ‖fderiv ℝ
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) e‖ ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e)
  -- ρ ≥ 0.
  have hρ_nn : 0 ≤ ρ := by
    have := (chartAtlasPOU I M).nonneg α ((extChartAt I α).symm e); exact this
  have hρ_abs : |ρ| = ρ := abs_of_nonneg hρ_nn
  -- Use squared basis decomposition.
  have h_sq := iteratedFDeriv_two_repr_opNormSq_le_sum_iteratedFDeriv_components_sq
    (I := I) (M := M) g r s T α (e := e) he
  -- Multiply both sides by ρ².
  have h_scaled : ρ ^ 2 *
      ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ρ ^ 2 * (N * Bnorm ^ 2 *
        ∑ Idx, ∑ Jdx,
          ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
  -- Bound ρ² · ‖∇²(raw_IJ ∘ symm) e‖² per IJ.
  have h_per_IJ : ∀ Idx Jdx,
      ρ ^ 2 * ‖iteratedFDeriv ℝ 2
        (tensorChartComponentRaw (I := I) (M := M) g r s T α
          Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
        3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2 := by
    intro Idx Jdx
    -- ContDiffAt 2 of (POU ∘ symm) at e: from chartAtlasPOU_symm_contDiffOn_target.
    have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
    have hP_cd : ContDiffAt ℝ 2 (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e := by
      have hcd_on := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
      have hcd_at_inf : ContDiffAt ℝ ∞ (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e :=
        (hcd_on _ he).contDiffAt (h_open.mem_nhds he)
      have h2_le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact (WithTop.coe_le_coe.mpr h1 : _)
      exact hcd_at_inf.of_le (by exact_mod_cast h2_le_inf)
    -- ContDiffAt 2 of (raw_IJ ∘ symm) at e.
    have hR_cd : ContDiffAt ℝ 2 (fun e' : E =>
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e')) e := by
      have hcd_on := tensorChartComponentRaw_symm_contDiffOn_target
        (I := I) (M := M) g r s T α Idx Jdx
      have hcd_at_inf : ContDiffAt ℝ ∞ (fun e' : E =>
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e :=
        (hcd_on _ he).contDiffAt (h_open.mem_nhds he)
      have h2_le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
        exact (WithTop.coe_le_coe.mpr h1 : _)
      exact hcd_at_inf.of_le (by exact_mod_cast h2_le_inf)
    -- Apply scalar order-2 Leibniz inequality.
    set P := fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e') with hP_def
    set R := fun e' : E => tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e') with hR_def
    have h_leibniz := scalar_iteratedFDeriv_two_mul_norm_le P R hP_cd hR_cd
    -- P e = ρ, |R e| = |raw_IJ at symm e|.
    have hPe : P e = ρ := rfl
    set raw_val : ℝ := R e with hraw_def
    have hraw_eq : raw_val = tensorChartComponentRaw (I := I) (M := M) g r s T α
        Idx Jdx ((extChartAt I α).symm e) := rfl
    rw [hPe] at h_leibniz
    rw [hρ_abs] at h_leibniz
    -- Square (a+b+c)² ≤ 3(a²+b²+c²).
    have h_sq_ineq : (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 ≤
        3 * (‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ ^ 2 +
            (|raw_val| * ‖iteratedFDeriv ℝ 2 P e‖) ^ 2 +
            (2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖) ^ 2) := by
      set a : ℝ := ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖
      set b : ℝ := |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖
      set c : ℝ := 2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have hc_nn : 0 ≤ c := by positivity
      have hρR_nn : 0 ≤ ρ * ‖iteratedFDeriv ℝ 2 R e‖ :=
        mul_nonneg hρ_nn (norm_nonneg _)
      have h_lhs_le : ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤ a + b + c := by
        change ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ +
            |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖ + 2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖
        -- h_leibniz: |P e| · ‖iter² R‖ ≤ ‖iter²(PR)‖ + |R e| · ‖iter² P‖ + 2 · ‖∇P‖ · ‖∇R‖
        -- with P e = ρ, R e = raw_val.
        have h_temp : ρ * ‖iteratedFDeriv ℝ 2 R e‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ +
            |raw_val| * ‖iteratedFDeriv ℝ 2 P e‖ +
            2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖ := h_leibniz
        exact h_temp
      have h_sq_le : (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 ≤ (a + b + c) ^ 2 :=
        pow_le_pow_left₀ hρR_nn h_lhs_le 2
      have h_expand : (a + b + c) ^ 2 ≤ 3 * (a^2 + b^2 + c^2) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a+b-c)]
      exact le_trans h_sq_le h_expand
    -- ρ² · ‖∇²R‖² = (ρ · ‖∇²R‖)².
    have hρ_R_sq : ρ ^ 2 * ‖iteratedFDeriv ℝ 2 R e‖ ^ 2 =
        (ρ * ‖iteratedFDeriv ℝ 2 R e‖) ^ 2 := by ring
    -- The goal uses `tensorChartComponentRaw ... ∘ symm` while R is
    -- `fun e' => tensorChartComponentRaw ... (symm e')`. They are defeq.
    change ρ ^ 2 * ‖iteratedFDeriv ℝ 2 R e‖ ^ 2 ≤ _
    rw [hρ_R_sq]
    refine h_sq_ineq.trans ?_
    -- Expand RHS components.
    have h_a_sq : ‖iteratedFDeriv ℝ 2 (fun y : E => P y * R y) e‖ ^ 2 =
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_b_sq : (|raw_val| * ‖iteratedFDeriv ℝ 2 P e‖) ^ 2 =
        raw_val ^ 2 * ‖iteratedFDeriv ℝ 2 P e‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    have h_c_sq : (2 * ‖fderiv ℝ P e‖ * ‖fderiv ℝ R e‖) ^ 2 =
        4 * ‖fderiv ℝ P e‖ ^ 2 * ‖fderiv ℝ R e‖ ^ 2 := by ring
    rw [h_a_sq, h_b_sq, h_c_sq]
    -- Identify the components.
    have h_P_def : ‖iteratedFDeriv ℝ 2 P e‖ ^ 2 =
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_P_fderiv_def : ‖fderiv ℝ P e‖ ^ 2 =
        ‖fderiv ℝ
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 := by rfl
    have h_R_fderiv_def : ‖fderiv ℝ R e‖ ^ 2 =
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := by rfl
    have h_raw_def : raw_val ^ 2 = (tensorChartComponentRaw (I := I) (M := M)
        g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 := by rw [hraw_eq]
    rw [h_P_def, h_P_fderiv_def, h_R_fderiv_def, h_raw_def]
    linarith
  -- Sum over IJ to obtain the bound.
  refine le_trans h_scaled ?_
  -- Distribute ρ² into the inner sum, then apply h_per_IJ termwise.
  have h_distrib : ρ ^ 2 * (N * Bnorm ^ 2 *
      ∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
      (N * Bnorm ^ 2) *
        ∑ Idx, ∑ Jdx,
          ρ ^ 2 * ‖iteratedFDeriv ℝ 2
            (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 := by
    rw [show (∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2) =
          ρ ^ 2 * ∑ Idx, ∑ Jdx,
            ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
                Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]]
    ring
  rw [h_distrib]
  -- Bound each summand using h_per_IJ.
  have hNBsq_nn : 0 ≤ N * Bnorm ^ 2 :=
    mul_nonneg hN_nn (sq_nonneg _)
  -- Apply h_per_IJ termwise then expand the sum.
  have h_sum_bound :
      ∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    exact h_per_IJ Idx Jdx
  -- Apply the multiplication by `N · Bnorm²`.
  have h_mul_le : (N * Bnorm ^ 2) *
      ∑ Idx, ∑ Jdx,
        ρ ^ 2 * ‖iteratedFDeriv ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α
            Idx Jdx ∘ (extChartAt I α).symm) e‖ ^ 2 ≤
      (N * Bnorm ^ 2) * ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_sum_bound hNBsq_nn
  refine le_trans h_mul_le ?_
  -- Expand the sums and apply uniform K_pou2.
  -- We must show:
  --   N·B² · Σ Σ (3·a_IJ² + 3·raw²·c² + 12·b²·d²) ≤
  --     3N·B² · Σ Σ a_IJ² + 3N·B²·K_pou² · Σ Σ raw² + 12N·B² · Σ Σ b²·d²
  -- where c = ‖∇²P‖ ≤ K_pou², b = ‖∇P‖, d = ‖∇R_IJ‖, a_IJ = ‖∇²(PR_IJ)‖.
  -- Use ‖∇²P‖² ≤ K_pou² (so K_pou ^ 2 is the upper bound). Strategy: write
  -- c² = ‖∇²P‖² and use c² ≤ K_pou² to bound by the wanted form.
  have hP_fderiv2_bound :
      ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 ≤ K_pou2 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hK_pou2_bound e he) 2
  -- Now distribute.
  have h_sum_split :
      ∑ Idx, ∑ Jdx,
        (3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2 +
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 +
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) =
      (∑ Idx, ∑ Jdx,
        3 * ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
      (∑ Idx, ∑ Jdx,
        3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e)) ^ 2 *
          ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2) +
      (∑ Idx, ∑ Jdx,
        12 * ‖fderiv ℝ
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2 *
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
    -- Distribute the sum over the binary + operations.
    rw [Finset.sum_congr rfl (fun Idx _ =>
      show (∑ Jdx, _) = _ from by rw [Finset.sum_add_distrib, Finset.sum_add_distrib])]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [h_sum_split]
  -- Pull constants out and apply K_pou2 bound on second term.
  have h_factor3_a : (∑ Idx, ∑ Jdx,
      3 * ‖iteratedFDeriv ℝ 2
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e')) e‖ ^ 2) =
      3 * ∑ Idx, ∑ Jdx,
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e')) e‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [Finset.mul_sum]
  have h_factor3_b_inner : (∑ Idx, ∑ Jdx,
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 *
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2) ≤
      3 * K_pou2 ^ 2 * ∑ Idx, ∑ Jdx,
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 := by
    -- Use hP_fderiv2_bound to replace ‖∇²P‖² ≤ K_pou²; raw² is ≥ 0.
    rw [show (3 : ℝ) * K_pou2 ^ 2 = 3 * K_pou2 ^ 2 from rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    have hsq_raw_nn : 0 ≤ (tensorChartComponentRaw (I := I) (M := M)
        g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 := sq_nonneg _
    have hbound :
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 *
        ‖iteratedFDeriv ℝ 2
          (fun e' : E =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e')) e‖ ^ 2 ≤
      3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e)) ^ 2 * K_pou2 ^ 2 := by
      have h3raw_nn : 0 ≤ 3 * (tensorChartComponentRaw (I := I) (M := M)
          g r s T α Idx Jdx ((extChartAt I α).symm e)) ^ 2 :=
        mul_nonneg (by norm_num) hsq_raw_nn
      exact mul_le_mul_of_nonneg_left hP_fderiv2_bound h3raw_nn
    linarith [hbound]
  have h_factor3_c : (∑ Idx, ∑ Jdx,
      12 * ‖fderiv ℝ
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2) =
      12 * ∑ Idx, ∑ Jdx,
        ‖fderiv ℝ
            (fun e' : E =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
        ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    ring
  rw [h_factor3_a, h_factor3_c]
  -- Combine everything.
  -- Goal: N·B² · (3·A + B + 12·C) ≤ 3N·B² · A + 3N·B²·K² · raw_sum + 12N·B² · C
  -- where A = Σ ∇²(PR)², B ≤ 3K²·raw_sum, raw_sum = Σ raw², C = Σ ∇P²·∇R²
  set A := ∑ Idx, ∑ Jdx,
    ‖iteratedFDeriv ℝ 2
      (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e') *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e')) e‖ ^ 2 with hA_def
  set B_old := ∑ Idx, ∑ Jdx,
    3 * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e)) ^ 2 *
      ‖iteratedFDeriv ℝ 2
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ^ 2 with hB_def
  set RawSum := ∑ Idx, ∑ Jdx,
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
      ((extChartAt I α).symm e)) ^ 2 with hRawSum_def
  set C := ∑ Idx, ∑ Jdx,
    ‖fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ^ 2 *
    ‖fderiv ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e‖ ^ 2 with hC_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hB_nn : 0 ≤ B_old := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)))
  have hRawSum_nn : 0 ≤ RawSum := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hB_le : B_old ≤ 3 * K_pou2 ^ 2 * RawSum := h_factor3_b_inner
  -- Bound: N·B² · (3A + B_old + 12C) ≤ 3N·B²·A + N·B² · (3·K²·raw_sum) + 12N·B²·C
  -- = 3·N·B²·A + 3·N·B²·K²·raw_sum + 12·N·B²·C
  -- We want: ≤ 3·N·B²·A + 3·N·B²·K²·raw_sum + 12·N·B²·C
  have hgoal : (N * Bnorm ^ 2) * (3 * A + B_old + 12 * C) ≤
      (3 * N * Bnorm ^ 2) * A +
      (3 * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum +
      (12 * N * Bnorm ^ 2) * C := by
    have h1 : (N * Bnorm ^ 2) * (3 * A + B_old + 12 * C) =
        (N * Bnorm ^ 2) * (3 * A) + (N * Bnorm ^ 2) * B_old +
        (N * Bnorm ^ 2) * (12 * C) := by ring
    rw [h1]
    have hnb_nn : 0 ≤ N * Bnorm ^ 2 := hNBsq_nn
    have h_b_mul : (N * Bnorm ^ 2) * B_old ≤
        (N * Bnorm ^ 2) * (3 * K_pou2 ^ 2 * RawSum) :=
      mul_le_mul_of_nonneg_left hB_le hnb_nn
    have h_eq1 : (N * Bnorm ^ 2) * (3 * A) = (3 * N * Bnorm ^ 2) * A := by ring
    have h_eq2 : (N * Bnorm ^ 2) * (3 * K_pou2 ^ 2 * RawSum) =
        (3 * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum := by ring
    have h_eq3 : (N * Bnorm ^ 2) * (12 * C) = (12 * N * Bnorm ^ 2) * C := by ring
    linarith [h_b_mul]
  -- Final manipulation. We need to match.
  have h_final :
    (N * Bnorm ^ 2) *
      ((3 : ℝ) * (∑ Idx, ∑ Jdx,
            ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
        (∑ Idx, ∑ Jdx,
          (3 : ℝ) * (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e)) ^ 2 *
            ‖iteratedFDeriv ℝ 2
              (fun e' : E =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e')) e‖ ^ 2) +
        (12 : ℝ) * (∑ Idx, ∑ Jdx,
            ‖fderiv ℝ
                (fun e' : E =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e')) e‖ ^ 2 *
            ‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) e‖ ^ 2)) ≤
      ((3 : ℝ) * N * Bnorm ^ 2) * A +
      ((3 : ℝ) * N * Bnorm ^ 2 * K_pou2 ^ 2) * RawSum +
      ((12 : ℝ) * N * Bnorm ^ 2) * C := by
    -- The LHS is (N·B²)·(3·A + B_old + 12·C).
    -- We reshape the LHS using `ring_nf` etc.
    convert hgoal using 2
  -- Match the goal. The goal RHS is exactly the final h_final RHS structure.
  exact h_final

/-! ## Order-2 headline: chart-target POU-weighted L² of iteratedFDeriv 2 of the
    chart-pulled tensor representation by chart-component Sobolev data -/

/-- **Order-2 chart-target POU-weighted L² bound for the second iterated
Fréchet derivative of the chart-pulled tensor representation by chart-component
data.** For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`,
and a chart base point `α : M`, there is a non-negative constant `K` (depending
only on `(g, r, s, α)` and the model space; independent of `T`) such that for
every smooth compactly-supported `(r, s)`-tensor section `T`, the chart-target
Lebesgue integral of the partition-of-unity-weighted squared operator norm of
`iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α T.toSection ∘
(extChartAt I α).symm)` is bounded by `K` times the sum of three pieces:

* the sum of the chart-target Lebesgue integrals of the squared iterated
  Fréchet-derivative norms of the POU-weighted chart-frame scalar components
  (this piece is the principal contribution; it is bounded above by the
  squared `wkpNorm 2 2` of `tensorChartComp_IJ` modulo a constant factor that
  is absorbed into `K`),
* the sum of the squared `L²`-norms over the chart target of the chart-pulled
  Fréchet derivatives of the raw scalar components (first Leibniz correction),
* the sum of the squared `L²`-norms over the chart target of the chart-pulled
  raw scalar components themselves (second Leibniz correction).

The two correction terms are deferred to cross-chart aggregation. The proof
combines the order-2 squared basis decomposition, the order-2 scalar Leibniz
inequality, the uniform bound on the chart-pulled POU iteratedFDeriv 2, and
the `(a+b+c)² ≤ 3(a²+b²+c²)` algebraic inequality, integrated against the
chart-target restriction measure. -/
theorem chartTargetPouWeightedL2NormSq_iteratedFDeriv_two_repr_le_sum_chartComp_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        (‖iteratedFDeriv ℝ 2
                          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                              ((extChartAt I α).symm e') *
                            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                              ((extChartAt I α).symm e'))
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                      ∂(volume : Measure EuclN)) +
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        (‖fderiv ℝ
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
                      ∂(volume : Measure EuclN)) +
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                      ENNReal.ofReal
                        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
                      ∂(volume : Measure EuclN))) := by
  classical
  -- The chart-pulled POU iteratedFDeriv-2 and fderiv uniform bounds.
  obtain ⟨K_pou2, hK_pou2_nn, hK_pou2_bound⟩ :=
    exists_pou_symm_iteratedFDeriv_two_uniform_bound (I := I) (M := M) α
  obtain ⟨K_pou1, hK_pou1_nn, hK_pou1_bound⟩ :=
    exists_pou_symm_fderiv_uniform_bound (I := I) (M := M) α
  -- The constants from the pointwise bound.
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set N : ℝ := ((Finset.univ : Finset
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set C1 : ℝ := 3 * N * Bnorm ^ 2 with hC1_def
  set C2 : ℝ := 3 * N * Bnorm ^ 2 * K_pou2 ^ 2 with hC2_def
  set C3 : ℝ := 12 * N * Bnorm ^ 2 * K_pou1 ^ 2 with hC3_def
  have hC1_nn : 0 ≤ C1 := by
    refine mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _); norm_num
  have hC2_nn : 0 ≤ C2 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    norm_num
  have hC3_nn : 0 ≤ C3 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _)) (sq_nonneg _)
    norm_num
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2) with hlhs_def
  set wIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y)‖ ^ 2)
  set fIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        (‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
  set rIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx (sym y)) ^ 2)
  -- Pointwise bound.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
        ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
        ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y) := by
    intro y hy
    set e : E := (toEuclidean (E := E)).symm y with he_def
    have he_target : e ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    -- Real bound from `pou_sq_iteratedFDeriv_two_repr_sq_pointwise`.
    have h_real := pou_sq_iteratedFDeriv_two_repr_sq_pointwise
      (I := I) (M := M) g r s T α K_pou2 hK_pou2_nn hK_pou2_bound (e := e) he_target
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm e) with hρ_def
    have hρ_sym : ρ = (chartAtlasPOU I M α : M → ℝ) (sym y) := by
      simp [hρ_def, hsym_def, he_def]
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set FRsq : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e‖ ^ 2 with hFRsq_def
    set wSum : ℝ := ∑ Idx, ∑ Jdx,
      ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e‖ ^ 2 with hwSum_def
    have hwSum_nn : 0 ≤ wSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set rSum : ℝ := ∑ Idx, ∑ Jdx,
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm e)) ^ 2 with hrSum_def
    have hrSum_nn : 0 ≤ rSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    set fSum_raw : ℝ := ∑ Idx, ∑ Jdx,
      ‖fderiv ℝ
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e')) e‖ ^ 2 *
      ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 with hfSum_raw_def
    have hfSum_raw_nn : 0 ≤ fSum_raw :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    -- Real bound: ρ²·FRsq ≤ C1·wSum + C2·rSum + (12·N·B²)·fSum_raw.
    have h_real' : ρ ^ 2 * FRsq ≤ C1 * wSum + C2 * rSum + (12 * N * Bnorm ^ 2) * fSum_raw := by
      simpa [ρ, FRsq, wSum, rSum, fSum_raw, C1, C2, Bnorm, N,
        hC1_def, hC2_def, hBnorm_def, hN_def] using h_real
    -- Bound `‖∇POU‖²·‖∇raw‖² ≤ K_pou1²·‖∇raw‖²` using the uniform fderiv bound.
    have hK_pou1_e : ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ≤ K_pou1 := hK_pou1_bound e he_target
    have hK_pou1_e_sq : ‖fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e‖ ^ 2 ≤ K_pou1 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hK_pou1_e 2
    have h_fSum_raw_le : fSum_raw ≤ K_pou1 ^ 2 *
        (∑ Idx, ∑ Jdx,
          ‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) e‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun Idx _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun Jdx _ => ?_)
      have hsq_raw_nn : 0 ≤ ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hK_pou1_e_sq hsq_raw_nn
    set fdSum : ℝ := ∑ Idx, ∑ Jdx,
      ‖fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) e‖ ^ 2 with hfdSum_def
    have hfdSum_nn : 0 ≤ fdSum :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_NB12_nn : 0 ≤ 12 * N * Bnorm ^ 2 := by
      refine mul_nonneg (mul_nonneg ?_ hN_nn) (sq_nonneg _); norm_num
    have h_real'' : ρ ^ 2 * FRsq ≤ C1 * wSum + C2 * rSum + C3 * fdSum := by
      have h := h_real'
      have h_step : (12 * N * Bnorm ^ 2) * fSum_raw ≤
          (12 * N * Bnorm ^ 2) * (K_pou1 ^ 2 * fdSum) :=
        mul_le_mul_of_nonneg_left h_fSum_raw_le h_NB12_nn
      have h_eq : (12 * N * Bnorm ^ 2) * (K_pou1 ^ 2 * fdSum) = C3 * fdSum := by
        rw [hC3_def]; ring
      linarith
    -- Lift to ENNReal.
    have h_LHS_eq : lhsIntegrand y = ENNReal.ofReal (ρ ^ 2 * FRsq) := by
      simp only [hlhs_def, ← hρ_sym, FRsq]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_LHS_eq]
    have h_C1w_nn : 0 ≤ C1 * wSum := mul_nonneg hC1_nn hwSum_nn
    have h_C2r_nn : 0 ≤ C2 * rSum := mul_nonneg hC2_nn hrSum_nn
    have h_C3fd_nn : 0 ≤ C3 * fdSum := mul_nonneg hC3_nn hfdSum_nn
    have h_step1 :
        ENNReal.ofReal (ρ ^ 2 * FRsq) ≤
          ENNReal.ofReal (C1 * wSum + C2 * rSum + C3 * fdSum) :=
      ENNReal.ofReal_le_ofReal h_real''
    refine le_trans h_step1 ?_
    rw [ENNReal.ofReal_add (add_nonneg h_C1w_nn h_C2r_nn) h_C3fd_nn]
    rw [ENNReal.ofReal_add h_C1w_nn h_C2r_nn]
    rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn,
      ENNReal.ofReal_mul hC3_nn]
    -- Decompose the sums.
    have h_wSum_eq :
        ENNReal.ofReal wSum =
          ∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y := by
      simp only [hwSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have h_rSum_eq :
        ENNReal.ofReal rSum =
          ∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y := by
      simp only [hrSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have h_fdSum_eq :
        ENNReal.ofReal fdSum =
          ∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y := by
      simp only [hfdSum_def]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [h_wSum_eq, h_rSum_eq, h_fdSum_eq]
  -- Integrate the pointwise bound.
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  -- AEMeasurability (continuous on chart target, plus toEucl.symm continuous).
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  -- Get ContinuousOn of each integrand on chartTargetEuclid α.
  -- (POU·raw)∘symm is ContDiffOn ∞ on (extChartAt α).target, so its iteratedFDeriv 2 is continuous.
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_2le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have h_wInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (wIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    -- iteratedFDeriv 2 of (POU·raw)∘symm is continuous on (extChartAt α).target.
    have hP_cd := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
    have hR_cd := tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
    have h_prod_cd : ContDiffOn ℝ ∞
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) (extChartAt I α).target :=
      hP_cd.mul hR_cd
    have h_iter_contOn : ContinuousOn
        (fun e' : E => iteratedFDeriv ℝ 2
          (fun e'' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e'') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'')) e') (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (fun e'' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e'') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'')) e' :=
        ((h_prod_cd _ he').contDiffAt (h_open.mem_nhds he')).of_le
          (by exact_mod_cast h_2le_inf)
      exact (h_cd_at.continuousAt_iteratedFDeriv (k := 2) le_rfl).continuousWithinAt
    have h_iter_sym_contOn : ContinuousOn
        (fun y : EuclN => iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_iter_contOn.comp h_toEucl_symm_cont.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_norm_sym_ae : AEMeasurable
        (fun y : EuclN => ‖iteratedFDeriv ℝ 2
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
              ((extChartAt I α).symm e') *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y)‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_iter_sym_contOn.norm.aemeasurable h_chartTarget_meas
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h_norm_sym_ae.pow_const 2)
  have h_fInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (fIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    -- fderiv (raw_IJ ∘ symm) is continuous on (extChartAt α).target.
    have hR_cd := tensorChartComponentRaw_symm_contDiffOn_target
      (I := I) (M := M) g r s T α Idx Jdx
    have h_fderiv_contOn : ContinuousOn
        (fun e' : E => fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e') (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) e' :=
        ((hR_cd _ he').contDiffAt (h_open.mem_nhds he')).of_le
          (by exact_mod_cast h_2le_inf)
      exact (h_cd_at.continuousAt_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).continuousWithinAt
    have h_fderiv_sym_contOn : ContinuousOn
        (fun y : EuclN => fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_fderiv_contOn.comp h_toEucl_symm_cont.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_norm_sym_ae : AEMeasurable
        (fun y : EuclN => ‖fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_fderiv_sym_contOn.norm.aemeasurable h_chartTarget_meas
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h_norm_sym_ae.pow_const 2)
  have h_rInt_aeMeas : ∀ Idx Jdx,
      AEMeasurable (rIntegrand Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro Idx Jdx
    exact raw_sym_sq_ofReal_aeMeasurable_restrict
      (I := I) (M := M) g r s T α Idx Jdx
  -- Inner sum AEMeasurability — for w, r, f.
  have h_innersum_aeMeas : ∀ (f : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞),
      (∀ Idx Jdx, AEMeasurable (f Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) →
      AEMeasurable (fun y : EuclN => ∑ Idx, ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro f hf
    have h_inner_ae : ∀ Idx, AEMeasurable
        (fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx, fun y : EuclN => f Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => hf Idx Jdx)
      have h_eq : (∑ Jdx, fun y : EuclN => f Idx Jdx y) =
          (fun y : EuclN => ∑ Jdx, f Idx Jdx y) := by
        funext y; simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    have h_funsum_ae : AEMeasurable
        (∑ Idx, fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      Finset.aemeasurable_sum _ (fun Idx _ => h_inner_ae Idx)
    have h_eq : (∑ Idx, fun y : EuclN => ∑ Jdx, f Idx Jdx y) =
        (fun y : EuclN => ∑ Idx, ∑ Jdx, f Idx Jdx y) := by
      funext y; simp [Finset.sum_apply]
    rwa [h_eq] at h_funsum_ae
  have h_wSum_aeMeas := h_innersum_aeMeas wIntegrand h_wInt_aeMeas
  have h_fSum_aeMeas := h_innersum_aeMeas fIntegrand h_fInt_aeMeas
  have h_rSum_aeMeas := h_innersum_aeMeas rIntegrand h_rInt_aeMeas
  -- Integrate the pointwise bound.
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
              ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
              ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y))
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  -- Split + pull constants out.
  have h_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
            ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) +
            ENNReal.ofReal C3 * (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y))
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal C1 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) +
        ENNReal.ofReal C2 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) +
        ENNReal.ofReal C3 *
          (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              (∑ Idx, ∑ Jdx, fIntegrand Idx Jdx y) ∂(volume : Measure EuclN)) := by
    have h_C1_ae : AEMeasurable
        (fun y : EuclN => ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      AEMeasurable.const_mul h_wSum_aeMeas _
    have h_C2_ae : AEMeasurable
        (fun y : EuclN => ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      AEMeasurable.const_mul h_rSum_aeMeas _
    have h_C12_ae : AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal C1 * (∑ Idx, ∑ Jdx, wIntegrand Idx Jdx y) +
          ENNReal.ofReal C2 * (∑ Idx, ∑ Jdx, rIntegrand Idx Jdx y))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_C1_ae.add h_C2_ae
    rw [lintegral_add_left' h_C12_ae]
    rw [lintegral_add_left' h_C1_ae]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [h_split] at h_int_mono
  -- Distribute each integral over the double sums.
  have h_dist : ∀ (f : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞),
      (∀ Idx Jdx, AEMeasurable (f Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) →
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx, ∑ Jdx, f Idx Jdx y) ∂(volume : Measure EuclN) =
        ∑ Idx, ∑ Jdx,
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              f Idx Jdx y ∂(volume : Measure EuclN) := by
    intro f hf
    have h_inner_ae : ∀ Idx, AEMeasurable
        (fun y : EuclN => ∑ Jdx, f Idx Jdx y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      intro Idx
      have h_funsum_ae : AEMeasurable
          (∑ Jdx, fun y : EuclN => f Idx Jdx y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        Finset.aemeasurable_sum _ (fun Jdx _ => hf Idx Jdx)
      have h_eq : (∑ Jdx, fun y : EuclN => f Idx Jdx y) =
          (fun y : EuclN => ∑ Jdx, f Idx Jdx y) := by
        funext y; simp [Finset.sum_apply]
      rwa [h_eq] at h_funsum_ae
    rw [lintegral_finset_sum' _ (fun Idx _ => h_inner_ae Idx)]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact lintegral_finset_sum' _ (fun Jdx _ => hf Idx Jdx)
  rw [h_dist wIntegrand h_wInt_aeMeas,
      h_dist rIntegrand h_rInt_aeMeas,
      h_dist fIntegrand h_fInt_aeMeas] at h_int_mono
  -- Now `h_int_mono` has form: LHS ≤ C1·Σ∫w + C2·Σ∫r + C3·Σ∫f.
  -- We need: LHS ≤ ofReal(C1+C2+C3) · (Σ∫w + Σ∫f + Σ∫r).
  -- Strategy: each Ci ≤ ofReal(C1+C2+C3); and the inner sums are non-negative.
  refine h_int_mono.trans ?_
  set Sw : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        wIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  set Sr : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        rIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  set Sf : ℝ≥0∞ := ∑ Idx, ∑ Jdx,
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        fIntegrand Idx Jdx y ∂(volume : Measure EuclN)
  -- Each Ci ≤ C1 + C2 + C3.
  have hC1_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC2_le : ENNReal.ofReal C2 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC3_le : ENNReal.ofReal C3 ≤ ENNReal.ofReal (C1 + C2 + C3) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal C1 * Sw + ENNReal.ofReal C2 * Sr + ENNReal.ofReal C3 * Sf
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Sw +
        ENNReal.ofReal (C1 + C2 + C3) * Sr +
        ENNReal.ofReal (C1 + C2 + C3) * Sf := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_left hC1_le Sw
        · exact mul_le_mul_left hC2_le Sr
        · exact mul_le_mul_left hC3_le Sf
    _ = ENNReal.ofReal (C1 + C2 + C3) * (Sw + Sf + Sr) := by ring
    _ = ENNReal.ofReal (C1 + C2 + C3) *
          ((∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  wIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
            (∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  fIntegrand Idx Jdx y ∂(volume : Measure EuclN)) +
            (∑ Idx, ∑ Jdx,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  rIntegrand Idx Jdx y ∂(volume : Measure EuclN))) := by rfl


/-! ## Cross-chart consistency helpers

Under the chart-source-consistent atlas predicate
`HasChartSourceConsistentChartAt`, the canonical chart selector `chartAt H`
is constant on each chart source. This forces, for any two chart base points
`α, β : M` whose chart sources both contain a point `b`, that the charts
themselves coincide as `OpenPartialHomeomorph`s — hence the chart targets
coincide as sets in `E`, the inverse charts coincide as functions, and
chart-frame trivialised scalars (such as `tensorChartComponentRaw α IJ`) take
the same value on the shared point. -/

/-- Under `HasChartSourceConsistentChartAt`, the chart at any point of the
chart source `α` equals the chart at `α`. (A restatement of
`HasChartSourceConsistentChartAt` with the orientation handy for the
chart-frame comparison below.) -/
private lemma chartAt_eq_of_mem_source
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (α : M) (b : M) (hb : b ∈ (chartAt H α).source) :
    chartAt H b = chartAt H α :=
  h_atlas_strong α b hb

/-- Under `HasChartSourceConsistentChartAt`, if `b` belongs to both
`chartAt H α`-source and `chartAt H β`-source, then the two charts coincide. -/
private lemma chartAt_eq_of_shared_source
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (α β : M) (b : M)
    (hb_α : b ∈ (chartAt H α).source) (hb_β : b ∈ (chartAt H β).source) :
    chartAt H α = chartAt H β := by
  have h1 : chartAt H b = chartAt H α :=
    chartAt_eq_of_mem_source (M := M) h_atlas_strong α b hb_α
  have h2 : chartAt H b = chartAt H β :=
    chartAt_eq_of_mem_source (M := M) h_atlas_strong β b hb_β
  exact h1.symm.trans h2

/-- Under `HasChartSourceConsistentChartAt`, if `chartAt H α = chartAt H β`, the
extended charts coincide. -/
private lemma extChartAt_eq_of_chartAt_eq
    {α β : M} (h_eq : chartAt H α = chartAt H β) :
    extChartAt I α = extChartAt I β := by
  simp only [extChartAt, h_eq]

/-- Under `HasChartSourceConsistentChartAt`, if `chartAt H α = chartAt H β`, then
`chartTargetEuclid α = chartTargetEuclid β`. -/
private lemma chartTargetEuclid_eq_of_chartAt_eq
    {α β : M} (h_eq : chartAt H α = chartAt H β) :
    chartTargetEuclid (I := I) (M := M) α =
      chartTargetEuclid (I := I) (M := M) β := by
  unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
  rw [extChartAt_eq_of_chartAt_eq (I := I) (M := M) h_eq]

/-- Under `HasChartSourceConsistentChartAt`, for `b ∈ (chart α).source`, the
chart trivialisation at `α` agrees with the trivialisation at `b`. (At chart
identification level this is automatic from `chartAt H b = chartAt H α`.) -/
private lemma extChartAt_eq_at_source_point
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    {α b : M} (hb : b ∈ (chartAt H α).source) :
    extChartAt I b = extChartAt I α :=
  extChartAt_eq_of_chartAt_eq (I := I) (M := M)
    (chartAt_eq_of_mem_source (M := M) h_atlas_strong α b hb)

/-! ## Algebraic helper: sum of non-negative squares is bounded by the square
of the sum (in `ℝ≥0∞`). -/

/-- For a finite family of non-negative extended reals, `∑ a_i² ≤ (∑ a_i)²`. -/
private lemma sum_sq_le_sq_sum_finset
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ i ∈ s, (f i) ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  set S : ℝ≥0∞ := ∑ i ∈ s, f i with hS_def
  have hS_sq : S ^ 2 = S * S := sq S
  have hineq : ∀ i ∈ s, (f i) ^ 2 ≤ f i * S := by
    intro i hi
    have hi_le_S : f i ≤ S := Finset.single_le_sum
      (f := f) (fun _ _ => zero_le _) hi
    have hsq_eq : (f i) ^ 2 = f i * f i := sq (f i)
    rw [hsq_eq]
    exact mul_le_mul_of_nonneg_left hi_le_S (zero_le _)
  calc ∑ i ∈ s, (f i) ^ 2
      ≤ ∑ i ∈ s, f i * S := Finset.sum_le_sum hineq
    _ = (∑ i ∈ s, f i) * S := by rw [← Finset.sum_mul]
    _ = S * S := by rw [← hS_def]
    _ = S ^ 2 := hS_sq.symm

/-- For a countable family of non-negative extended reals, `∑' a_i² ≤ (∑' a_i)²`. -/
private lemma tsum_sq_le_sq_tsum_ennreal
    {ι : Type*} (f : ι → ℝ≥0∞) :
    ∑' i, (f i) ^ 2 ≤ (∑' i, f i) ^ 2 := by
  classical
  set S : ℝ≥0∞ := ∑' i, f i with hS_def
  -- Each `f i ≤ S` (`Σ' = sup of finite partial sums`).
  have h_le : ∀ i, f i ≤ S := fun i => ENNReal.le_tsum i
  -- So `(f i)^2 ≤ f i · S`.
  have h_pointwise : ∀ i, (f i) ^ 2 ≤ f i * S := by
    intro i
    have hsq : (f i) ^ 2 = f i * f i := sq (f i)
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (h_le i) (zero_le _)
  -- Sum both sides.
  calc ∑' i, (f i) ^ 2
      ≤ ∑' i, f i * S :=
        ENNReal.tsum_le_tsum h_pointwise
    _ = (∑' i, f i) * S := by rw [ENNReal.tsum_mul_right]
    _ = S * S := by rw [← hS_def]
    _ = S ^ 2 := (sq S).symm

/-! ## Bounding the per-chart sum by `wtwokTwoNorm² g 1 T` -/

/-- For each `α` in a finset of charts and each component multi-index `(Idx, Jdx)`,
the square of `wkpNorm 0 2 (tensorChartComp α Idx Jdx)` (on the chart target) is
bounded by `(wtwokTwoNorm g 1 T)^2`. This is the per-chart contribution to the
overall `wtwokTwoNorm` square bound. -/
private lemma wkpNorm_zero_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 0 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  -- Step 1: `wkpNorm 0 2 ≤ wkpNorm 2 2`.
  have h01 : wkpNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have : (0 : ℕ) ≤ 2 * 1 := by norm_num
    simpa using wkpNorm_mono_order (d := Module.finrank ℝ E)
      this
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)
  -- Step 2: bound per-chart term `wkpNorm 2 2 of tensorChartComp α IJ` by `wtwokTwoNorm`.
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    -- The per-α-IJ term is ≤ the tsum (since each term is ≥ 0).
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    -- Now bound the per-α finite double sum by the tsum.
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  have h_combined : wkpNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := h01.trans h_α
  exact pow_le_pow_left' h_combined 2

/-- The finset sum `∑_α ∑_IJ (wkpNorm 0 2 of tensorChartComp α IJ)²` over
`chartAtlasPOU_finset` is bounded by `|finset| · cardIdx · cardJdx ·
(wtwokTwoNorm g 1 T)²`. -/
private lemma finset_sum_wkpNorm_zero_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  -- Apply the per-α, per-IJ bound and count terms.
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  have h_bound : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        ∀ Jdx ∈ (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W := by
    intro α _ Idx _ Jdx _
    exact wkpNorm_zero_sq_le_wtwokTwoNorm_sq (I := I) (M := M)
      g r s T α Idx Jdx
  -- Bound the triple sum by |finset| · cardIdx · cardJdx · W.
  have h_step1 :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (wkpNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
    refine Finset.sum_le_sum (fun α hα => ?_)
    refine Finset.sum_le_sum (fun Idx hIdx => ?_)
    refine Finset.sum_le_sum (fun Jdx hJdx => ?_)
    exact h_bound α hα Idx hIdx Jdx hJdx
  refine h_step1.trans ?_
  -- Sum of constants: |finset| · cardIdx · cardJdx · W.
  have h_inner_eq : ∀ _α : M,
      (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          (((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              W) := by
    intro _α
    have h_inner :
        (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
        ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            W := by
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h_inner, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr (rfl :
    chartAtlasPOU_finset (I := I) (M := M) = chartAtlasPOU_finset (I := I) (M := M))
    (fun α _ => h_inner_eq α)]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        (((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          (((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              W)) =
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
          ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
            W from by ring]

/-! ## Monotonicity-based per-chart bound for `wkpNorm 1 2` and `wkpNorm 2 2` -/

/-- Same as `wkpNorm_zero_sq_le_wtwokTwoNorm_sq` but for `wkpNorm 1 2`. -/
private lemma wkpNorm_one_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 1 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  have h12 : wkpNorm (d := Module.finrank ℝ E) 1 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have : (1 : ℕ) ≤ 2 * 1 := by norm_num
    exact wkpNorm_mono_order (d := Module.finrank ℝ E) this _ _
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  exact pow_le_pow_left' (h12.trans h_α) 2

/-- Same as `wkpNorm_zero_sq_le_wtwokTwoNorm_sq` but for `wkpNorm 2 2`. -/
private lemma wkpNorm_two_sq_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
      (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  have h_eq : (2 : ℕ) = 2 * 1 := by norm_num
  rw [h_eq]
  -- Now bound `wkpNorm (2*1) 2` per-chart by `wtwokTwoNorm g 1 T`.
  have h_α : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g 1 T := by
    unfold wtwokTwoNorm
    have h_term : wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
      calc wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Jdx' : Fin s → Fin (Module.finrank ℝ E) =>
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
                  (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
        _ ≤ ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                  (chartTargetEuclid (I := I) (M := M) α) :=
            Finset.single_le_sum
              (f := fun Idx' : Fin r → Fin (Module.finrank ℝ E) =>
                ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) (2 * 1) 2
                    (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
                    (chartTargetEuclid (I := I) (M := M) α))
              (fun _ _ => zero_le _) (Finset.mem_univ Idx)
    refine h_term.trans ?_
    exact ENNReal.le_tsum α
  exact pow_le_pow_left' h_α 2

/-! ## Cross-chart pointwise identity for the tangent trivialisation -/

/-- When `chartAt H α = chartAt H β`, the tangent trivialisations at `α` and `β`
applied at `b` coincide. -/
private lemma tangent_continuousLinearMapAt_eq_of_chartAt_eq
    {α β : M} (h_chart : chartAt H α = chartAt H β) (b : M)
    (hb_α : b ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b := by
  classical
  have hb_β : b ∈ (chartAt H β).source := by rw [← h_chart]; exact hb_α
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := I) hb_α]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) (I := I) hb_β]
  congr 1
  exact Subtype.ext h_chart

/-! ## Cross-chart equality of `tensorChartComponentRaw`

Under `HasChartSourceConsistentChartAt`, for `b` lying in both `(chartAt H α).source`
and `(chartAt H β).source`, the raw chart-frame scalar components at `α` and `β`
agree pointwise. The proof routes through the `(r, s)`-tensor bundle locality
identity which says that the forward trivialization at any base point, evaluated
at a point in its own chart source, reduces to the identity (up to the bundle ↔
model identification). -/

/-- Under `HasChartSourceConsistentChartAt`, the raw chart-frame scalar component
is constant across chart base points whose chart source contains the evaluation
point. -/
private lemma tensorChartComponentRaw_eq_of_shared_source
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β b : M)
    (hb_α : b ∈ (chartAt H α).source) (hb_β : b ∈ (chartAt H β).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b =
      tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b := by
  classical
  -- It suffices to show the forward trivialization projections at α and β agree.
  have h_proj_eq :
      tensorTrivProj (I := I) (M := M) g r s T α b =
        tensorTrivProj (I := I) (M := M) g r s T β b := by
    -- Both equal the bundle fiber element viewed in the model.
    -- Use `tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality`:
    -- For α: `chartAt H b = chartAt H α` (from chart-source consistency at α).
    have h_chart_α : chartAt H b = chartAt H α := h_atlas_strong α b hb_α
    have h_chart_β : chartAt H b = chartAt H β := h_atlas_strong β b hb_β
    -- Unfold `tensorTrivProj` and apply the locality identity.
    apply ContinuousLinearMap.ext
    intro D
    -- LHS: `(triv at α).continuousLinearMapAt ℝ b (T.toSection b) D`.
    have h_α := tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
      (I := I) (M := M) (r := r) (s := s) (b₀ := α) (b := b) h_chart_α hb_α
      (T.toSection b) D
    have h_β := tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
      (I := I) (M := M) (r := r) (s := s) (b₀ := β) (b := b) h_chart_β hb_β
      (T.toSection b) D
    -- Both `h_α` and `h_β` say the LHS equals the model-form of `T.toSection b D`.
    -- So they're equal.
    change (tensorTrivProj (I := I) (M := M) g r s T α b) D =
        (tensorTrivProj (I := I) (M := M) g r s T β b) D
    unfold tensorTrivProj
    rw [h_α, h_β]
  rw [tensorChartComponentRaw_def, tensorChartComponentRaw_def, h_proj_eq]

/-- Under `HasChartSourceConsistentChartAt`, for `b ∈ (chartAt H α).source`, the
raw chart-frame scalar component at `α` equals the partition-of-unity weighted
sum over all chart base points in `chartAtlasPOU_finset` of the POU-weighted raw
chart-frame scalar components at the other charts. -/
private lemma tensorChartComponentRaw_eq_sum_pou
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_α : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b =
      ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b := by
  classical
  -- For each β in the finset: if POU(β b) > 0, then b ∈ chart source β, and by
  -- chart-source-consistency, raw α IJ b = raw β IJ b. So
  -- POU(β b) · raw α IJ b = POU(β b) · raw β IJ b = tensorChartComponentPou β IJ b.
  -- If POU(β b) = 0, then both sides are 0.
  -- Hence sum = (Σ_β POU(β b)) · raw α IJ b = 1 · raw α IJ b = raw α IJ b.
  have h_sum_one : (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartAtlasPOU I M β : M → ℝ) b) = 1 := by
    have h_fs : (chartAtlasPOU I M).finsupport b ⊆
        chartAtlasPOU_finset (I := I) (M := M) := by
      intro x hx
      rw [SmoothPartitionOfUnity.mem_finsupport] at hx
      rw [chartAtlasPOU_finset_mem]
      exact ⟨b, hx⟩
    exact (chartAtlasPOU I M).sum_finsupport' b (Set.mem_univ b) h_fs
  -- Multiply each side by raw α IJ b.
  have h_lhs_eq : tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b =
      (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M β : M → ℝ) b) *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
    rw [h_sum_one]; ring
  rw [h_lhs_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  -- Show `POU(β b) · raw α IJ b = tensorChartComponentPou β IJ b`.
  -- Case 1: POU(β b) = 0.
  by_cases h_pos : (chartAtlasPOU I M β : M → ℝ) b = 0
  · rw [h_pos, zero_mul]
    unfold tensorChartComponentPou
    rw [h_pos, zero_mul]
  · -- Case 2: POU(β b) ≠ 0, hence b ∈ chart source β.
    have h_pos_nn : 0 < (chartAtlasPOU I M β : M → ℝ) b := by
      have h_nn : 0 ≤ (chartAtlasPOU I M β : M → ℝ) b :=
        (chartAtlasPOU I M).nonneg β b
      exact lt_of_le_of_ne h_nn (Ne.symm h_pos)
    have hb_β_supp : b ∈ Function.support ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      simp only [Function.mem_support, ne_eq]
      exact h_pos
    have hb_β_tsupp : b ∈ tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hb_β_supp
    -- POU support ⊆ chart source.
    have hsupp_β :
        tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          (chartAt H β).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
    have hb_β : b ∈ (chartAt H β).source := hsupp_β hb_β_tsupp
    -- Now use the cross-chart raw equality.
    have h_raw_eq := tensorChartComponentRaw_eq_of_shared_source
      (I := I) (M := M) h_atlas_strong g r s T α β b hb_α hb_β Idx Jdx
    unfold tensorChartComponentPou
    rw [h_raw_eq]

/-! ## Pointwise Cauchy-Schwarz expansion: `raw α IJ ∘ symm` versus the chart-β
sum

The cross-chart identity `raw α IJ b = Σ_β tensorChartComponentPou β IJ b`,
combined with Cauchy-Schwarz, yields the pointwise bound
`(raw α IJ b)² ≤ |finset| · Σ_β (tensorChartComponentPou β IJ b)²`. We use this
to bound the per-α correction terms in the order-1 and order-2 chart-target
pointwise bounds. -/

/-- Cauchy-Schwarz for a finset sum of reals: `(Σ f i)² ≤ #s · Σ (f i)²`. -/
private lemma finset_sum_sq_le_card_mul_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  have hbase := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ : ι => (1 : ℝ)) f
  simp only [one_mul, one_pow] at hbase
  have h_sum_one : (∑ _i ∈ s, (1 : ℝ)) = (s.card : ℝ) := by simp
  rw [h_sum_one] at hbase
  exact hbase

/-- Pointwise Cauchy-Schwarz for `raw α IJ`: `(raw α IJ b)² ≤ |finset| ·
Σ_β (tensorChartComponentPou β IJ b)²`. -/
private lemma raw_sq_le_card_sum_pou_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_α : b ∈ (chartAt H α).source)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
  classical
  have h_sum := tensorChartComponentRaw_eq_sum_pou
    (I := I) (M := M) h_atlas_strong g r s T α b hb_α Idx Jdx
  rw [h_sum]
  exact finset_sum_sq_le_card_mul_sum_sq
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun β => tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b)

/-! ## Integral bound for `(raw α IJ ∘ symm)² ` over the chart-α target

For each β, the integral `∫_chartTarget α (tensorChartComponentPou β IJ ∘ symm_α)² dy`
is bounded by `(wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²`. This is the
key per-β term in the cross-chart aggregation of the raw correction. -/

/-- For each β and each y ∈ chartTarget α, the squared value of the POU-weighted
raw chart-frame scalar at `β` evaluated at `symm_α y` is bounded by the squared
value of the chart-component function at `β` evaluated at the appropriate point.

When `chartAt H β = chartAt H α`, the chart targets coincide and `symm_α = symm_β`
on this common set, so we can directly identify the two sides. When the charts
disagree, the POU-weighted raw at `β` evaluated at `symm_α y` is zero (because
POU(β) is zero off chart source β, which excludes `symm_α y ∈ chart source α`
under the chart-source-consistency hypothesis), making the inequality trivial. -/
private lemma pou_at_β_sq_le_chartComp_sq_pointwise
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 ≤
      (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2 := by
  classical
  -- Set b := (extChartAt I α).symm (toEuclidean.symm y); we have b ∈ chart source α.
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_α : b ∈ (chartAt H α).source := by
    rw [hb_def]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  -- Case 1: POU(β b) = 0. Then LHS = 0 ≤ RHS trivially.
  by_cases h_pos : (chartAtlasPOU I M β : M → ℝ) b = 0
  · have hLHS_zero :
        tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b = 0 := by
      unfold tensorChartComponentPou
      rw [h_pos, zero_mul]
    rw [hLHS_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _
  -- Case 2: POU(β b) > 0. Then b ∈ chart source β, hence chartAt H α = chartAt H β.
  · have h_pos_nn : 0 < (chartAtlasPOU I M β : M → ℝ) b := by
      have h_nn : 0 ≤ (chartAtlasPOU I M β : M → ℝ) b :=
        (chartAtlasPOU I M).nonneg β b
      exact lt_of_le_of_ne h_nn (Ne.symm h_pos)
    have hb_β_supp : b ∈ Function.support ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      simp only [Function.mem_support, ne_eq]
      exact h_pos
    have hb_β_tsupp : b ∈ tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hb_β_supp
    have hsupp_β :
        tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          (chartAt H β).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
    have hb_β : b ∈ (chartAt H β).source := hsupp_β hb_β_tsupp
    -- Chart consistency: chartAt H α = chartAt H β.
    have h_chart_eq : chartAt H α = chartAt H β :=
      chartAt_eq_of_shared_source (M := M) h_atlas_strong α β b hb_α hb_β
    -- Hence chartTargetEuclid α = chartTargetEuclid β, and symm_α y = symm_β y on this common set.
    have h_target_eq : chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) β :=
      chartTargetEuclid_eq_of_chartAt_eq (I := I) (M := M) h_chart_eq
    have hy_β : y ∈ chartTargetEuclid (I := I) (M := M) β := h_target_eq ▸ hy
    have h_symm_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) =
        (extChartAt I β).symm ((toEuclidean (E := E)).symm y) := by
      rw [extChartAt_eq_of_chartAt_eq (I := I) (M := M) h_chart_eq]
    -- Identify the integrand at β: by `tensorChartComp_apply_of_mem`, `tensorChartComp β IJ y
    -- = tensorChartComponentPou β IJ ((extChartAt I β).symm (toEuclidean.symm y))`.
    have h_apply_β := tensorChartComp_apply_of_mem
      (I := I) (M := M) g r s T β Idx Jdx hy_β
    -- The LHS is `(tensorChartComponentPou β IJ (symm_α y))²`.
    -- The RHS is `(tensorChartComp β IJ y)²`.
    -- Via `h_apply_β` and `h_symm_eq`:
    -- `tensorChartComp β IJ y = tensorChartComponentPou β IJ (symm_β y) = tensorChartComponentPou β IJ (symm_α y)`.
    rw [h_apply_β, ← h_symm_eq, ← hb_def]

/-! ## Per-(α, β, IJ) integral bound for `(raw α IJ ∘ symm_α)²`

Combine the Cauchy-Schwarz pointwise expansion of `(raw α IJ ∘ symm_α)²` and the
per-β pointwise bound by `(tensorChartComp β IJ)²` to obtain an integral bound. -/

/-- Per-(α, β, IJ): the integral of `(tensorChartComponentPou β IJ ∘ symm_α)²`
over `chartTarget α` is bounded by `(wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²`,
i.e. `(wtwokTwoNorm g 1 T)²` after the per-β bound. -/
private lemma int_pou_at_β_symm_sq_le_wkpNorm_zero
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
        ∂(volume : Measure EuclN) ≤
      (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  -- Pointwise: `(tensorChartComponentPou β IJ ∘ symm_α y)² ≤ (tensorChartComp β IJ y)²` for
  -- y ∈ chartTargetEuclid α (by pou_at_β_sq_le_chartComp_sq_pointwise).
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) ≤
        ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2) := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (pou_at_β_sq_le_chartComp_sq_pointwise (I := I) (M := M) h_atlas_strong
        g r s T α β y hy Idx Jdx)
  have h_chartTarget_meas_α : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_int_le :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2)
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas_α
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  refine h_int_le.trans ?_
  -- Bound `∫_chartTarget α (tensorChartComp β IJ)² ≤ ∫_EuclN (tensorChartComp β IJ)²`.
  -- And `∫_EuclN = ∫_chartTarget β` (since tensorChartComp β IJ has support in chartTarget β).
  -- The latter equals `(wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²` by the
  -- `sq_eLpNorm_two_eq_lintegral_ofReal_sq` identity.
  have h_int_ext :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y,
            ENNReal.ofReal
              ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2)
            ∂(volume : Measure EuclN) :=
    MeasureTheory.setLIntegral_le_lintegral _ _
  refine h_int_ext.trans ?_
  -- Now identify the full lintegral with the chartTarget β lintegral (support).
  have h_supp_β :
      tsupport (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) ⊆
        chartTargetEuclid (I := I) (M := M) β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  -- Outside chartTargetEuclid β: tensorChartComp β IJ = 0, so the integrand is 0.
  have h_chartTarget_meas_β : MeasurableSet (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) β
  have h_off_β_zero : ∀ y ∉ chartTargetEuclid (I := I) (M := M) β,
      ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2) = 0 := by
    intro y hy
    rw [tensorChartComp_apply_of_notMem (I := I) (M := M) g r s T β Idx Jdx hy]
    simp
  have h_full_eq_restrict :
      ∫⁻ y,
          ENNReal.ofReal
            ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2)
          ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
            ENNReal.ofReal
              ((tensorChartComp (I := I) (M := M) g r s T β Idx Jdx y) ^ 2)
            ∂(volume : Measure EuclN) := by
    rw [← MeasureTheory.lintegral_indicator h_chartTarget_meas_β]
    refine lintegral_congr ?_
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) β
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, h_off_β_zero y hy]
  rw [h_full_eq_restrict]
  -- Now use sq_eLpNorm_two_eq_lintegral_ofReal_sq: this is the existing
  -- conversion that relates (eLpNorm f 2 μ)² to ∫⁻ ofReal(f²) ∂μ.
  -- This needs to match: wkpNorm 0 2 (tensorChartComp β IJ) chartTarget β = eLpNorm ...
  rw [wkpNorm_zero (d := Module.finrank ℝ E) 2 _ _]
  -- Now: (eLpNorm (tensorChartComp β IJ) 2 (vol.restrict chartTarget β))² =
  --   ∫⁻ y in chartTarget β, ofReal ((tensorChartComp β IJ y)²) ∂vol
  rw [sq_eLpNorm_two_eq_lintegral_ofReal_sq
    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
    ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) β))]

/-! ## Per-(α, IJ) integral bound for `(raw α IJ ∘ symm_α)²`

Combining the Cauchy-Schwarz pointwise expansion of `(raw α IJ ∘ symm_α)²` and
the per-β integral bound by `(wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²`,
the integral of `(raw α IJ ∘ symm_α)²` over `chartTarget α` is bounded by
`|finset|² · (wtwokTwoNorm g 1 T)²`. -/

/-- Per-(α, IJ): the lintegral of `(raw α IJ ∘ symm_α)²` over `chartTarget α`
is bounded by `|finset| · Σ_β (wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²`. -/
private lemma int_raw_α_symm_sq_le_card_sum_wkpNorm_zero_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  -- Pointwise Cauchy-Schwarz expansion.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) ≤
        ENNReal.ofReal
          (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
    intro y hy
    have hb_α : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H α).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
    exact ENNReal.ofReal_le_ofReal
      (raw_sq_le_card_sum_pou_sq (I := I) (M := M) h_atlas_strong g r s T α _ hb_α Idx Jdx)
  have h_chartTarget_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_int_le_pointwise :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
                ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
                  (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  refine h_int_le_pointwise.trans ?_
  -- Pull constants and sums.
  have hN_nn : 0 ≤ ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) :=
    Nat.cast_nonneg _
  -- ofReal(N · Σ_β (...)²) = ofReal N · ofReal Σ_β (...)² = ofReal N · Σ_β ofReal (...)²
  have h_split_pt : ∀ y,
      ENNReal.ofReal
          (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) =
        ENNReal.ofReal ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ENNReal.ofReal
              ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
    intro y
    rw [ENNReal.ofReal_mul hN_nn]
    rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => sq_nonneg _)]
  -- AEMeasurability of `y ↦ ofReal ((POU β IJ ∘ symm_α y)²)` on restricted chartTarget α.
  -- This is proved by ContinuousOn of (POU β IJ ∘ symm_α) on chartTarget α + measurability lift.
  have h_aemeas_pou : ∀ β,
      AEMeasurable
        (fun y : EuclN =>
          ENNReal.ofReal
            ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro β
    -- ContinuousOn of the extChartAt symm on its target.
    have h_extChartAt_symm_contOn :
        ContinuousOn (extChartAt I α).symm ((extChartAt I α).target) :=
      continuousOn_extChartAt_symm (I := I) α
    have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
      (toEuclidean (E := E)).symm.continuous
    -- Build ContinuousOn of `y ↦ (extChartAt I α).symm ((toEuclidean (E := E)).symm y)` on chartTarget α.
    have h_sym_contOn : ContinuousOn
        (fun y : EuclN =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_extChartAt_symm_contOn.comp h_toEucl_symm_cont.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    -- POU β IJ is ContMDiff on M (since POU is C^∞ and raw β IJ is C^∞ on chart source β,
    -- and POU is supported in chart source β); but here we need just CONTINUITY at points
    -- of chartTarget α (open).
    -- Use a fact: `tensorChartComponentPou β IJ` is continuous on M (proven below).
    have h_pou_cont :
        Continuous (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx) := by
      -- POU(β) is continuous, raw β IJ is continuous on chart source β; on M as a whole,
      -- POU(β) · raw β IJ is continuous because off chart source β, POU(β) = 0.
      apply continuous_of_tsupport
      intro x hx
      have hsupp_β :
          tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
            (chartAt H β).source :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
      have hx_pou_tsupp :
          x ∈ tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        Set.mem_of_subset_of_mem (tsupport_smul_subset_left _ _) hx
      have hx_src : x ∈ (chartAt H β).source := hsupp_β hx_pou_tsupp
      have hP_cont : Continuous ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        (chartAtlasPOU I M β).contMDiff.continuous
      have hR_contOn : ContinuousOn
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx)
          (chartAt H β).source :=
        (tensorChartComponentRaw_contMDiffOn_chart_source
          (I := I) (M := M) g r s T β Idx Jdx).continuousOn
      have hR_contAt : ContinuousAt
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx) x :=
        ContinuousOn.continuousAt hR_contOn ((chartAt H β).open_source.mem_nhds hx_src)
      exact (hP_cont.continuousAt.mul hR_contAt)
    have h_pou_sym_contOn : ContinuousOn
        (fun y : EuclN =>
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_pou_cont.continuousOn.comp h_sym_contOn (Set.mapsTo_univ _ _)
    have h_pou_sym_ae : AEMeasurable
        (fun y : EuclN =>
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_pou_sym_contOn.aemeasurable h_chartTarget_meas
    have h_sq_ae : AEMeasurable
        (fun y : EuclN =>
          (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_pou_sym_ae.pow_const 2
    exact ENNReal.measurable_ofReal.comp_aemeasurable h_sq_ae
  have h_int_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
              ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
                (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  ((tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
                ∂(volume : Measure EuclN) := by
    rw [lintegral_congr (fun y => h_split_pt y)]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_finset_sum' _ (fun β _ => h_aemeas_pou β)
  rw [h_int_split]
  -- Now: ENNReal.ofReal N · Σ_β ∫_chartTarget α (POU β IJ ∘ symm_α y)² dy ≤
  --   ENNReal.ofReal N · Σ_β (wkpNorm 0 2 tensorChartComp β IJ chartTarget β)²
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  refine Finset.sum_le_sum (fun β _ => ?_)
  exact int_pou_at_β_symm_sq_le_wkpNorm_zero
    (I := I) (M := M) h_atlas_strong g r s T α β Idx Jdx

/-! ## Aggregate per-(α, IJ) bound for the raw correction over the finset

Combining `int_raw_α_symm_sq_le_card_sum_wkpNorm_zero_sq` with the per-β bound
`wkpNorm_zero_sq_le_wtwokTwoNorm_sq` gives an aggregate bound expressible as
`|finset|² · (wtwokTwoNorm)²`. -/

/-- Per-(α, IJ): the lintegral of `(raw α IJ ∘ symm_α)²` over `chartTarget α`
is bounded by `|finset|² · (wtwokTwoNorm g 1 T)²`. -/
private lemma int_raw_α_symm_sq_le_card_sq_mul_wtwokTwoNorm_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
          (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2) := by
  classical
  refine (int_raw_α_symm_sq_le_card_sum_wkpNorm_zero_sq
    (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx).trans ?_
  -- The factor `ENNReal.ofReal N` (with N = |finset|) is already pulled out.
  -- We then bound the sum by `N · wtwokTwoNorm²` via `wkpNorm_zero_sq_le_wtwokTwoNorm_sq`.
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  have h_per_β : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) β)) ^ 2 ≤ W := by
    intro β _
    exact wkpNorm_zero_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T β Idx Jdx
  have h_sum_le :
      ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) β)) ^ 2 ≤
        ∑ _β ∈ chartAtlasPOU_finset (I := I) (M := M), W :=
    Finset.sum_le_sum h_per_β
  refine h_sum_le.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Chain rule transformation for `iteratedFDeriv 2` across `toEuclidean`

For the principal piece in `B'.3c`, the integrand
`‖iteratedFDeriv ℝ 2 (POU · raw_IJ ∘ extChartAt.symm) ((toEuclidean.symm) y)‖²`
is related to `‖iteratedFDeriv ℝ 2 (tensorChartComp α IJ) y‖²` via the chain
rule applied to the linear isomorphism `toEuclidean`. The factor introduced is
`‖toEuclidean‖²` (per derivative slot, raised to the power 2 from the squared
norm). -/

/-- Chain rule transformation: for `y ∈ chartTarget α`, the squared model-space
iterated Fréchet 2-derivative of the POU-weighted raw chart-frame scalar pulled
back through the chart symm is bounded by a multiple of the squared Euclidean
iterated Fréchet 2-derivative of the chart-component function. -/
private lemma iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ 2
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e'))
        ((toEuclidean (E := E)).symm y)‖ ^ 2 ≤
      (‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2 *
        ‖iteratedFDeriv ℝ 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2 := by
  classical
  set L : E →L[ℝ] EuclN := (toEuclidean (E := E) : E ≃L[ℝ] EuclN).toContinuousLinearMap
  set f : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T α Idx Jdx with hf_def
  set u : E → ℝ := fun e' =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e') *
      tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm e') with hu_def
  -- On `(extChartAt I α).target` (open), `u = f ∘ L`.
  have he : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_open : IsOpen ((extChartAt I α).target) := isOpen_extChartAt_target (I := I) α
  have h_agree_on : Set.EqOn u (f ∘ L) ((extChartAt I α).target) := by
    intro e' he'
    -- u e' = POU(symm e') · raw(symm e').
    -- f (L e') = tensorChartComp α IJ (toEuclidean e').
    -- Since L e' = toEuclidean e' ∈ chartTargetEuclid α iff e' ∈ (extChartAt α).target.
    have hL_e' : L e' = toEuclidean e' := rfl
    have h_L_e'_target : L e' ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨e', he', rfl⟩
    have h_f_apply :
        f (L e') =
          tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm (L e'))) := by
      rw [hf_def]
      exact tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx h_L_e'_target
    -- Simplify (toEuclidean (E := E)).symm (L e') = e'.
    have h_symL_e' : (toEuclidean (E := E)).symm (L e') = e' := by
      change (toEuclidean (E := E)).symm (toEuclidean e') = e'
      exact (toEuclidean (E := E)).symm_apply_apply e'
    rw [h_symL_e'] at h_f_apply
    -- Now identify u with f(L e').
    change u e' = f (L e')
    rw [h_f_apply]
    unfold tensorChartComponentPou
    rfl
  -- iteratedFDeriv at interior points (open set) only depends on local values.
  have h_iter_eq :
      iteratedFDeriv ℝ 2 u ((toEuclidean (E := E)).symm y) =
        iteratedFDeriv ℝ 2 (f ∘ L) ((toEuclidean (E := E)).symm y) := by
    have h_evEq : u =ᶠ[𝓝 ((toEuclidean (E := E)).symm y)] (f ∘ L) :=
      Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_agree_on
    exact (Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq 2).eq_of_nhds
  rw [h_iter_eq]
  -- Apply ContinuousLinearMap.iteratedFDeriv_comp_right for L.
  have h_f_cd : ContDiff ℝ ∞ f :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
  have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  rw [L.iteratedFDeriv_comp_right (n := (⊤ : ℕ∞)) h_f_cd _ h2_le]
  -- Simplify L ((toEuclidean.symm) y) = y.
  have h_L_sym : L ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  rw [h_L_sym]
  -- Now the LHS is `‖.compContinuousLinearMap (fun _ => L)‖²` evaluated at y.
  -- Use `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`.
  have h_norm_le : ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
        (fun _ : Fin 2 => L)‖ ≤
      ‖iteratedFDeriv ℝ 2 f y‖ * ∏ _i : Fin 2, ‖L‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  rw [show (∏ _i : Fin 2, ‖L‖) = ‖L‖ ^ 2 from by
    rw [Finset.prod_const]; simp] at h_norm_le
  -- Now square both sides.
  have hLHS_nn : 0 ≤ ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
      (fun _ : Fin 2 => L)‖ := norm_nonneg _
  have h_sq_le : ‖(iteratedFDeriv ℝ 2 f y).compContinuousLinearMap
        (fun _ : Fin 2 => L)‖ ^ 2 ≤
      (‖iteratedFDeriv ℝ 2 f y‖ * ‖L‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hLHS_nn h_norm_le 2
  have hL_norm : ‖L‖ = ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ := rfl
  rw [hL_norm] at h_sq_le
  refine h_sq_le.trans (le_of_eq ?_)
  ring

/-! ## Per-(α, IJ) integral bound for `‖fderiv (raw α IJ ∘ symm)‖²`

Analogous to the iteratedFDeriv 2 bridge: for y ∈ chartTarget α, the squared
model-space Fréchet derivative norm of `raw α IJ ∘ extChartAt.symm` evaluated at
toEuclidean.symm y is bounded by `‖toEuclidean‖² ·
‖fderiv (raw α IJ ∘ symm_α ∘ toEuclidean.symm)‖² = ‖toEuclidean‖² ·
‖fderiv (raw α IJ ∘ symm_α — chart-pulled)‖²` ... well, this involves the same
chain rule logic but without the POU factor.

Actually, on `chartTarget α` we have `raw α IJ ∘ extChartAt.symm ∘ toEuclidean.symm =
Σ_β tensorChartComponentPou β IJ ∘ extChartAt.symm ∘ toEuclidean.symm`. The fderiv
distributes through the sum, so Cauchy-Schwarz reduces to per-β terms. Under
chart equality with β, the per-β term equals `fderiv (tensorChartComp β IJ ∘ toEuclidean)`,
which via the chain rule is bounded by `‖toEuclidean‖ · ‖fderiv (tensorChartComp β IJ)‖`.

This gives:
```
∫_chartTarget α ‖fderiv (raw α IJ ∘ symm_α) (toEucl.symm y)‖² dy ≤
  |finset| · ‖toEuclidean‖² · Σ_β (wkpNorm 2 2 tensorChartComp β IJ chartTarget β)²
```
under chart-source consistency. The total ≤ |finset|² · ‖toEuclidean‖² · wtwokTwoNorm².
-/

/-- The fderiv bridge: for the chain rule of `raw α IJ ∘ symm_α ∘ toEuclidean.symm`,
the squared model-space Fréchet derivative norm is bounded by a multiple of the
squared Euclidean Fréchet derivative norm of the corresponding chart-pushed
function. -/
private lemma fderiv_raw_symm_sq_le_fderiv_chartComp_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖fderiv ℝ
        (fun e' : E =>
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) ((toEuclidean (E := E)).symm y)‖ ^ 2 ≤
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2 *
        ‖fderiv ℝ
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2 := by
  classical
  set L : E →L[ℝ] EuclN := (toEuclidean (E := E) : E ≃L[ℝ] EuclN).toContinuousLinearMap
  set f : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T β Idx Jdx with hf_def
  set u : E → ℝ := fun e' =>
    tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
      ((extChartAt I α).symm e') with hu_def
  -- We'll show u = f ∘ L on (extChartAt I α).target (open) under chart consistency or
  -- show u = 0 on (extChartAt I α).target under chart inequality.
  -- Then by EventuallyEq, fderiv u (toEuclidean.symm y) = fderiv (f ∘ L) (toEuclidean.symm y)
  -- or = 0 respectively.
  have he : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_open : IsOpen ((extChartAt I α).target) := isOpen_extChartAt_target (I := I) α
  -- Case analysis: chart consistency at α and β.
  -- Use the same disjoint-source argument as before.
  by_cases h_some_b_β : ∃ b ∈ (chartAt H α).source, b ∈ (chartAt H β).source
  · -- chart equality case.
    obtain ⟨b, hb_α, hb_β⟩ := h_some_b_β
    have h_chart_eq : chartAt H α = chartAt H β :=
      chartAt_eq_of_shared_source (M := M) h_atlas_strong α β b hb_α hb_β
    have h_target_eq : (extChartAt I α).target = (extChartAt I β).target := by
      rw [extChartAt_eq_of_chartAt_eq (I := I) (M := M) h_chart_eq]
    have h_chartTargetEucl_eq : chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) β :=
      chartTargetEuclid_eq_of_chartAt_eq (I := I) (M := M) h_chart_eq
    -- u = f ∘ L on (extChartAt I α).target.
    have h_agree_on : Set.EqOn u (f ∘ L) ((extChartAt I α).target) := by
      intro e' he'
      have hL_e' : L e' = toEuclidean e' := rfl
      have h_L_e'_target_α : L e' ∈ chartTargetEuclid (I := I) (M := M) α :=
        ⟨e', he', rfl⟩
      have h_L_e'_target_β : L e' ∈ chartTargetEuclid (I := I) (M := M) β :=
        h_chartTargetEucl_eq ▸ h_L_e'_target_α
      have h_f_apply :
          f (L e') = tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I β).symm ((toEuclidean (E := E)).symm (L e'))) := by
        rw [hf_def]
        exact tensorChartComp_apply_of_mem (I := I) (M := M) g r s T β Idx Jdx h_L_e'_target_β
      have h_symL_e' : (toEuclidean (E := E)).symm (L e') = e' := by
        change (toEuclidean (E := E)).symm (toEuclidean e') = e'
        exact (toEuclidean (E := E)).symm_apply_apply e'
      rw [h_symL_e'] at h_f_apply
      have h_extChart_eq : extChartAt I α = extChartAt I β :=
        extChartAt_eq_of_chartAt_eq (I := I) (M := M) h_chart_eq
      change u e' = f (L e')
      rw [h_f_apply]
      change tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
          ((extChartAt I α).symm e') = _
      rw [h_extChart_eq]
    have h_fderiv_eq :
        fderiv ℝ u ((toEuclidean (E := E)).symm y) =
          fderiv ℝ (f ∘ L) ((toEuclidean (E := E)).symm y) := by
      have h_evEq : u =ᶠ[𝓝 ((toEuclidean (E := E)).symm y)] (f ∘ L) :=
        Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_agree_on
      exact h_evEq.fderiv_eq
    rw [h_fderiv_eq]
    -- Chain rule for f ∘ L.
    have h_f_cd : ContDiff ℝ ∞ f :=
      tensorChartComp_contDiff (I := I) (M := M) g r s T β Idx Jdx
    have h_f_diff : Differentiable ℝ f :=
      h_f_cd.differentiable (by decide)
    have h_f_diff_at : DifferentiableAt ℝ f (L ((toEuclidean (E := E)).symm y)) :=
      h_f_diff _
    rw [fderiv_comp ((toEuclidean (E := E)).symm y) h_f_diff_at
      L.differentiableAt]
    -- ‖fderiv f (L (...)) ∘L fderiv L (...)‖ ≤ ‖fderiv f (L (...))‖ · ‖fderiv L (...)‖.
    have h_L_sym : L ((toEuclidean (E := E)).symm y) = y :=
      (toEuclidean (E := E)).apply_symm_apply y
    rw [show fderiv ℝ L ((toEuclidean (E := E)).symm y) = L from L.fderiv]
    rw [h_L_sym]
    have h_op_le := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f y) L
    have h_sq_le : ‖(fderiv ℝ f y).comp L‖ ^ 2 ≤ (‖fderiv ℝ f y‖ * ‖L‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_op_le 2
    refine h_sq_le.trans (le_of_eq ?_)
    have hL_norm : ‖L‖ = ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ := rfl
    rw [hL_norm]
    ring
  · -- chart inequality case: chart source α ∩ chart source β = ∅.
    rw [show (¬ (∃ b ∈ (chartAt H α).source, b ∈ (chartAt H β).source)) ↔
        ∀ b ∈ (chartAt H α).source, b ∉ (chartAt H β).source from by
      constructor
      · intro h b hb hb'
        exact h ⟨b, hb, hb'⟩
      · intro h ⟨b, hb, hb'⟩
        exact h b hb hb'] at h_some_b_β
    -- u is identically 0 on (extChartAt I α).target (because POU β = 0 on chart source α
    -- and we map there).
    have h_u_zero_on : Set.EqOn u 0 ((extChartAt I α).target) := by
      intro e' he'
      -- (extChartAt I α).symm e' ∈ chart source α.
      have hsym_e'_src_α : (extChartAt I α).symm e' ∈ (chartAt H α).source := by
        rw [← extChartAt_source (I := I)]
        exact (extChartAt I α).map_target he'
      -- (extChartAt I α).symm e' ∉ chart source β.
      have hsym_e'_notin_β : (extChartAt I α).symm e' ∉ (chartAt H β).source :=
        h_some_b_β _ hsym_e'_src_α
      -- POU(β) is supported in chart source β, so POU(β at sym e') = 0.
      have hsupp_β :
          tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
            (chartAt H β).source :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
      have h_POU_zero : (chartAtlasPOU I M β : M → ℝ)
          ((extChartAt I α).symm e') = 0 := by
        by_contra hne
        have h_in_supp : (extChartAt I α).symm e' ∈ Function.support
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          simp only [Function.mem_support, ne_eq]
          exact hne
        have h_in_tsupp : (extChartAt I α).symm e' ∈ tsupport
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _ h_in_supp
        exact hsym_e'_notin_β (hsupp_β h_in_tsupp)
      change tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
          ((extChartAt I α).symm e') = (0 : ℝ)
      unfold tensorChartComponentPou
      rw [h_POU_zero, zero_mul]
    have h_fderiv_zero :
        fderiv ℝ u ((toEuclidean (E := E)).symm y) = 0 := by
      have h_evEq : u =ᶠ[𝓝 ((toEuclidean (E := E)).symm y)] (fun _ => 0 : E → ℝ) :=
        Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_u_zero_on
      rw [h_evEq.fderiv_eq]
      change fderiv ℝ (Function.const _ (0 : ℝ)) ((toEuclidean (E := E)).symm y) = _
      rw [fderiv_const]
      rfl
    rw [h_fderiv_zero]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-! ## Per-(α, IJ) integral bound for `‖fderiv (raw α IJ ∘ symm) (toEucl.symm y)‖²`

Combining the Cauchy-Schwarz expansion of `fderiv (raw α IJ ∘ symm_α)` (as a sum
over β of `fderiv (POU β IJ ∘ symm_α)`), the per-β bound by
`‖toEuclidean‖² · ‖fderiv (tensorChartComp β IJ)‖²` (from the chain rule under
chart consistency), and the integral bound `(wkpNorm 2 2 tensorChartComp β IJ)²`
(via the Sobolev chart-target bridge), we obtain:
```
∫_chartTarget α ‖fderiv (raw α IJ ∘ extChartAt.symm) (toEucl.symm y)‖² dy ≤
  |finset|² · ‖toEucl‖² · (wtwokTwoNorm g 1 T)²
```
for each (α, IJ). -/

/-- Pointwise version: combining the Cauchy-Schwarz bound on the linearised raw
sum and the per-β fderiv bridge. -/
private lemma fderiv_raw_symm_pointwise_bound
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2 ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2 *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ‖fderiv ℝ
                (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2 := by
  classical
  -- `raw α IJ ∘ extChartAt.symm = Σ_β POU β IJ ∘ extChartAt.symm` on
  -- (extChartAt α).target. Hence the fderiv distributes.
  set e : E := (toEuclidean (E := E)).symm y
  have he : e ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_open : IsOpen ((extChartAt I α).target) := isOpen_extChartAt_target (I := I) α
  -- Establish the equation `raw α IJ ∘ extChartAt.symm = Σ_β POU β IJ ∘ extChartAt.symm`
  -- pointwise on (extChartAt α).target.
  have h_agree_on : Set.EqOn
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (fun e' =>
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) ((extChartAt I α).target) := by
    intro e' he'
    have hb_α : (extChartAt I α).symm e' ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target he'
    exact tensorChartComponentRaw_eq_sum_pou
      (I := I) (M := M) h_atlas_strong g r s T α _ hb_α Idx Jdx
  -- fderiv eq via EventuallyEq.
  have h_fderiv_eq :
      fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e =
        fderiv ℝ (fun e' =>
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
              ((extChartAt I α).symm e')) e := by
    have h_evEq :
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
          (extChartAt I α).symm) =ᶠ[𝓝 e] (fun e' =>
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
              ((extChartAt I α).symm e')) :=
      Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_agree_on
    exact h_evEq.fderiv_eq
  rw [h_fderiv_eq]
  -- Distribute fderiv over the finite sum (each summand differentiable).
  -- Use HasFDerivAt at e for each summand to conclude the sum is differentiable.
  -- Then the fderiv of the sum equals the sum of fderivs.
  have h_each_diff : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      DifferentiableAt ℝ (fun e' =>
        tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
          ((extChartAt I α).symm e')) e := by
    intro β _
    -- Differentiability via ContDiffOn of `pou (extChartAt.symm)` on (extChartAt α).target.
    -- In the chart-equality case, this is C^∞; in the inequality case, it's the constant zero.
    -- Either way, it's differentiable at e ∈ (extChartAt α).target (open).
    by_cases h_some : ∃ b ∈ (chartAt H α).source, b ∈ (chartAt H β).source
    · obtain ⟨b, hb_α, hb_β⟩ := h_some
      have h_chart_eq : chartAt H α = chartAt H β :=
        chartAt_eq_of_shared_source (M := M) h_atlas_strong α β b hb_α hb_β
      -- ContDiffOn proof.
      have hP_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        (chartAtlasPOU I M β).contMDiff
      have hR_cd : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx)
          ((chartAt H β).source) :=
        tensorChartComponentRaw_contMDiffOn_chart_source
          (I := I) (M := M) g r s T β Idx Jdx
      -- The composition (POU · raw β IJ) ∘ extChartAt α.symm is differentiable on (extChartAt α).target.
      -- This is messy; use the fact that the function is ContMDiff on M (proven below).
      have h_pou_contMDiff :
          ContMDiff I (𝓘(ℝ, ℝ)) ∞
            (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx) := by
        refine contMDiff_of_tsupport (fun x hx => ?_)
        have hsupp_β :
            tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
              (chartAt H β).source :=
          DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
        have hx_pou_tsupp :
            x ∈ tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          Set.mem_of_subset_of_mem (tsupport_smul_subset_left _ _) hx
        have hx_src : x ∈ (chartAt H β).source := hsupp_β hx_pou_tsupp
        refine ContMDiffAt.mul ?_ ?_
        · exact hP_smooth.contMDiffAt
        · exact (hR_cd x hx_src).contMDiffAt
            ((chartAt H β).open_source.mem_nhds hx_src)
      -- Use ContMDiffAt for the manifold smoothness, then compose.
      have h_sym_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm e := by
        have h_cont_within := contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) α
        exact h_cont_within.contMDiffAt (h_open.mem_nhds he)
      have h_comp_at : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
          (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx ∘
            (extChartAt I α).symm) e :=
        h_pou_contMDiff.contMDiffAt.comp e h_sym_at
      -- ContDiffAt from ContMDiffAt on Euclidean.
      have h_cdAt : ContDiffAt ℝ ∞
          (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx ∘
            (extChartAt I α).symm) e := by
        rw [← contMDiffAt_iff_contDiffAt]
        exact h_comp_at
      exact h_cdAt.differentiableAt (by decide)
    · -- chart inequality case.
      have h_some_negated : ∀ b ∈ (chartAt H α).source, b ∉ (chartAt H β).source := by
        intro b hb hb'
        exact h_some ⟨b, hb, hb'⟩
      -- The function is identically 0 on (extChartAt α).target.
      have h_zero_on : ∀ e' ∈ (extChartAt I α).target,
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e') = 0 := by
        intro e' he'
        have hsym_e'_src_α : (extChartAt I α).symm e' ∈ (chartAt H α).source := by
          rw [← extChartAt_source (I := I)]
          exact (extChartAt I α).map_target he'
        have hsym_e'_notin_β : (extChartAt I α).symm e' ∉ (chartAt H β).source :=
          h_some_negated _ hsym_e'_src_α
        have hsupp_β :
            tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
              (chartAt H β).source :=
          DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
        have h_POU_zero : (chartAtlasPOU I M β : M → ℝ)
            ((extChartAt I α).symm e') = 0 := by
          by_contra hne
          have h_in_supp : (extChartAt I α).symm e' ∈ Function.support
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
            simp only [Function.mem_support, ne_eq]
            exact hne
          have h_in_tsupp : (extChartAt I α).symm e' ∈ tsupport
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
            subset_tsupport _ h_in_supp
          exact hsym_e'_notin_β (hsupp_β h_in_tsupp)
        unfold tensorChartComponentPou
        rw [h_POU_zero, zero_mul]
      -- Differentiability of a constant function at e.
      have h_evEq : (fun e' =>
        tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
          ((extChartAt I α).symm e')) =ᶠ[𝓝 e] (fun _ => (0 : ℝ)) :=
        Filter.eventuallyEq_of_mem (h_open.mem_nhds he) h_zero_on
      exact (differentiable_const (0 : ℝ)).differentiableAt.congr_of_eventuallyEq h_evEq
  -- Distribute fderiv.
  have h_fderiv_sum : fderiv ℝ
      (fun e' =>
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) e =
      ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        fderiv ℝ (fun e' =>
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) e := by
    rw [show (fun e' =>
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) =
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          (fun e' => tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
            ((extChartAt I α).symm e')) from by
      funext e'
      rw [Finset.sum_apply]]
    exact fderiv_sum h_each_diff
  rw [h_fderiv_sum]
  -- Cauchy-Schwarz: ‖Σ a_β‖² ≤ |finset| · Σ ‖a_β‖².
  have h_sum_bound :
      ‖∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            fderiv ℝ (fun e' =>
              tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm e')) e‖ ^ 2 ≤
        ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ‖fderiv ℝ (fun e' =>
              tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm e')) e‖ ^ 2 := by
    -- Use Cauchy-Schwarz via norm_sum_le and Finset.inner_mul_le_norm_mul_norm-style.
    have h_norm_sum_le :
        ‖∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              fderiv ℝ (fun e' =>
                tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                  ((extChartAt I α).symm e')) e‖ ≤
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ‖fderiv ℝ (fun e' =>
              tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                ((extChartAt I α).symm e')) e‖ :=
      norm_sum_le _ _
    have h_sq : (‖∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              fderiv ℝ (fun e' =>
                tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                  ((extChartAt I α).symm e')) e‖) ^ 2 ≤
        (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ‖fderiv ℝ (fun e' =>
                tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                  ((extChartAt I α).symm e')) e‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_norm_sum_le 2
    refine h_sq.trans ?_
    exact finset_sum_sq_le_card_mul_sum_sq
      (chartAtlasPOU_finset (I := I) (M := M))
      (fun β => ‖fderiv ℝ (fun e' =>
        tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
          ((extChartAt I α).symm e')) e‖)
  refine h_sum_bound.trans ?_
  -- Each per-β term bounded by ‖toEuclidean‖² · ‖fderiv (tensorChartComp β IJ) y‖².
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun β _ => ?_)
  exact fderiv_raw_symm_sq_le_fderiv_chartComp_sq
    (I := I) (M := M) h_atlas_strong g r s T α β Idx Jdx y hy

/-! ## Pre-headline helpers: pouImage membership under boundaryless atlases -/

/-- For `y ∈ chartTargetEuclid α` and `POU(α at symm y) ≠ 0`, the inverse-chart
preimage `symm y` lies in `tsupport POU(α) ∩ chartLeviCivitaGoodSet`. Under
`[I.Boundaryless]`, the good set equals the chart source, and `tsupport POU(α)
⊆ chart source α` (subordinate), so the intersection equals `tsupport POU(α)`. -/
private lemma symm_mem_pou_inter_goodSet
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_pou_pos :
      (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≠ 0) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
        chartLeviCivitaGoodSet (I := I) α := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source := by
    rw [hb_def]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_supp : b ∈ Function.support ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    simp only [Function.mem_support, ne_eq]
    exact h_pou_pos
  have hb_tsupp : b ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ hb_supp
  have h_goodSet_eq : chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  have hb_extSrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [h_goodSet_eq]; exact hb_extSrc
  exact ⟨hb_tsupp, hb_good⟩

/-- For `y ∈ chartTargetEuclid α` and `POU(α at symm y) ≠ 0`, `y` lies in the
`toEuclidean` image of `extChartAt α` image of `tsupport POU(α) ∩ goodSet`. -/
private lemma mem_pouImage_of_pou_pos
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (h_pou_pos :
      (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≠ 0) :
    y ∈ (toEuclidean : E ≃L[ℝ] EuclN) ''
          ((extChartAt I α) ''
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              chartLeviCivitaGoodSet (I := I) α)) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_in : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        chartLeviCivitaGoodSet (I := I) α :=
    symm_mem_pou_inter_goodSet (I := I) (M := M) α hy h_pou_pos
  refine ⟨(toEuclidean (E := E)).symm y, ⟨b, hb_in, ?_⟩, ?_⟩
  · rw [hb_def]
    exact (extChartAt I α).right_inv hb_target
  · exact (toEuclidean (E := E)).apply_symm_apply y

/-- **Per-α pointwise bound**: on `chartTargetEuclid α`, the POU²-weighted
chart-pulled squared norm of the raw connection Laplacian is bounded
pointwise by `K_2b` times the POU²-weighted sum of squared chart-data norms.
Outside the partition-of-unity support, the bound is trivial (the integrand
is zero). -/
private lemma per_alpha_pointwise_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
            tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M =>
                rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) b) y ≤
          K * (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 +
                ‖fderiv ℝ
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2 +
                ‖iteratedFDeriv ℝ 2
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) := by
  classical
  obtain ⟨K_2b, hK_2b_nn, hK_2b_bound⟩ :=
    tensorTrivProjPushedNormSq_rawTensorConnLap_le_chartTarget_data_on_pouImage
      (I := I) (M := M) h_atlas g r s α
  refine ⟨K_2b, hK_2b_nn, ?_⟩
  intro T y hy
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2
  set F : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
      ((toEuclidean (E := E)).symm y)‖ ^ 2
  set Inorm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
      ((toEuclidean (E := E)).symm y)‖ ^ 2
  set X : ℝ := tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
      (fun b : M =>
        rawTensorConnLap (I := I) g r s
          (fun z : M => T.toSection z) b) y
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hX_nn : 0 ≤ X :=
    tensorTrivProjPushedNormSq_nonneg (I := I) (M := M) g r s α _ y
  have hV_nn : 0 ≤ V := sq_nonneg _
  have hF_nn : 0 ≤ F := sq_nonneg _
  have hI_nn : 0 ≤ Inorm := sq_nonneg _
  have hSum_nn : 0 ≤ V + F + Inorm := by linarith
  by_cases h_pou : ρ = 0
  · have h_lhs_zero : ρ ^ 2 * X = 0 := by
      rw [show ρ ^ 2 = 0 from by rw [h_pou]; ring, zero_mul]
    rw [h_lhs_zero]
    refine mul_nonneg hK_2b_nn ?_
    refine mul_nonneg hρ_sq_nn hSum_nn
  · have hy_pouImage := mem_pouImage_of_pou_pos (I := I) (M := M) α hy h_pou
    have h_X_le : X ≤ K_2b * (V + F + Inorm) := hK_2b_bound T hy_pouImage
    have h_scaled : ρ ^ 2 * X ≤ ρ ^ 2 * (K_2b * (V + F + Inorm)) :=
      mul_le_mul_of_nonneg_left h_X_le hρ_sq_nn
    refine h_scaled.trans (le_of_eq ?_)
    ring

/-! ## Public headlines

We deliver the two public headlines as `axiom`-free, `sorry`-free thin
statements that compose the per-α pointwise B'.2b bound together with the
three chart-component data integral bounds (B'.3a, B'.3b, B'.3c) and the
cross-chart aggregation helpers established above. The mathematical core
goes through the following intermediate steps:

(i) For each `α ∈ chartAtlasPOU_finset`, the chart-α POU²-weighted integral
of the chart-pulled squared norm of the raw connection Laplacian is bounded
pointwise via `per_alpha_pointwise_bound` (B'.2b) by `K_α α` times
`POU(α)² · (V² + F² + I²)`. Integrating over `chartTargetEuclid α` gives a
sum of three integrals corresponding to B'.3a, B'.3b, B'.3c, each of which
admits an explicit bound in terms of the chart-component Sobolev data:

  * B'.3a bound is the chart-component `wkpNorm 0 2` integral, controlled
    by `wkpNorm_zero_sq_le_wtwokTwoNorm_sq`.
  * B'.3b bound is the chart-component `wkpNorm 1 2` integral (principal)
    plus an `eLpNorm`²-of-raw-component correction, controlled by
    `wkpNorm_one_sq_le_wtwokTwoNorm_sq` and
    `int_raw_α_symm_sq_le_card_sq_mul_wtwokTwoNorm_sq`.
  * B'.3c bound has a principal `iteratedFDeriv 2`-of-pou-weighted-raw
    component piece (which by the chain-rule helper
    `iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq`
    is controlled by the chart-component `wkpNorm 2 2` via `toEuclidean`
    chain-rule), plus a first-correction `fderiv`-of-raw piece (controlled
    via `fderiv_raw_symm_pointwise_bound`) plus a second-correction
    raw-squared piece (controlled by
    `int_raw_α_symm_sq_le_card_sq_mul_wtwokTwoNorm_sq`).

(ii) Aggregating over the (finite) `chartAtlasPOU_finset` then yields the
overall constant.

The full proof is detailed and runs ~1500-2500 lines (mainly bookkeeping of
ENNReal-of-Real conversions, AEMeasurability arguments for the three
integrand pieces, and `lintegral_add_left'` splits for the binary/ternary
sums inside the integrand). It is broken out into a separate sub-substep
to respect the per-substep line budget. -/

/-! ## Auxiliary integral bounds for the B'.3b / B'.3c correction pieces -/

/-- The squared `eLpNorm` of the chart-pulled raw chart-frame scalar
`y ↦ raw α IJ ((extChartAt α).symm ((toEuclidean).symm y))` equals the
lintegral over the chart target of `ofReal` of its square. -/
private lemma sq_eLpNorm_raw_symm_eq_lintegral
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (eLpNorm
        (fun y : EuclN =>
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) ^ 2 =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
          ∂(volume : Measure EuclN) := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
  refine lintegral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change ‖tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ 2 =
      ENNReal.ofReal ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
  rw [show ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) =
      ‖tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 from by
    rw [Real.norm_eq_abs, sq_abs]]
  rw [show ENNReal.ofReal
      (‖tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
        (ENNReal.ofReal
          ‖tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) ^ 2 from
    ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [ofReal_norm_eq_enorm]

/-- The `eLpNorm`-squared of the chart-pulled raw chart-frame scalar is bounded
by `|finset|² · wtwokTwoNorm²`. -/
private lemma eLpNorm_sq_raw_symm_le_wtwokTwoNorm_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (eLpNorm
        (fun y : EuclN =>
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
        (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
          (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2) := by
  classical
  rw [sq_eLpNorm_raw_symm_eq_lintegral
    (I := I) (M := M) g r s T α Idx Jdx]
  refine (int_raw_α_symm_sq_le_card_sq_mul_wtwokTwoNorm_sq
    (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx).trans ?_
  have hN_eq : ENNReal.ofReal
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) =
        ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) := by
    rw [ENNReal.ofReal_natCast]
  rw [hN_eq]

/-- For each `α` and `IJ`, the integral over `chartTargetEuclid α` of
`ofReal(‖fderiv (chartComp β IJ) y‖²)` is bounded by `(wkpNorm 2 2 chartComp
β IJ chartTarget β)²`. Domain enlargement: extend the integral from
`chartTarget α` to the whole space (since the integrand vanishes outside
`tsupport (chartComp β IJ) ⊆ chartTarget β`), then apply the Sobolev bridge
`chartTarget_fderiv_eLpNorm_le_wkpNorm_two`. -/
private lemma int_fderiv_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖fderiv ℝ
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  set fd : EuclN → ℝ := fun y => ‖fderiv ℝ
    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ with hfd_def
  -- Step 1: extend the domain.
  have h_le_full :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) ≤
        ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) :=
    setLIntegral_le_lintegral _ _
  refine h_le_full.trans ?_
  -- Step 2: `fd` vanishes outside `tsupport (chartComp β IJ) ⊆ chartTarget β`.
  have h_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_fd_supp : tsupport fd ⊆ chartTargetEuclid (I := I) (M := M) β := by
    -- Use Mathlib's `tsupport_fderiv_subset` (composed with norm).
    have h_norm_subset : tsupport fd ⊆
        tsupport (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)) := by
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq, hfd_def] at hy
      simp only [Function.mem_support, ne_eq]
      intro hzero
      apply hy
      rw [hzero, norm_zero]
    refine (h_norm_subset.trans (tsupport_fderiv_subset _)).trans h_supp
  -- Step 3: rewrite the full lintegral as a restricted lintegral on chartTarget β.
  have h_chartTarget_β_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) β
  have h_full_eq_β :
      ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
            ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    have h_indicator_eq : (fun y => ENNReal.ofReal (fd y ^ 2)) =
        (chartTargetEuclid (I := I) (M := M) β).indicator
          (fun y => ENNReal.ofReal (fd y ^ 2)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) β
      · rw [Set.indicator_of_mem hy]
      · have hy_notin_supp : y ∉ tsupport fd := fun hin => hy (h_fd_supp hin)
        have hy_zero : fd y = 0 := by
          by_contra hne
          have hy_in_supp : y ∈ Function.support fd := by
            simp only [Function.mem_support, ne_eq]; exact hne
          exact hy_notin_supp (subset_tsupport _ hy_in_supp)
        rw [hy_zero, Set.indicator_of_notMem hy]
        simp
    conv_lhs => rw [h_indicator_eq]
    rw [MeasureTheory.lintegral_indicator h_chartTarget_β_meas]
  rw [h_full_eq_β]
  -- Step 4: rewrite the restricted lintegral as `(eLpNorm fd 2 restricted)²`.
  have h_sq_eLp_eq : (eLpNorm fd 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β))) ^ 2 =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change ‖fd y‖ₑ ^ 2 = ENNReal.ofReal (fd y ^ 2)
    rw [show (fd y ^ 2) = ‖fd y‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show ENNReal.ofReal (‖fd y‖ ^ 2) = (ENNReal.ofReal ‖fd y‖) ^ 2 from
      ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ofReal_norm_eq_enorm]
  rw [← h_sq_eLp_eq]
  -- Step 5: apply `chartTarget_fderiv_eLpNorm_le_wkpNorm_two`.
  have h_β_open : IsOpen (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T β Idx Jdx
  have h_cc :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T β Idx Jdx
  have h_supp_β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_fderiv_eLpNorm_le_wkpNorm_two
      (d := Module.finrank ℝ E) (Ω := chartTargetEuclid (I := I) (M := M) β)
      h_β_open h_smooth h_cc h_supp_β
  exact pow_le_pow_left' h_bridge 2

/-- The per-α-(Idx, Jdx) `chartTarget α` integral of
`‖iteratedFDeriv 2 (chartComp β IJ) y‖²` is bounded by
`(wkpNorm 2 2 chartComp β IJ chartTarget β)²`. The structure mirrors
`int_fderiv_tensorChartComp_β_sq_le_wkpNorm_two_sq`. -/
private lemma int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      (wkpNorm (d := Module.finrank ℝ E) 2 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  set fd : EuclN → ℝ := fun y => ‖iteratedFDeriv ℝ 2
    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ with hfd_def
  -- Step 1: extend the domain.
  have h_le_full :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) ≤
        ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) :=
    setLIntegral_le_lintegral _ _
  refine h_le_full.trans ?_
  -- Step 2: `fd` vanishes outside `tsupport (chartComp β IJ) ⊆ chartTarget β`.
  have h_supp : tsupport (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_fd_supp : tsupport fd ⊆ chartTargetEuclid (I := I) (M := M) β := by
    -- Use Mathlib's `tsupport_iteratedFDeriv_subset` (composed with norm).
    have h_norm_subset : tsupport fd ⊆
        tsupport (iteratedFDeriv ℝ 2
          (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)) := by
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq, hfd_def] at hy
      simp only [Function.mem_support, ne_eq]
      intro hzero
      apply hy
      rw [hzero, norm_zero]
    refine (h_norm_subset.trans (tsupport_iteratedFDeriv_subset 2)).trans h_supp
  -- Step 3: rewrite the full lintegral as a restricted lintegral on chartTarget β.
  have h_chartTarget_β_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) β
  have h_full_eq_β :
      ∫⁻ y, ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
            ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    have h_indicator_eq : (fun y => ENNReal.ofReal (fd y ^ 2)) =
        (chartTargetEuclid (I := I) (M := M) β).indicator
          (fun y => ENNReal.ofReal (fd y ^ 2)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) β
      · rw [Set.indicator_of_mem hy]
      · have hy_notin_supp : y ∉ tsupport fd := fun hin => hy (h_fd_supp hin)
        have hy_zero : fd y = 0 := by
          by_contra hne
          have hy_in_supp : y ∈ Function.support fd := by
            simp only [Function.mem_support, ne_eq]; exact hne
          exact hy_notin_supp (subset_tsupport _ hy_in_supp)
        rw [hy_zero, Set.indicator_of_notMem hy]
        simp
    conv_lhs => rw [h_indicator_eq]
    rw [MeasureTheory.lintegral_indicator h_chartTarget_β_meas]
  rw [h_full_eq_β]
  -- Step 4: rewrite as `(eLpNorm fd 2 restricted)²`.
  have h_sq_eLp_eq : (eLpNorm fd 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β))) ^ 2 =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
          ENNReal.ofReal (fd y ^ 2) ∂(volume : Measure EuclN) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change ‖fd y‖ₑ ^ 2 = ENNReal.ofReal (fd y ^ 2)
    rw [show (fd y ^ 2) = ‖fd y‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show ENNReal.ofReal (‖fd y‖ ^ 2) = (ENNReal.ofReal ‖fd y‖) ^ 2 from
      ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [ofReal_norm_eq_enorm]
  rw [← h_sq_eLp_eq]
  -- Step 5: apply `chartTarget_iteratedFDeriv_two_eLpNorm_le_wkpNorm_two`.
  have h_β_open : IsOpen (chartTargetEuclid (I := I) (M := M) β) :=
    chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_smooth : ContDiff ℝ ∞
      (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T β Idx Jdx
  have h_cc :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T β Idx Jdx
  have h_supp_β :=
    tensorChartComp_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) g r s T β Idx Jdx
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chartTarget_iteratedFDeriv_two_eLpNorm_le_wkpNorm_two
      (d := Module.finrank ℝ E) (Ω := chartTargetEuclid (I := I) (M := M) β)
      h_β_open h_smooth h_cc h_supp_β
  exact pow_le_pow_left' h_bridge 2

/-- The per-(α, IJ) `chartTarget α` integral of the squared norm of the
iterated 2-derivative of `POU(α) · raw α IJ ∘ symm_α` is bounded by
`‖toEuclidean‖⁴ · (wkpNorm 2 2 chartComp α IJ chartTarget α)²`. This combines
the chain rule lemma `iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq`
with `int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq`. -/
private lemma int_iteratedFDeriv_two_pou_raw_α_symm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e'))
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal ((‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2) *
        (wkpNorm (d := Module.finrank ℝ E) 2 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
  classical
  set NtoE_sq2 : ℝ := (‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) ^ 2 with hNtoE_sq2_def
  have hNtoE_sq2_nn : 0 ≤ NtoE_sq2 := sq_nonneg _
  -- Pointwise bound from `iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq`.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
            (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm e') *
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm e'))
            ((toEuclidean (E := E)).symm y)‖ ^ 2) ≤
        ENNReal.ofReal NtoE_sq2 *
          ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2) := by
    intro y hy
    have h_real := iteratedFDeriv_two_pou_raw_symm_sq_le_iteratedFDeriv_two_chartComp_sq
      (I := I) (M := M) g r s T α Idx Jdx y hy
    have h_step :=
      ENNReal.ofReal_le_ofReal h_real
    refine h_step.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hNtoE_sq2_nn]
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2
              (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                  ((extChartAt I α).symm e') *
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm e'))
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal NtoE_sq2 *
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y‖ ^ 2)
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  refine h_int_mono.trans ?_
  -- Pull constant out.
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  -- Bound by `(wkpNorm 2 2 ...)²` via `int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq`.
  exact int_iteratedFDeriv_two_tensorChartComp_β_sq_le_wkpNorm_two_sq
    (I := I) (M := M) g r s T α α Idx Jdx

/-- The per-(α, IJ) `chartTarget α` integral of the squared norm of the
fderiv of `raw α IJ ∘ symm_α` (via `fderiv_raw_symm_pointwise_bound`) is
bounded by `|finset| · ‖toEucl‖² · |finset| · wtwokTwoNorm²`. -/
private lemma int_fderiv_raw_α_symm_sq_le_wtwokTwoNorm_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume : Measure EuclN) ≤
      ENNReal.ofReal
          (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
            ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ 2) *
        (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
          (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2) := by
  classical
  set Nfin : ℝ := ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) with hNfin_def
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNfin_nn : 0 ≤ Nfin := Nat.cast_nonneg _
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  have hConst_nn : 0 ≤ Nfin * NtoE ^ 2 := mul_nonneg hNfin_nn (sq_nonneg _)
  -- Pointwise bound from `fderiv_raw_symm_pointwise_bound`.
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (‖fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2) ≤
        ENNReal.ofReal
          (Nfin * NtoE ^ 2 *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ‖fderiv ℝ
                (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2) := by
    intro y hy
    refine ENNReal.ofReal_le_ofReal ?_
    have h_raw := fderiv_raw_symm_pointwise_bound
      (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx y hy
    simpa [Nfin, NtoE, hNfin_def, hNtoE_def] using h_raw
  -- Step 1: integrate.
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (‖fderiv ℝ
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (Nfin * NtoE ^ 2 *
                ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
                  ‖fderiv ℝ
                    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  refine h_int_mono.trans ?_
  -- Step 2: split `ofReal(C · Σ_β ...)` and integrate per-β.
  have h_split_pt : ∀ y : EuclN,
      ENNReal.ofReal
          (Nfin * NtoE ^ 2 *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ‖fderiv ℝ
                (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2) =
        ENNReal.ofReal (Nfin * NtoE ^ 2) *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ENNReal.ofReal
              (‖fderiv ℝ
                (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2) := by
    intro y
    rw [ENNReal.ofReal_mul hConst_nn]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  have h_fderiv_meas : ∀ β,
      Measurable (fun y : EuclN =>
        ENNReal.ofReal
          (‖fderiv ℝ
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)) := by
    intro β
    exact fderiv_tensorChartComp_sq_ofReal_measurable
      (I := I) (M := M) g r s T β Idx Jdx
  have h_int_split :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (Nfin * NtoE ^ 2 *
              ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
                ‖fderiv ℝ
                  (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
          ∂(volume : Measure EuclN) =
        ENNReal.ofReal (Nfin * NtoE ^ 2) *
          ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (‖fderiv ℝ
                    (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
                ∂(volume : Measure EuclN) := by
    rw [lintegral_congr (fun y => h_split_pt y)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_finset_sum _ (fun β _ => h_fderiv_meas β)
  rw [h_int_split]
  -- Step 3: bound per-β by `(wkpNorm 2 2 chartComp β IJ chartTarget β)² ≤ wtwokTwoNorm²`.
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  have h_per_β : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (‖fderiv ℝ
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx) y‖ ^ 2)
          ∂(volume : Measure EuclN) ≤ W := by
    intro β _
    refine (int_fderiv_tensorChartComp_β_sq_le_wkpNorm_two_sq
      (I := I) (M := M) g r s T α β Idx Jdx).trans ?_
    exact wkpNorm_two_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T β Idx Jdx
  refine (Finset.sum_le_sum h_per_β).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Aggregated B'.3 per-α bounds on the three integrals -/

/-- The per-α B'.3a bound aggregated: the V-integral
`∫_α ofReal(POU² · ‖repr‖²)` is bounded by `K_a · cardIdx · cardJdx · W` for an
explicit `K_a` from `chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq`. -/
private lemma per_alpha_V_int_le_wtwokTwoNorm_sq
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
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨K_a, hK_a_nn, hK_a_bound⟩ :=
    chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
      (I := I) (M := M) g r s α
  set cIcJ : ℝ :=
    ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ) *
      ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ)
    with hcIcJ_def
  have hcIcJ_nn : 0 ≤ cIcJ := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨K_a * cIcJ, mul_nonneg hK_a_nn hcIcJ_nn, ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  refine (hK_a_bound T).trans ?_
  rw [ENNReal.ofReal_mul hK_a_nn]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  -- Bound Σ_IJ (wkpNorm 0 2 chartComp α IJ)² ≤ cIcJ · W using `wkpNorm_zero_sq_le_wtwokTwoNorm_sq`.
  have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      (wkpNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W :=
    fun Idx Jdx => wkpNorm_zero_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T α Idx Jdx
  -- Triple-sum (over (Idx, Jdx)) — sum of cIcJ terms, each ≤ W.
  calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2
      ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
        refine Finset.sum_le_sum (fun Idx _ => ?_)
        refine Finset.sum_le_sum (fun Jdx _ => ?_)
        exact h_per_IJ Idx Jdx
    _ = ENNReal.ofReal cIcJ * W := by
        rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
            ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              (((Finset.univ : Finset
                  (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) * W) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_const, nsmul_eq_mul]]
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [show ENNReal.ofReal cIcJ =
            ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
              ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞)
          from by
          rw [hcIcJ_def, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
        ring

/-- The per-α B'.3b bound aggregated: the F-integral
`∫_α ofReal(POU² · ‖fderiv (repr ∘ symm)‖²)` is bounded by `K_b · (cardIdx · cardJdx + cardIdx · cardJdx · |finset|²) · W`. -/
private lemma per_alpha_F_int_le_wtwokTwoNorm_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
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
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨K_b, hK_b_nn, hK_b_bound⟩ :=
    chartTargetPouWeightedL2NormSq_fderiv_repr_le_sum_chartComp_data
      (I := I) (M := M) g r s α
  set cIcJ : ℝ :=
    ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ) *
      ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ)
    with hcIcJ_def
  have hcIcJ_nn : 0 ≤ cIcJ := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set Nfin : ℝ := ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) with hNfin_def
  have hNfin_nn : 0 ≤ Nfin := Nat.cast_nonneg _
  refine ⟨K_b * (cIcJ + cIcJ * Nfin ^ 2), ?_, ?_⟩
  · refine mul_nonneg hK_b_nn ?_
    refine add_nonneg hcIcJ_nn (mul_nonneg hcIcJ_nn (sq_nonneg _))
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  refine (hK_b_bound T).trans ?_
  -- The B'.3b RHS has form `ofReal K_b · (Σ_IJ (wkpNorm 1 2 ...)² + Σ_IJ (eLpNorm raw_∘sym 2)²)`.
  rw [ENNReal.ofReal_mul hK_b_nn]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  -- Bound (a + b) ≤ (cIcJ · W) + (cIcJ · |finset|² · W) = ofReal (cIcJ · (1 + |finset|²)) · W.
  -- Each summand bounded.
  have h_a_bound :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (wkpNorm (d := Module.finrank ℝ E) 1 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
        ENNReal.ofReal cIcJ * W := by
    have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (wkpNorm (d := Module.finrank ℝ E) 1 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤ W :=
      fun Idx Jdx => wkpNorm_one_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T α Idx Jdx
    calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (wkpNorm (d := Module.finrank ℝ E) 1 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2
        ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = ENNReal.ofReal cIcJ * W := by
          rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), W) =
              ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
                (((Finset.univ : Finset
                    (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) * W) from by
            refine Finset.sum_congr rfl (fun _ _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [show ENNReal.ofReal cIcJ =
              ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞)
            from by
            rw [hcIcJ_def, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
          ring
  -- Second piece: ∑_IJ (eLpNorm raw_∘sym 2)² ≤ cIcJ · |finset|² · W.
  have h_b_bound :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          eLpNorm
              (fun y : EuclN =>
                tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2 ≤
        ENNReal.ofReal (cIcJ * Nfin ^ 2) * W := by
    have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm
            (fun y : EuclN =>
              tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
            (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) :=
      fun Idx Jdx => eLpNorm_sq_raw_symm_le_wtwokTwoNorm_sq
        (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx
    calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
                (fun y : EuclN =>
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) 2
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2
        ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = ENNReal.ofReal (cIcJ * Nfin ^ 2) * W := by
          rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W)) =
              ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
                (((Finset.univ : Finset
                    (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                    (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W))) from by
            refine Finset.sum_congr rfl (fun _ _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]]
          rw [Finset.sum_const, nsmul_eq_mul]
          have hNfin_sq_eq : ENNReal.ofReal (Nfin ^ 2) =
              ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) := by
            rw [hNfin_def]
            rw [show ((((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) ^ 2) : ℝ) =
                ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
                  ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) from by ring]
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            rw [ENNReal.ofReal_natCast]
          have hcIcJNfin_eq : ENNReal.ofReal (cIcJ * Nfin ^ 2) =
              ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                    ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞)) := by
            rw [ENNReal.ofReal_mul hcIcJ_nn, hNfin_sq_eq]
            rw [hcIcJ_def, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          rw [hcIcJNfin_eq]
          ring
  -- Combine: (a + b) ≤ ofReal cIcJ · W + ofReal (cIcJ · Nfin²) · W
  --         = ofReal (cIcJ + cIcJ · Nfin²) · W.
  refine (add_le_add h_a_bound h_b_bound).trans ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_add hcIcJ_nn (mul_nonneg hcIcJ_nn (sq_nonneg _))]

/-- The per-α B'.3c bound aggregated: the I-integral
`∫_α ofReal(POU² · ‖iteratedFDeriv 2 (repr ∘ symm)‖²)` is bounded by a
multiple of `W`. -/
private lemma per_alpha_I_int_le_wtwokTwoNorm_sq
    (h_atlas_strong :
      DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                    (tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨K_c, hK_c_nn, hK_c_bound⟩ :=
    chartTargetPouWeightedL2NormSq_iteratedFDeriv_two_repr_le_sum_chartComp_data
      (I := I) (M := M) g r s α
  set cIcJ : ℝ :=
    ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ) *
      ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ)
    with hcIcJ_def
  have hcIcJ_nn : 0 ≤ cIcJ := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set Nfin : ℝ := ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) with hNfin_def
  have hNfin_nn : 0 ≤ Nfin := Nat.cast_nonneg _
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  -- Constant: K_c · (cIcJ · NtoE^4 + cIcJ · Nfin² · NtoE² + cIcJ · Nfin²)
  refine ⟨K_c * (cIcJ * (NtoE ^ 2) ^ 2 +
    Nfin * NtoE ^ 2 * (cIcJ * Nfin) +
    cIcJ * Nfin ^ 2), ?_, ?_⟩
  · refine mul_nonneg hK_c_nn ?_
    positivity
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  refine (hK_c_bound T).trans ?_
  -- B'.3c gives: LHS ≤ ofReal K_c · (∑_IJ ∫wInt + ∑_IJ ∫fInt + ∑_IJ ∫rInt).
  -- We bound each summand and then aggregate.
  rw [ENNReal.ofReal_mul hK_c_nn]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  -- Three sums to bound.
  -- (a) wInt: ∑_IJ ∫_α ‖iteratedFDeriv 2 (POU·raw α IJ ∘ symm)‖² ≤ cIcJ · NtoE^4 · W.
  -- (b) fInt: ∑_IJ ∫_α ‖fderiv (raw α IJ ∘ symm)‖² ≤ cIcJ · |finset| · NtoE² · |finset| · W.
  -- (c) rInt: ∑_IJ ∫_α ‖raw α IJ ∘ symm‖² ≤ cIcJ · |finset|² · W.
  -- (a)
  have h_a_bound :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (‖iteratedFDeriv ℝ 2
                  (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                      ((extChartAt I α).symm e') *
                    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                      ((extChartAt I α).symm e'))
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (cIcJ * (NtoE ^ 2) ^ 2) * W := by
    have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (‖iteratedFDeriv ℝ 2
                (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                    ((extChartAt I α).symm e') *
                  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm e'))
                ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal ((NtoE ^ 2) ^ 2) * W := by
      intro Idx Jdx
      refine (int_iteratedFDeriv_two_pou_raw_α_symm_sq_le
        (I := I) (M := M) g r s T α Idx Jdx).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
      exact wkpNorm_two_sq_le_wtwokTwoNorm_sq (I := I) (M := M) g r s T α Idx Jdx
    calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (‖iteratedFDeriv ℝ 2
                    (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                        ((extChartAt I α).symm e') *
                      tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                        ((extChartAt I α).symm e'))
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)
        ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal ((NtoE ^ 2) ^ 2) * W := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = ENNReal.ofReal (cIcJ * (NtoE ^ 2) ^ 2) * W := by
          rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
                ENNReal.ofReal ((NtoE ^ 2) ^ 2) * W) =
              ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
                (((Finset.univ : Finset
                    (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  (ENNReal.ofReal ((NtoE ^ 2) ^ 2) * W)) from by
            refine Finset.sum_congr rfl (fun _ _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul hcIcJ_nn]
          rw [hcIcJ_def]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          ring
  -- (b)
  have h_b_bound :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (‖fderiv ℝ
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                    (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (Nfin * NtoE ^ 2 * (cIcJ * Nfin)) * W := by
    have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (‖fderiv ℝ
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal (Nfin * NtoE ^ 2) *
            (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) :=
      fun Idx Jdx => int_fderiv_raw_α_symm_sq_le_wtwokTwoNorm_sq
        (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx
    calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (‖fderiv ℝ
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                      (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)
        ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal (Nfin * NtoE ^ 2) *
                (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = ENNReal.ofReal (Nfin * NtoE ^ 2 * (cIcJ * Nfin)) * W := by
          rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
                ENNReal.ofReal (Nfin * NtoE ^ 2) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W)) =
              ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
                (((Finset.univ : Finset
                    (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  (ENNReal.ofReal (Nfin * NtoE ^ 2) *
                    (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W))) from by
            refine Finset.sum_congr rfl (fun _ _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]]
          rw [Finset.sum_const, nsmul_eq_mul]
          have h_cIcJ_ENNReal :
              ENNReal.ofReal cIcJ =
                ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) := by
            rw [hcIcJ_def, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            simp [ENNReal.ofReal_natCast]
          have h_Nfin_ENNReal :
              ENNReal.ofReal Nfin =
                ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) := by
            rw [hNfin_def, ENNReal.ofReal_natCast]
          rw [ENNReal.ofReal_mul (mul_nonneg hNfin_nn (sq_nonneg _))]
          rw [ENNReal.ofReal_mul hcIcJ_nn]
          rw [h_cIcJ_ENNReal, h_Nfin_ENNReal]
          ring
  -- (c)
  have h_c_bound :
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
              ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (cIcJ * Nfin ^ 2) * W := by
    have h_per_IJ : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ∂(volume : Measure EuclN) ≤
          ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
            (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) := by
      intro Idx Jdx
      have := int_raw_α_symm_sq_le_card_sq_mul_wtwokTwoNorm_sq
        (I := I) (M := M) h_atlas_strong g r s T α Idx Jdx
      refine this.trans ?_
      have hN_eq : ENNReal.ofReal
          ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) =
            ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) := by
        rw [ENNReal.ofReal_natCast]
      rw [hN_eq]
    calc ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
                ∂(volume : Measure EuclN)
        ≤ ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W) := by
          refine Finset.sum_le_sum (fun Idx _ => ?_)
          refine Finset.sum_le_sum (fun Jdx _ => ?_)
          exact h_per_IJ Idx Jdx
      _ = ENNReal.ofReal (cIcJ * Nfin ^ 2) * W := by
          rw [show (∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W)) =
              ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
                (((Finset.univ : Finset
                    (Fin s → Fin (Module.finrank ℝ E))).card : ℝ≥0∞) *
                  (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) *
                    (((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ≥0∞) * W))) from by
            refine Finset.sum_congr rfl (fun _ _ => ?_)
            rw [Finset.sum_const, nsmul_eq_mul]]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul hcIcJ_nn]
          rw [hcIcJ_def]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [show (Nfin ^ 2 : ℝ) = Nfin * Nfin from by ring]
          rw [ENNReal.ofReal_mul hNfin_nn]
          rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, hNfin_def, ENNReal.ofReal_natCast]
          ring
  -- Aggregate.
  refine (add_le_add (add_le_add h_a_bound h_b_bound) h_c_bound).trans ?_
  rw [← add_mul, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  have h1_nn : 0 ≤ cIcJ * (NtoE ^ 2) ^ 2 := mul_nonneg hcIcJ_nn (sq_nonneg _)
  have h2_nn : 0 ≤ Nfin * NtoE ^ 2 * (cIcJ * Nfin) := by positivity
  have h3_nn : 0 ≤ cIcJ * Nfin ^ 2 := mul_nonneg hcIcJ_nn (sq_nonneg _)
  rw [show ENNReal.ofReal
      (cIcJ * (NtoE ^ 2) ^ 2 + Nfin * NtoE ^ 2 * (cIcJ * Nfin) + cIcJ * Nfin ^ 2) =
      ENNReal.ofReal (cIcJ * (NtoE ^ 2) ^ 2 + Nfin * NtoE ^ 2 * (cIcJ * Nfin)) +
        ENNReal.ofReal (cIcJ * Nfin ^ 2) from
    ENNReal.ofReal_add (add_nonneg h1_nn h2_nn) h3_nn]
  rw [show ENNReal.ofReal (cIcJ * (NtoE ^ 2) ^ 2 + Nfin * NtoE ^ 2 * (cIcJ * Nfin)) =
      ENNReal.ofReal (cIcJ * (NtoE ^ 2) ^ 2) +
        ENNReal.ofReal (Nfin * NtoE ^ 2 * (cIcJ * Nfin)) from
    ENNReal.ofReal_add h1_nn h2_nn]

/-! ## Per-α aggregate: chartSobolevRawNormPou summand ≤ K_α · wtwokTwoNorm² -/

/-- **Per-α bound for the chart-Sobolev raw-norm summand.** For each `α : M`,
the per-α summand of `chartSobolevRawNormPou` is bounded above by an explicit
non-negative constant `K_α` (depending only on `g`, `α`, `(r, s)`, and the
chart atlas) times `(wtwokTwoNorm g 1 T)²`. -/
private lemma per_alpha_chartSobolev_summand_le_wtwokTwoNorm_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M =>
                    rawTensorConnLap (I := I) g r s
                      (fun z : M => T.toSection z) b)
                  y)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  -- Pointwise bound via `per_alpha_pointwise_bound`.
  obtain ⟨K_2b, hK_2b_nn, hK_2b_bound⟩ :=
    per_alpha_pointwise_bound (I := I) (M := M) h_atlas h_atlas_strong g r s α
  -- The three per-α V/F/I bounds.
  obtain ⟨Cv, hCv_nn, hCv_bound⟩ :=
    per_alpha_V_int_le_wtwokTwoNorm_sq (I := I) (M := M) g r s α
  obtain ⟨Cf, hCf_nn, hCf_bound⟩ :=
    per_alpha_F_int_le_wtwokTwoNorm_sq (I := I) (M := M) h_atlas_strong g r s α
  obtain ⟨Ci, hCi_nn, hCi_bound⟩ :=
    per_alpha_I_int_le_wtwokTwoNorm_sq (I := I) (M := M) h_atlas_strong g r s α
  refine ⟨K_2b * (Cv + Cf + Ci), ?_, ?_⟩
  · refine mul_nonneg hK_2b_nn ?_
    linarith
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  -- Pointwise reduction: ofReal(ρ² · X) ≤ ofReal K_2b · (ofReal(ρ²) · ofReal(V²) + ofReal(ρ²) · ofReal(F²) + ofReal(ρ²) · ofReal(I²)).
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M =>
              rawTensorConnLap (I := I) g r s
                (fun z : M => T.toSection z) b) y) ≤
        ENNReal.ofReal K_2b * (
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) +
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖fderiv ℝ
                  (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) +
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖iteratedFDeriv ℝ 2
                  (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)) := by
    intro y hy
    have h_real := hK_2b_bound T y hy
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
        (fun z : M => T.toSection z)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2
    set F : ℝ := ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
        ((toEuclidean (E := E)).symm y)‖ ^ 2
    set Inorm : ℝ := ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
        ((toEuclidean (E := E)).symm y)‖ ^ 2
    set X : ℝ := tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M =>
          rawTensorConnLap (I := I) g r s
            (fun z : M => T.toSection z) b) y
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
    have hX_nn : 0 ≤ X :=
      tensorTrivProjPushedNormSq_nonneg (I := I) (M := M) g r s α _ y
    have hV_nn : 0 ≤ V := sq_nonneg _
    have hF_nn : 0 ≤ F := sq_nonneg _
    have hI_nn : 0 ≤ Inorm := sq_nonneg _
    rw [show ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal X = ENNReal.ofReal (ρ ^ 2 * X) from
      (ENNReal.ofReal_mul hρ_sq_nn).symm]
    -- The real bound: ρ² · X ≤ K_2b · (ρ² · (V + F + Inorm)).
    have h_real' : ρ ^ 2 * X ≤ K_2b * (ρ ^ 2 * V + ρ ^ 2 * F + ρ ^ 2 * Inorm) := by
      have h := h_real
      nlinarith [h, sq_nonneg ρ]
    refine (ENNReal.ofReal_le_ofReal h_real').trans ?_
    have h1_nn : 0 ≤ ρ ^ 2 * V := mul_nonneg hρ_sq_nn hV_nn
    have h2_nn : 0 ≤ ρ ^ 2 * F := mul_nonneg hρ_sq_nn hF_nn
    have h3_nn : 0 ≤ ρ ^ 2 * Inorm := mul_nonneg hρ_sq_nn hI_nn
    have hSum_nn : 0 ≤ ρ ^ 2 * V + ρ ^ 2 * F + ρ ^ 2 * Inorm := by linarith
    rw [ENNReal.ofReal_mul hK_2b_nn]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    rw [ENNReal.ofReal_add (add_nonneg h1_nn h2_nn) h3_nn]
    rw [ENNReal.ofReal_add h1_nn h2_nn]
    rw [ENNReal.ofReal_mul hρ_sq_nn, ENNReal.ofReal_mul hρ_sq_nn,
      ENNReal.ofReal_mul hρ_sq_nn]
  -- Integrate the pointwise bound.
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  set V_int : ℝ≥0∞ := ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
      ENNReal.ofReal
        (‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
      ∂(volume : Measure EuclN) with hV_int_def
  set F_int : ℝ≥0∞ := ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
      ENNReal.ofReal
        (‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
      ∂(volume : Measure EuclN) with hF_int_def
  set I_int : ℝ≥0∞ := ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
      ENNReal.ofReal
        (‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
      ∂(volume : Measure EuclN) with hI_int_def
  -- AEMeasurability of V_y, F_y, I_y on the restricted measure (continuity-based).
  have h_pou_sym_contOn : ContinuousOn (fun y : EuclN =>
      ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pou_cont : Continuous ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α).contMDiff.continuous
    have h_sym_cont : ContinuousOn (fun y : EuclN =>
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine (continuousOn_extChartAt_symm (I := I) α).comp
        (toEuclidean (E := E)).symm.continuous.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    exact h_pou_cont.continuousOn.comp h_sym_cont (Set.mapsTo_univ _ _)
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_2le_inf : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  -- ContDiffOn ∞ from R_contDiffOn_goodSet.
  have h_goodSet_eq : chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  have h_repr_sym_cd : ContDiffOn ℝ ∞ (tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
      (extChartAt I α).target := by
    have h_cd_good :=
      DifferentialGeometry.Integral.Connection.R_contDiffOn_goodSet
        (I := I) (M := M) g r s α T
    have h_target_eq : (extChartAt I α) '' (extChartAt I α).source =
        (extChartAt I α).target := by
      rw [PartialEquiv.image_source_eq_target]
    rw [show (extChartAt I α).target =
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α from by
      rw [h_goodSet_eq, h_target_eq]]
    exact h_cd_good
  have h_V_aeMeas : AEMeasurable (fun y : EuclN =>
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (‖tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_repr_sym_cont : ContinuousOn (fun y : EuclN =>
        tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro y hy
      have he : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
        exact hy
      have h_diff := repr_symm_differentiableAt (I := I) (M := M) g r s T α
        (e := (toEuclidean (E := E)).symm y) he
      have h_cont_at_e : ContinuousAt (fun e' : E =>
          tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ((extChartAt I α).symm e'))
          ((toEuclidean (E := E)).symm y) := h_diff.continuousAt
      have h_sym_at : ContinuousAt
          (fun y' : EuclN => (toEuclidean (E := E)).symm y') y :=
        (toEuclidean (E := E)).symm.continuous.continuousAt
      exact (h_cont_at_e.comp h_sym_at).continuousWithinAt
    have h_prod_contOn : ContinuousOn (fun y : EuclN =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
        ‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContinuousOn.mul (h_pou_sym_contOn.pow 2) ((h_repr_sym_cont.norm).pow 2)
    have h_prod_ae : AEMeasurable (fun y : EuclN =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
        ‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_prod_contOn.aemeasurable h_chartTarget_meas
    have h_eq : (fun y : EuclN =>
        ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (‖tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) =
        (fun y : EuclN =>
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
      funext y; rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_eq]
    exact ENNReal.measurable_ofReal.comp_aemeasurable h_prod_ae
  have h_F_aeMeas : AEMeasurable (fun y : EuclN =>
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (‖fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_fderiv_contOn : ContinuousOn (fun e' : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e')
        (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e' := by
        refine (h_repr_sym_cd.contDiffAt (h_open.mem_nhds he')).of_le ?_
        exact_mod_cast h_2le_inf
      exact (h_cd_at.continuousAt_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).continuousWithinAt
    have h_fderiv_sym_contOn : ContinuousOn (fun y : EuclN =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_fderiv_contOn.comp
        (toEuclidean (E := E)).symm.continuous.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_prod_contOn : ContinuousOn (fun y : EuclN =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
        ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContinuousOn.mul (h_pou_sym_contOn.pow 2) ((h_fderiv_sym_contOn.norm).pow 2)
    have h_prod_ae : AEMeasurable _
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_prod_contOn.aemeasurable h_chartTarget_meas
    have h_eq : (fun y : EuclN =>
        ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (‖fderiv ℝ
                (tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
        (fun y : EuclN =>
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖fderiv ℝ
                  (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)) := by
      funext y; rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_eq]
    exact ENNReal.measurable_ofReal.comp_aemeasurable h_prod_ae
  have h_I_aeMeas : AEMeasurable (fun y : EuclN =>
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (‖iteratedFDeriv ℝ 2
              (tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_iter_contOn : ContinuousOn (fun e' : E =>
        iteratedFDeriv ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e')
        (extChartAt I α).target := by
      intro e' he'
      have h_cd_at : ContDiffAt ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm) e' := by
        refine (h_repr_sym_cd.contDiffAt (h_open.mem_nhds he')).of_le ?_
        exact_mod_cast h_2le_inf
      exact (h_cd_at.continuousAt_iteratedFDeriv (k := 2) le_rfl).continuousWithinAt
    have h_iter_sym_contOn : ContinuousOn (fun y : EuclN =>
        iteratedFDeriv ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine h_iter_contOn.comp
        (toEuclidean (E := E)).symm.continuous.continuousOn ?_
      intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_prod_contOn : ContinuousOn (fun y : EuclN =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
        ‖iteratedFDeriv ℝ 2
            (tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContinuousOn.mul (h_pou_sym_contOn.pow 2) ((h_iter_sym_contOn.norm).pow 2)
    have h_prod_ae : AEMeasurable _
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_prod_contOn.aemeasurable h_chartTarget_meas
    have h_eq : (fun y : EuclN =>
        ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
          ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2
                (tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
        (fun y : EuclN =>
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖iteratedFDeriv ℝ 2
                  (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)) := by
      funext y; rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h_eq]
    exact ENNReal.measurable_ofReal.comp_aemeasurable h_prod_ae
  -- The pointwise bound's integral.
  have h_int_le :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M =>
                  rawTensorConnLap (I := I) g r s
                    (fun z : M => T.toSection z) b) y)
          ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal K_2b * (V_int + F_int + I_int) := by
    refine (setLIntegral_mono_ae' h_chartTarget_meas
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    -- Now: ∫_α (Vy + Fy + Iy) = V_int + F_int + I_int via AEMeasurability.
    have h_VF_aeMeas := h_V_aeMeas.add h_F_aeMeas
    rw [lintegral_add_left' h_VF_aeMeas]
    rw [lintegral_add_left' h_V_aeMeas]
  -- Bound V_int, F_int, I_int by Cv · W, Cf · W, Ci · W.
  refine h_int_le.trans ?_
  refine (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (hCv_bound T) (hCf_bound T)) (hCi_bound T))
    (zero_le _)).trans ?_
  -- Now: ofReal K_2b · (ofReal Cv · W + ofReal Cf · W + ofReal Ci · W) ≤ ofReal (K_2b · (Cv+Cf+Ci)) · W.
  rw [show ENNReal.ofReal Cv * W + ENNReal.ofReal Cf * W + ENNReal.ofReal Ci * W =
      (ENNReal.ofReal Cv + ENNReal.ofReal Cf + ENNReal.ofReal Ci) * W from by ring]
  rw [show (ENNReal.ofReal Cv + ENNReal.ofReal Cf + ENNReal.ofReal Ci) =
      ENNReal.ofReal (Cv + Cf + Ci) from by
    rw [ENNReal.ofReal_add (add_nonneg hCv_nn hCf_nn) hCi_nn]
    rw [ENNReal.ofReal_add hCv_nn hCf_nn]]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul hK_2b_nn]

/-! ## Public headline B'.3 -/

/-- **Chart-Sobolev raw-norm POU aggregate bounded by `(wtwokTwoNorm g 1 T)²`.**
For a closed smooth Riemannian manifold `(M, g)` and ranks `(r, s)`, there is a
non-negative constant `C` (depending only on `g`, `(r, s)`, the chart atlas,
and the model space) such that for every smooth compactly-supported
`(r, s)`-tensor section `T`, the chart-target POU-weighted aggregate
`chartSobolevRawNormPou g r s T` is bounded above by `C · (wtwokTwoNorm g 1 T)²`.
-/
theorem chartSobolevRawNormPou_le_wtwokTwoNorm_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        chartSobolevRawNormPou (I := I) (M := M) g r s T ≤
          ENNReal.ofReal C *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  -- The constant is bounded by `|chartAtlasPOU_finset| · max_α K_α`.
  -- We use a uniform constant `K_∞`: pick K_α for each α and bound by the sum.
  -- For simplicity (over all α in the finset), we extract per-α constants and sum.
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  -- Choose a per-α constant via Classical.choose for each α ∈ Sfin.
  set Kα : M → ℝ := fun α => Classical.choose
    (per_alpha_chartSobolev_summand_le_wtwokTwoNorm_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s α) with hKα_def
  have hKα_spec : ∀ α : M, 0 ≤ Kα α ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M =>
                    rawTensorConnLap (I := I) g r s
                      (fun z : M => T.toSection z) b)
                  y)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal (Kα α) *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := fun α =>
    Classical.choose_spec
      (per_alpha_chartSobolev_summand_le_wtwokTwoNorm_sq
        (I := I) (M := M) h_atlas h_atlas_strong g r s α)
  set C : ℝ := ∑ α ∈ Sfin, Kα α with hC_def
  have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun α _ => (hKα_spec α).1)
  refine ⟨C, hC_nn, ?_⟩
  intro T
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  -- Unfold chartSobolevRawNormPou as a finite sum.
  rw [chartSobolevRawNormPou_def]
  -- Each summand ≤ ofReal (Kα α) · W.
  refine (Finset.sum_le_sum (s := Sfin) (fun α _ => (hKα_spec α).2 T)).trans ?_
  -- Now: ∑_α ofReal (Kα α) · W ≤ ofReal C · W.
  -- ∑_α ofReal (Kα α) · W = (∑_α ofReal (Kα α)) · W = ofReal C · W.
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- ∑_α ofReal (Kα α) = ofReal (∑_α Kα α) = ofReal C, using non-negativity.
  rw [hC_def]
  rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => (hKα_spec α).1)]

/-! ## Public headline E.3.1.d -/

/-- **Tensor connection Laplacian L² norm bounded by `(wtwokTwoNorm g 1 T)²`.**
For a closed smooth Riemannian manifold `(M, g)` and ranks `(r, s)`, there is a
non-negative constant `C` such that for every smooth compactly-supported
`(r, s)`-tensor section `T` with measurable squared norm, the `L²` norm of the
raw tensor connection Laplacian `rawTensorConnLap T` (taken with respect to the
Riemannian volume measure on `M`) is bounded by `C · (wtwokTwoNorm g 1 T)²`.
This composes the chart-target POU bridge
`rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou` with the chart-Sobolev
raw-norm POU aggregate bound `chartSobolevRawNormPou_le_wtwokTwoNorm_sq`. -/
theorem rawTensorConnLap_L2NormSq_le_wtwokTwoNorm_sq
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        (letI : MeasurableSpace M := borel M
         haveI : BorelSpace M := ⟨rfl⟩
         Measurable (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ ^ 2)) →
        ∫⁻ x,
            (‖rawTensorConnLap (I := I) g r s
                (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set C_bridge : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g
    with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge :=
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g
  obtain ⟨C_B3, hC_B3_nn, hC_B3_bound⟩ :=
    chartSobolevRawNormPou_le_wtwokTwoNorm_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s
  refine ⟨C_bridge * C_B3, mul_nonneg hC_bridge_nn hC_B3_nn, ?_⟩
  intro T hraw_meas
  set W : ℝ≥0∞ := (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 with hW_def
  -- The bridge gives ∫ ‖raw‖² ≤ ofReal C_bridge · chartSobolevRawNormPou.
  obtain ⟨_C_bridge', _hC_bridge'_nn, hC_bridge_bound⟩ :=
    rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou
      (I := I) (M := M) h_atlas g r s
  have h1 := hC_bridge_bound T hraw_meas
  refine h1.trans ?_
  have h2 := hC_B3_bound T
  refine (mul_le_mul_of_nonneg_left h2 (zero_le _)).trans ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul hC_bridge_nn]

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chartSobolevRawNormPou_le_wtwokTwoNorm_sq
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_L2NormSq_le_wtwokTwoNorm_sq
end Sanity

