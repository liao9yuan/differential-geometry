import DifferentialGeometry.Integral.Connection.TensorRSIntrinsicChartCLMOpNorm
import DifferentialGeometry.Integral.Connection.SlotChristoffelCorrectionOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm

/-!
# Pointwise op-norm bound for `chartTensorRSCovariantDerivative`

The chart-frame covariant derivative
`chartTensorRSCovariantDerivative r s g α T X b ∈ TensorRSSpace r s I b`
is, by definition, the difference of three pieces:

* the intrinsic Fréchet-derivative piece
  `tensorRSIntrinsicChartCLM r s α T b (X b)`,
* the sum over upper slots `k : Fin r` of
  `chartTensorRSInputSlotCorrection r s g α T X b k`,
* the sum over lower slots `l : Fin s` of
  `chartTensorRSOutputSlotCorrection r s g α T X b l`.

The triangle inequality together with the previously shipped op-norm bounds
delivers a uniform pointwise bound of the form

  `‖chartTensorRSCovariantDerivative r s g α T X b‖ ≤
      C * (max (1 + ‖X b‖) 1) ^ (max r s) *
        (‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X b‖
         + ‖T b‖)`

valid for every `b` in the closed support of the canonical chart-atlas
partition-of-unity weight at `α`. The constant `C` depends only on the chart
at `α`, the locality hypothesis, and the metric `g`; it is independent of
`T`, `X`, and `b`. The polynomial factor `(max (1+‖X b‖) 1) ^ (max r s)`
absorbs the slot-Christoffel product.

## Strategy

1. Triangle inequality on the three-term decomposition.
2. The intrinsic piece is bounded by
   `C_I * ‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X b‖`
   via `tensorRSIntrinsicChartCLM_opNorm_isBounded_on_compact`.
3. Each slot correction is bounded by
   `(max ‖chartLeviCivitaParallelCLM g α b X‖ 1) ^ n * ‖T b‖`
   pointwise (`chartTensorRSInputSlotCorrection_opNorm_le`,
   `chartTensorRSOutputSlotCorrection_opNorm_le`).
4. The slot CLM op-norm itself is bounded by `C_LC * ‖X b‖` on the POU
   tsupport via `chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport`,
   so `(max ‖Φ‖ 1) ^ n ≤ ((max C_LC 1 + 1) * (1 + ‖X b‖)) ^ n`.
5. Combining yields the headline bound. The `‖X b‖`-polynomial absorbs into
   the polynomial factor `(max (1+‖X b‖) 1) ^ (max r s)`.

Note: the slot bound is `O(‖T b‖)`, not `O(‖T b‖ · ‖X b‖)`. The factor
`max ‖Φ‖ 1 ≥ 1` retains a constant term even when `X = 0`. The headline
RHS therefore presents the natural decomposition
`(Fréchet derivative term) · ‖X b‖ + (slot Christoffel term)`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Auxiliary slot-Christoffel factor bounds -/

/-- Core slot-Christoffel bound: `max ‖Φ‖ 1 ≤ (max C_LC 1 + 1) * (1 + ‖X b‖)`,
valid whenever `‖Φ‖ ≤ C_LC * ‖X b‖` and `C_LC, ‖X b‖ ≥ 0`. -/
private lemma slot_factor_le_const_mul_one_plus_X
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (_hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    max Φ_norm 1 ≤ (max C_LC 1 + 1) * (1 + X_b_norm) := by
  have hmaxC_nn : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
  have hmaxC_ge_one : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_Φ_le_step :
      Φ_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : C_LC * X_b_norm ≤ max C_LC 1 * X_b_norm :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX_nn
    have h_b : max C_LC 1 * X_b_norm ≤ max C_LC 1 * (1 + X_b_norm) := by
      have : X_b_norm ≤ 1 + X_b_norm := by linarith
      exact mul_le_mul_of_nonneg_left this hmaxC_nn
    linarith
  have h_one_le_step :
      (1 : ℝ) ≤ max C_LC 1 * (1 + X_b_norm) := by
    have h_a : (1 : ℝ) * 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
      mul_le_mul hmaxC_ge_one h_1X_ge_one (by norm_num) hmaxC_nn
    linarith
  have h_max_step : max Φ_norm 1 ≤ max C_LC 1 * (1 + X_b_norm) :=
    max_le h_Φ_le_step h_one_le_step
  have h_expand : max C_LC 1 * (1 + X_b_norm) ≤
      (max C_LC 1 + 1) * (1 + X_b_norm) := by
    have h1 : max C_LC 1 ≤ max C_LC 1 + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h1 h_1X_nn
  linarith

/-- Raise the previous bound to the `n`-th power and split the product. -/
private lemma slot_factor_pow_le_const_mul_one_plus_X_pow (n : ℕ)
    {Φ_norm : ℝ}
    {C_LC X_b_norm : ℝ} (hC_LC_nn : 0 ≤ C_LC) (hX_nn : 0 ≤ X_b_norm)
    (hΦ : Φ_norm ≤ C_LC * X_b_norm) :
    (max Φ_norm 1) ^ n ≤
      (max C_LC 1 + 1) ^ n * (1 + X_b_norm) ^ n := by
  have h_max_nn : 0 ≤ max Φ_norm 1 := le_trans zero_le_one (le_max_right _ _)
  have h_step :=
    slot_factor_le_const_mul_one_plus_X (Φ_norm := Φ_norm)
      (C_LC := C_LC) (X_b_norm := X_b_norm) hC_LC_nn hX_nn hΦ
  have h_pow :
      (max Φ_norm 1) ^ n ≤ ((max C_LC 1 + 1) * (1 + X_b_norm)) ^ n :=
    pow_le_pow_left₀ h_max_nn h_step n
  rw [mul_pow] at h_pow
  exact h_pow

/-- Monotonic absorption of `(1 + X_b_norm) ^ n` into `(max (1+X_b_norm) 1) ^ N`
when `n ≤ N`. -/
private lemma one_plus_X_pow_le_max_pow
    {X_b_norm : ℝ} (hX_nn : 0 ≤ X_b_norm) {n N : ℕ} (hn : n ≤ N) :
    (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ N := by
  have h_1X_nn : (0 : ℝ) ≤ 1 + X_b_norm := by linarith
  have h_1X_le_max : (1 + X_b_norm) ≤ max (1 + X_b_norm) 1 := le_max_left _ _
  have h_max_ge_one : (1 : ℝ) ≤ max (1 + X_b_norm) 1 := by
    have h_1X_ge_one : (1 : ℝ) ≤ 1 + X_b_norm := by linarith
    exact le_trans h_1X_ge_one h_1X_le_max
  have h_step1 :
      (1 + X_b_norm) ^ n ≤ (max (1 + X_b_norm) 1) ^ n :=
    pow_le_pow_left₀ h_1X_nn h_1X_le_max n
  have h_step2 :
      (max (1 + X_b_norm) 1) ^ n ≤ (max (1 + X_b_norm) 1) ^ N :=
    pow_le_pow_right₀ h_max_ge_one hn
  linarith

/-- Monotonic absorption of `(max C_LC 1 + 1) ^ n` into `(max C_LC 1 + 1) ^ N`
when `n ≤ N`. -/
private lemma const_pow_le_max_pow
    {C_LC : ℝ} (_hC_LC_nn : 0 ≤ C_LC) {n N : ℕ} (hn : n ≤ N) :
    (max C_LC 1 + 1) ^ n ≤ (max C_LC 1 + 1) ^ N := by
  have h_one_le : (1 : ℝ) ≤ max C_LC 1 + 1 := by
    have : (1 : ℝ) ≤ max C_LC 1 := le_max_right _ _
    linarith
  exact pow_le_pow_right₀ h_one_le hn

/-! ## The headline bound -/

/-- **Pointwise op-norm bound** for `chartTensorRSCovariantDerivative` on the
closed support of the canonical chart-atlas partition-of-unity weight at `α`.

There exists a non-negative constant `C` such that for every `b` in the POU
tsupport, every `(r, s)`-tensor section `T`, and every tangent vector
section `X`, the chart-frame covariant derivative satisfies

  `‖chartTensorRSCovariantDerivative r s g α T X b‖ ≤
      C * (max (1 + ‖X b‖) 1) ^ (max r s) *
        (‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X b‖
         + ‖T b‖)`.

The right-hand side packages the two natural data quantities:
* `‖fderiv ℝ F (extChartAt I α b)‖ · ‖X b‖` controls the intrinsic
  Fréchet-derivative piece.
* `‖T b‖` controls each Christoffel slot correction (whose op-norm is
  `O(‖T b‖)` with a slot-CLM factor that scales like `(1 + ‖X b‖) ^ n`,
  absorbed into the polynomial multiplier).

The constant `C` depends only on `r`, `s`, the metric `g`, the chart at
`α`, and the locality hypothesis — not on `T`, `X`, or `b`. -/
theorem chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (T : Π b' : M, TensorRSSpace r s I b'),
        ∀ (X : Π b' : M, TangentSpace I b'),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α T X b‖ ≤
            C * (max (1 + ‖X b‖) 1) ^ (max r s) *
              (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T ∘
                  (extChartAt I α).symm) (extChartAt I α b)‖ * ‖X b‖
               + ‖T b‖) := by
  classical
  -- Set up the compact base set: the POU tsupport at `α`.
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- Step 1: uniform bound on the intrinsic CLM over `K`.
  obtain ⟨C_I, hC_I_pos, hC_I_bound⟩ :=
    tensorRSIntrinsicChartCLM_opNorm_isBounded_on_compact
      (I := I) (M := M) h_atlas r s α hK_compact hK_sub
  have hC_I_nn : 0 ≤ C_I := le_of_lt hC_I_pos
  -- Step 2: uniform bound on `‖chartLeviCivitaParallelCLM g α b X‖ ≤ C_LC * ‖X b‖`.
  obtain ⟨C_LC, hC_LC_nn, hC_LC_bound⟩ :=
    chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Slot-Christoffel constant: `(max C_LC 1 + 1) ^ (max r s)`.
  set C_slot : ℝ := (max C_LC 1 + 1) ^ (max r s) with hC_slot_def
  have hC_slot_nn : 0 ≤ C_slot := by
    have h_1 : 0 ≤ max C_LC 1 + 1 := by
      have : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
      linarith
    exact pow_nonneg h_1 _
  -- Final constant absorbs `C_I` plus `(r + s) * C_slot`.
  set C : ℝ := C_I + ((r : ℝ) + s) * C_slot with hC_def
  have hC_nn : 0 ≤ C := by
    have h1 : 0 ≤ ((r : ℝ) + s) * C_slot :=
      mul_nonneg (by positivity) hC_slot_nn
    linarith
  refine ⟨C, hC_nn, ?_⟩
  intro b hb T X
  -- Abbreviations.
  set N_F : ℝ := ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ with hN_F_def
  set N_X : ℝ := ‖X b‖ with hN_X_def
  set N_T : ℝ := ‖T b‖ with hN_T_def
  have hN_F_nn : 0 ≤ N_F := norm_nonneg _
  have hN_X_nn : 0 ≤ N_X := norm_nonneg _
  have hN_T_nn : 0 ≤ N_T := norm_nonneg _
  -- The polynomial factor.
  set MX : ℝ := (max (1 + N_X) 1) ^ (max r s) with hMX_def
  have h_1X_nn : (0 : ℝ) ≤ 1 + N_X := by linarith
  have hmax_one_X_nn : 0 ≤ max (1 + N_X) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have hmax_one_X_ge_one : (1 : ℝ) ≤ max (1 + N_X) 1 := le_max_right _ _
  have hMX_nn : 0 ≤ MX := pow_nonneg hmax_one_X_nn _
  have hMX_ge_one : 1 ≤ MX := by
    have h1 : (1 : ℝ) ^ (max r s) ≤ (max (1 + N_X) 1) ^ (max r s) :=
      pow_le_pow_left₀ (by norm_num) hmax_one_X_ge_one _
    simpa using h1
  -- Triangle inequality on the three-term decomposition.
  rw [chartTensorRSCovariantDerivative_def]
  set B_intr : TensorRSSpace r s I b :=
    tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) with hB_intr_def
  set B_in : TensorRSSpace r s I b :=
    ∑ k : Fin r,
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k with hB_in_def
  set B_out : TensorRSSpace r s I b :=
    ∑ l : Fin s,
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l with hB_out_def
  have h_tri : ‖B_intr + B_in - B_out‖ ≤ ‖B_intr‖ + ‖B_in‖ + ‖B_out‖ := by
    have h₁ : ‖B_intr + B_in - B_out‖ ≤ ‖B_intr + B_in‖ + ‖B_out‖ :=
      norm_sub_le _ _
    have h₂ : ‖B_intr + B_in‖ ≤ ‖B_intr‖ + ‖B_in‖ := norm_add_le _ _
    linarith
  -- Intrinsic piece bound.
  have h_intr_le : ‖B_intr‖ ≤ C_I * N_F * N_X := by
    rw [hB_intr_def]
    exact hC_I_bound T b hb (X b)
  -- Parallel-CLM bound at `b`.
  have h_LC_at_b : ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ ≤ C_LC * N_X := by
    rw [hN_X_def]
    exact hC_LC_bound hb X
  -- Per-input-slot bound.
  have h_in_per : ∀ k : Fin r,
      ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
        C_slot * MX * N_T := by
    intro k
    have h_step1 :
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
          (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r * N_T := by
      rw [hN_T_def]
      exact chartTensorRSInputSlotCorrection_opNorm_le (I := I) r s g α T X b k
    have h_pow_le :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r ≤
          (max C_LC 1 + 1) ^ r * (1 + N_X) ^ r :=
      slot_factor_pow_le_const_mul_one_plus_X_pow r hC_LC_nn hN_X_nn h_LC_at_b
    have h_const_pow_le :
        (max C_LC 1 + 1) ^ r ≤ (max C_LC 1 + 1) ^ (max r s) :=
      const_pow_le_max_pow hC_LC_nn (Nat.le_max_left r s)
    have h_1X_pow_le :
        (1 + N_X) ^ r ≤ (max (1 + N_X) 1) ^ (max r s) :=
      one_plus_X_pow_le_max_pow hN_X_nn (Nat.le_max_left r s)
    have h_C_slot_pow_nn : 0 ≤ (max C_LC 1 + 1) ^ (max r s) := by
      have : 0 ≤ max C_LC 1 + 1 := by
        have : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
        linarith
      exact pow_nonneg this _
    have h_combined :
        (max C_LC 1 + 1) ^ r * (1 + N_X) ^ r ≤ C_slot * MX := by
      have h_step_a :
          (max C_LC 1 + 1) ^ r * (1 + N_X) ^ r ≤
            (max C_LC 1 + 1) ^ (max r s) * (1 + N_X) ^ r :=
        mul_le_mul_of_nonneg_right h_const_pow_le (pow_nonneg h_1X_nn r)
      have h_step_b :
          (max C_LC 1 + 1) ^ (max r s) * (1 + N_X) ^ r ≤
            (max C_LC 1 + 1) ^ (max r s) * (max (1 + N_X) 1) ^ (max r s) :=
        mul_le_mul_of_nonneg_left h_1X_pow_le h_C_slot_pow_nn
      have h_final :
          (max C_LC 1 + 1) ^ (max r s) * (max (1 + N_X) 1) ^ (max r s) =
            C_slot * MX := by
        rw [hC_slot_def, hMX_def]
      linarith
    have h_step2 :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r ≤ C_slot * MX :=
      h_pow_le.trans h_combined
    have h_step3 :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r * N_T ≤
          C_slot * MX * N_T :=
      mul_le_mul_of_nonneg_right h_step2 hN_T_nn
    linarith
  -- Sum over input slots.
  have h_in_sum_le : ‖B_in‖ ≤ (r : ℝ) * (C_slot * MX * N_T) := by
    have h_norm_sum_le :
        ‖B_in‖ ≤ ∑ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ := by
      rw [hB_in_def]
      exact norm_sum_le _ _
    have h_each_le_const : ∀ k ∈ (Finset.univ : Finset (Fin r)),
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
          C_slot * MX * N_T := fun k _ => h_in_per k
    have h_sum_const :
        (∑ _k : Fin r, C_slot * MX * N_T) = (r : ℝ) * (C_slot * MX * N_T) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    have h_step :
        (∑ k : Fin r, ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖) ≤
          ∑ _k : Fin r, C_slot * MX * N_T :=
      Finset.sum_le_sum h_each_le_const
    linarith
  -- Per-output-slot bound and sum.
  have h_out_per : ∀ l : Fin s,
      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
        C_slot * MX * N_T := by
    intro l
    have h_step1 :
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
          (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s * N_T := by
      rw [hN_T_def]
      exact chartTensorRSOutputSlotCorrection_opNorm_le (I := I) r s g α T X b l
    have h_pow_le :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s ≤
          (max C_LC 1 + 1) ^ s * (1 + N_X) ^ s :=
      slot_factor_pow_le_const_mul_one_plus_X_pow s hC_LC_nn hN_X_nn h_LC_at_b
    have h_const_pow_le :
        (max C_LC 1 + 1) ^ s ≤ (max C_LC 1 + 1) ^ (max r s) :=
      const_pow_le_max_pow hC_LC_nn (Nat.le_max_right r s)
    have h_1X_pow_le :
        (1 + N_X) ^ s ≤ (max (1 + N_X) 1) ^ (max r s) :=
      one_plus_X_pow_le_max_pow hN_X_nn (Nat.le_max_right r s)
    have h_C_slot_pow_nn : 0 ≤ (max C_LC 1 + 1) ^ (max r s) := by
      have : 0 ≤ max C_LC 1 + 1 := by
        have : 0 ≤ max C_LC 1 := le_trans zero_le_one (le_max_right _ _)
        linarith
      exact pow_nonneg this _
    have h_combined :
        (max C_LC 1 + 1) ^ s * (1 + N_X) ^ s ≤ C_slot * MX := by
      have h_step_a :
          (max C_LC 1 + 1) ^ s * (1 + N_X) ^ s ≤
            (max C_LC 1 + 1) ^ (max r s) * (1 + N_X) ^ s :=
        mul_le_mul_of_nonneg_right h_const_pow_le (pow_nonneg h_1X_nn s)
      have h_step_b :
          (max C_LC 1 + 1) ^ (max r s) * (1 + N_X) ^ s ≤
            (max C_LC 1 + 1) ^ (max r s) * (max (1 + N_X) 1) ^ (max r s) :=
        mul_le_mul_of_nonneg_left h_1X_pow_le h_C_slot_pow_nn
      have h_final :
          (max C_LC 1 + 1) ^ (max r s) * (max (1 + N_X) 1) ^ (max r s) =
            C_slot * MX := by
        rw [hC_slot_def, hMX_def]
      linarith
    have h_step2 :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s ≤ C_slot * MX :=
      h_pow_le.trans h_combined
    have h_step3 :
        (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s * N_T ≤
          C_slot * MX * N_T :=
      mul_le_mul_of_nonneg_right h_step2 hN_T_nn
    linarith
  have h_out_sum_le : ‖B_out‖ ≤ (s : ℝ) * (C_slot * MX * N_T) := by
    have h_norm_sum_le :
        ‖B_out‖ ≤ ∑ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ := by
      rw [hB_out_def]
      exact norm_sum_le _ _
    have h_each_le_const : ∀ l ∈ (Finset.univ : Finset (Fin s)),
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
          C_slot * MX * N_T := fun l _ => h_out_per l
    have h_sum_const :
        (∑ _l : Fin s, C_slot * MX * N_T) = (s : ℝ) * (C_slot * MX * N_T) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    have h_step :
        (∑ l : Fin s, ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖) ≤
          ∑ _l : Fin s, C_slot * MX * N_T :=
      Finset.sum_le_sum h_each_le_const
    linarith
  -- Combine the three bounds.
  -- ‖∇T‖ ≤ C_I * N_F * N_X + ((r:ℝ) + s) * (C_slot * MX * N_T).
  have h_combined_le :
      ‖B_intr + B_in - B_out‖ ≤
        C_I * N_F * N_X + ((r : ℝ) + s) * (C_slot * MX * N_T) := by
    have h_dist : ((r : ℝ) + s) * (C_slot * MX * N_T)
        = (r : ℝ) * (C_slot * MX * N_T) + (s : ℝ) * (C_slot * MX * N_T) := by
      ring
    linarith
  -- Final lift to the headline form.
  -- Headline RHS: `C * MX * (N_F * N_X + N_T) = (C_I + ((r:ℝ)+s)*C_slot) * MX * (N_F*N_X + N_T)`.
  -- Use `MX ≥ 1` and non-negativity to bound each summand individually.
  have h_NX_term_nn : 0 ≤ N_F * N_X := mul_nonneg hN_F_nn hN_X_nn
  have h_sum_nn : 0 ≤ N_F * N_X + N_T := by linarith
  -- C_I * N_F * N_X ≤ C_I * MX * (N_F * N_X + N_T).
  have h_intr_to_headline :
      C_I * N_F * N_X ≤ C_I * MX * (N_F * N_X + N_T) := by
    have h_a : C_I * N_F * N_X ≤ C_I * MX * (N_F * N_X) := by
      have h_left_nn : 0 ≤ C_I * N_F := mul_nonneg hC_I_nn hN_F_nn
      have h_rearrange : C_I * MX * (N_F * N_X) = (C_I * N_F) * (MX * N_X) := by ring
      have h_lhs_eq : C_I * N_F * N_X = (C_I * N_F) * N_X := by ring
      rw [h_lhs_eq, h_rearrange]
      have h_MX_NX_ge : N_X ≤ MX * N_X := by
        have : (1 : ℝ) * N_X ≤ MX * N_X :=
          mul_le_mul_of_nonneg_right hMX_ge_one hN_X_nn
        linarith
      exact mul_le_mul_of_nonneg_left h_MX_NX_ge h_left_nn
    have h_b : C_I * MX * (N_F * N_X) ≤ C_I * MX * (N_F * N_X + N_T) := by
      have h_left_nn : 0 ≤ C_I * MX := mul_nonneg hC_I_nn hMX_nn
      have h_inc : N_F * N_X ≤ N_F * N_X + N_T := by linarith
      exact mul_le_mul_of_nonneg_left h_inc h_left_nn
    linarith
  -- ((r:ℝ) + s) * C_slot * MX * N_T ≤ ((r:ℝ) + s) * C_slot * MX * (N_F * N_X + N_T).
  have h_slot_to_headline :
      ((r : ℝ) + s) * (C_slot * MX * N_T) ≤
        ((r : ℝ) + s) * C_slot * MX * (N_F * N_X + N_T) := by
    have h_left_nn : 0 ≤ ((r : ℝ) + s) * C_slot * MX := by
      have h1 : 0 ≤ ((r : ℝ) + s) * C_slot :=
        mul_nonneg (by positivity) hC_slot_nn
      exact mul_nonneg h1 hMX_nn
    have h_inc : N_T ≤ N_F * N_X + N_T := by linarith
    have h_rearrange :
        ((r : ℝ) + s) * (C_slot * MX * N_T) = ((r : ℝ) + s) * C_slot * MX * N_T := by
      ring
    rw [h_rearrange]
    exact mul_le_mul_of_nonneg_left h_inc h_left_nn
  -- The headline RHS, `C * MX * (N_F * N_X + N_T)`, expands.
  have h_RHS_expand :
      C * MX * (N_F * N_X + N_T) =
        C_I * MX * (N_F * N_X + N_T) +
          ((r : ℝ) + s) * C_slot * MX * (N_F * N_X + N_T) := by
    rw [hC_def]; ring
  -- Combine.
  have h_combined_le' :
      ‖B_intr + B_in - B_out‖ ≤
        C_I * MX * (N_F * N_X + N_T) +
          ((r : ℝ) + s) * C_slot * MX * (N_F * N_X + N_T) := by
    have : C_I * N_F * N_X + ((r : ℝ) + s) * (C_slot * MX * N_T) ≤
        C_I * MX * (N_F * N_X + N_T) +
          ((r : ℝ) + s) * C_slot * MX * (N_F * N_X + N_T) := by
      linarith
    linarith
  -- Re-fold to `C * MX * (N_F * N_X + N_T)`.
  calc ‖B_intr + B_in - B_out‖
      ≤ C_I * MX * (N_F * N_X + N_T) +
          ((r : ℝ) + s) * C_slot * MX * (N_F * N_X + N_T) := h_combined_le'
    _ = C * MX * (N_F * N_X + N_T) := h_RHS_expand.symm

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
end Sanity
