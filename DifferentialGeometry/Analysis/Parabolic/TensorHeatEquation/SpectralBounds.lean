import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Spectral powers of the tensor heat semigroup on `TensorL2 r s g`

For a closed Riemannian manifold `(M, g)` with a uniform tensor Sobolev
bound `h_atlas`, this file extends the spectral construction of
`tensorHeatSemigroup g r s h_atlas t` to the family of operators
`tensorHeatPower g r s h_atlas k t = (-Δ_∇)^k ∘ e^{t Δ_∇}` on
`TensorL2 r s g`, defined for every `k : ℕ` and `t : ℝ` via the diagonal
action `T ↦ ∑' i, λ_i^k · exp(-λ_i · t) • ⟪b i, T⟫ • b i` (for `0 < t`)
on the tensor eigenbasis `b := tensorResolventHilbertEigenbasisSigma`.
At `k = 0` it coincides with `tensorHeatSemigroup`; for `k ≥ 1` and
`t ≤ 0` it is set to zero (junk).

## Main definitions

* `tensorHeatPower` — the spectral power as a `TensorL2 r s g →L[ℝ]
  TensorL2 r s g`.

## Main results

* `tensorHeatPower_zero` — identification at `k = 0`.
* `tensorHeatPower_apply_of_pos_one_le` — series formula for `1 ≤ k`,
  `0 < t`.
* `tensorHeatPower_eq_zero_of_one_le_of_nonpos` — zero map for `1 ≤ k`,
  `t ≤ 0`.
* `tensorHeatPower_opNorm_le` — `(k/t)^k · e^{-k}` bound for `1 ≤ k`,
  `0 < t`.
* `tensorHeatPower_apply_basis_pos` — diagonal action on the eigenbasis.
* `tensorHeatPower_isSelfAdjoint` — self-adjointness for `0 < t`.

## Sign convention

Geometer convention `Δ_∇ = -∇* ∇`, spectrum `⊆ (-∞, 0]`. `(-Δ_∇)` is
non-negative; the basis coefficient `λ_i^k · exp(-λ_i · t) ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Pointwise spectral bound

`λ^k · exp(-λ t) ≤ (k/t)^k · exp(-k)` for `λ ≥ 0`, `t > 0`. -/

/-- The constant `(k/t)^k · exp(-k)`, the global max of `λ ↦ λ^k e^{-λt}` on
`[0, ∞)` for `k ≥ 1` and `t > 0`. -/
private noncomputable def tensorHeatPowerCoeffBound (k : ℕ) (t : ℝ) : ℝ :=
  (k / t : ℝ) ^ k * Real.exp (-(k : ℝ))

private lemma tensorHeatPowerCoeffBound_nonneg (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ tensorHeatPowerCoeffBound k t := by
  unfold tensorHeatPowerCoeffBound
  apply mul_nonneg
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) ht.le) k
  · exact (Real.exp_pos _).le

/-- For `λ ≥ 0`, `t > 0` and any `k ≥ 0`, `λ^k · exp(-λt) ≤ (k/t)^k · exp(-k)`. -/
private lemma tensor_lambda_pow_mul_exp_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ^ k * Real.exp (-(lam * t)) ≤ tensorHeatPowerCoeffBound k t := by
  unfold tensorHeatPowerCoeffBound
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, Real.exp_zero,
      mul_one]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ lam * t := mul_nonneg hlam ht.le
    linarith
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have h_tk_pos : (0 : ℝ) < t / k := div_pos ht hk_real_pos
  have h_aux : lam * Real.exp (-((t / (k : ℝ)) * lam)) ≤
      (k / t : ℝ) * Real.exp (-1) := by
    set s : ℝ := (t / k : ℝ) * lam with hs_def
    have hs_nn : 0 ≤ s := mul_nonneg h_tk_pos.le hlam
    have hs_bound : s * Real.exp (-s) ≤ Real.exp (-1) := by
      have h1 : s ≤ Real.exp (s - 1) := by
        have h := Real.add_one_le_exp (s - 1)
        linarith
      have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
      have h_mul : s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h1 hexp_pos.le
      rw [← Real.exp_add] at h_mul
      have h_sum : s - 1 + -s = -1 := by ring
      rw [h_sum] at h_mul
      exact h_mul
    have h_lam_eq : lam = (k / t : ℝ) * s := by
      simp only [hs_def]
      have ht_ne : (t : ℝ) ≠ 0 := ht.ne'
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    have h_arg_eq : -((t / k : ℝ) * lam) = -s := by
      simp only [hs_def]
    rw [h_arg_eq, h_lam_eq]
    have h_kt_nn : 0 ≤ (k / t : ℝ) := div_nonneg hk_real_pos.le ht.le
    calc (k / t : ℝ) * s * Real.exp (-s)
        = (k / t : ℝ) * (s * Real.exp (-s)) := by ring
      _ ≤ (k / t : ℝ) * Real.exp (-1) :=
            mul_le_mul_of_nonneg_left hs_bound h_kt_nn
  have h_lhs_nn : 0 ≤ lam * Real.exp (-((t / (k : ℝ)) * lam)) :=
    mul_nonneg hlam (Real.exp_pos _).le
  have h_pow_le : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k ≤
      ((k / t : ℝ) * Real.exp (-1)) ^ k :=
    pow_le_pow_left₀ h_lhs_nn h_aux k
  have h_lhs_eq : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k =
      lam ^ k * Real.exp (-(lam * t)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have h_arg : (k : ℝ) * -((t / (k : ℝ)) * lam) = -(lam * t) := by
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    rw [h_arg]
  have h_rhs_eq : ((k / t : ℝ) * Real.exp (-1)) ^ k =
      (k / t : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  rw [h_lhs_eq] at h_pow_le
  rw [h_rhs_eq] at h_pow_le
  exact h_pow_le

/-- Squared version of `tensor_lambda_pow_mul_exp_le`. -/
private lemma tensor_lambda_pow_mul_exp_sq_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    (lam ^ k * Real.exp (-(lam * t))) ^ 2 ≤
      (tensorHeatPowerCoeffBound k t) ^ 2 := by
  have h_lhs_nn : 0 ≤ lam ^ k * Real.exp (-(lam * t)) :=
    mul_nonneg (pow_nonneg hlam k) (Real.exp_pos _).le
  have h_le : lam ^ k * Real.exp (-(lam * t)) ≤
      tensorHeatPowerCoeffBound k t :=
    tensor_lambda_pow_mul_exp_le k ht hlam
  exact pow_le_pow_left₀ h_lhs_nn h_le 2

/-! ## Square-summability of the heat-power-weighted basis coefficients -/

/-- `(λ_i^k · exp(-λ_i t) · ⟪b i, T⟫)²` is summable for `0 < t`. -/
private lemma tensorSummable_heatPower_coeff_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i, T⟫_ℝ) ^ 2) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_coeff_sq_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (⟪b i, T⟫_ℝ) ^ 2) := by
    have h_norm_sq_summable :=
      tensorSummable_basis_coeff_sq (I := I) (M := M) h_atlas T
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪b i, T⟫_ℝ‖ ^ 2) =
        (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
      funext i
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq] at h_norm_sq_summable
    exact h_norm_sq_summable
  refine Summable.of_nonneg_of_le ?_ ?_
    (h_coeff_sq_summable.mul_left ((tensorHeatPowerCoeffBound k t) ^ 2))
  · intro i; positivity
  · intro i
    have h_coeff_sq_le :
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤
          (tensorHeatPowerCoeffBound k t) ^ 2 := by
      have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have h_arg :
          -(TensorEigenIdx.lambda (I := I) (M := M) i) * t =
            -(TensorEigenIdx.lambda (I := I) (M := M) i * t) := by ring
      rw [h_arg]
      exact tensor_lambda_pow_mul_exp_sq_le k ht hlam
    have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
    calc
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) ^ 2
          = ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, T⟫_ℝ) ^ 2 := by ring
      _ ≤ (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_coeff_sq_le h_inner_sq_nn

/-- The heat-power-weighted basis-vector family is summable for `0 < t`. -/
lemma tensorSummable_heatPowerTerm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i, T⟫_ℝ •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_atlas i) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪b i, T⟫_ℝ)
  have h_sq_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖(TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ‖ ^ 2) =
      (fun i =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_sq_summable :=
    tensorSummable_heatPower_coeff_sq (I := I) (M := M) h_atlas k ht T
  have h_summable_V := h_iff.mpr h_sq_summable
  have h_map_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)
          ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, T⟫_ℝ)) =
      (fun i =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, T⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
    rw [mul_smul]
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

/-! ## L² norm bound for the heat-power series -/

/-- Squared L² bound of the heat-power series by `((k/t)^k · exp(-k))² · ‖T‖²`. -/
private lemma tensorNorm_sq_heatPowerTerm_sum_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    ‖∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_atlas i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i‖ ^ 2 ≤
      (tensorHeatPowerCoeffBound k t) ^ 2 * ‖T‖ ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_summand_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, T⟫_ℝ • b i) =
      (fun i =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) • b i) := by
    funext i; rw [smul_smul]
  rw [h_summand_eq]
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ := fun i =>
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
      ⟪b i, T⟫_ℝ
  have hC_nn : 0 ≤ tensorHeatPowerCoeffBound k t :=
    tensorHeatPowerCoeffBound_nonneg k ht
  have h_coeff_sq_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (⟪b i, T⟫_ℝ) ^ 2) := by
    have h_norm_sq_summable :=
      tensorSummable_basis_coeff_sq (I := I) (M := M) h_atlas T
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪b i, T⟫_ℝ‖ ^ 2) =
        (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
      funext i
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq] at h_norm_sq_summable
    exact h_norm_sq_summable
  have h_f_sq_le :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s, (f i) ^ 2 ≤
        (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 := by
    intro i
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have h_arg :
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t =
          -(TensorEigenIdx.lambda (I := I) (M := M) i * t) := by ring
    have h_coeff_sq_le :
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤
          (tensorHeatPowerCoeffBound k t) ^ 2 := by
      rw [h_arg]
      exact tensor_lambda_pow_mul_exp_sq_le k ht hlam
    have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ _
    calc
      (f i) ^ 2
          = ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, T⟫_ℝ) ^ 2 := by
                change ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
                  Real.exp
                    (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
                  ⟪b i, T⟫_ℝ) ^ 2 = _
                ring
      _ ≤ (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_coeff_sq_le h_inner_sq_nn
  have h_summable_f_sq : Summable (fun i =>
      (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_
      (h_coeff_sq_summable.mul_left
        ((tensorHeatPowerCoeffBound k t) ^ 2))
    · intro i; positivity
    · intro i; exact h_f_sq_le i
  have h_norm_sq_eq :=
    tensorOrthonormal_norm_sq_eq_tsum_sq
      (I := I) (M := M) h_atlas f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 ≤ _
  rw [h_norm_sq_eq]
  have h_dom : ∑' i : TensorEigenIdx (I := I) (M := M) g r s, (f i) ^ 2 ≤
      (tensorHeatPowerCoeffBound k t) ^ 2 *
        ∑' i, (⟪b i, T⟫_ℝ) ^ 2 := by
    have h_summable_dom :
        Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2) :=
      h_coeff_sq_summable.mul_left _
    have h_step :
        ∑' i : TensorEigenIdx (I := I) (M := M) g r s, (f i) ^ 2 ≤
        ∑' i,
          (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 :=
      Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq h_summable_dom
    have h_tsum_eq :
        (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          (tensorHeatPowerCoeffBound k t) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2) =
        (tensorHeatPowerCoeffBound k t) ^ 2 *
          ∑' i, (⟪b i, T⟫_ℝ) ^ 2 :=
      tsum_mul_left
    linarith [h_tsum_eq, h_step]
  refine le_trans h_dom ?_
  have h_parseval :=
    tensorParseval_norm_sq (I := I) (M := M) h_atlas T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖⟪b i, T⟫_ℝ‖ ^ 2) =
      (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_eq] at h_parseval
  have hC_sq_nn : 0 ≤ (tensorHeatPowerCoeffBound k t) ^ 2 := sq_nonneg _
  nlinarith [h_parseval, hC_sq_nn]

/-- L² bound of the heat-power series by `(k/t)^k · exp(-k) · ‖T‖`. -/
private lemma tensorNorm_heatPowerTerm_sum_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    ‖∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_atlas i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i‖ ≤
      tensorHeatPowerCoeffBound k t * ‖T‖ := by
  have h_sq :=
    tensorNorm_sq_heatPowerTerm_sum_le (I := I) (M := M) h_atlas k ht T
  have hC_nn : 0 ≤ tensorHeatPowerCoeffBound k t :=
    tensorHeatPowerCoeffBound_nonneg k ht
  have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
  have h_rhs_sq : (tensorHeatPowerCoeffBound k t * ‖T‖) ^ 2 =
      (tensorHeatPowerCoeffBound k t) ^ 2 * ‖T‖ ^ 2 := by ring
  rw [← h_rhs_sq] at h_sq
  have h_rhs_nn : 0 ≤ tensorHeatPowerCoeffBound k t * ‖T‖ :=
    mul_nonneg hC_nn h_T_nn
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

/-! ## Underlying linear map and CLM packaging -/

/-- The underlying function of `tensorHeatPower … k t` for `0 < t`. -/
private noncomputable def tensorHeatPowerFun
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ) (t : ℝ)
    (T : TensorL2 r s g) : TensorL2 r s g :=
  ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
    ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_atlas i, T⟫_ℝ •
      tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas i

/-- Additivity of `tensorHeatPowerFun` for `0 < t`. -/
private lemma tensorHeatPowerFun_add
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (T₁ T₂ : TensorL2 r s g) :
    tensorHeatPowerFun (I := I) (M := M) h_atlas k t (T₁ + T₂) =
      tensorHeatPowerFun (I := I) (M := M) h_atlas k t T₁ +
        tensorHeatPowerFun (I := I) (M := M) h_atlas k t T₂ := by
  unfold tensorHeatPowerFun
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, T₁ + T₂⟫_ℝ • b i =
      (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, T₁⟫_ℝ • b i) +
      (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, T₂⟫_ℝ • b i) := by
    intro i
    rw [inner_add_right, add_smul, smul_add]
  have h_sum_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, T₁ + T₂⟫_ℝ • b i) =
      (fun i =>
        (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, T₁⟫_ℝ • b i) +
        (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, T₂⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  rw [Summable.tsum_add
    (tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht T₁)
    (tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht T₂)]

/-- Scalar-homogeneity of `tensorHeatPowerFun` for `0 < t`. -/
private lemma tensorHeatPowerFun_smul
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (c : ℝ) (T : TensorL2 r s g) :
    tensorHeatPowerFun (I := I) (M := M) h_atlas k t (c • T) =
      c • tensorHeatPowerFun (I := I) (M := M) h_atlas k t T := by
  unfold tensorHeatPowerFun
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, c • T⟫_ℝ • b i =
      c • (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, T⟫_ℝ • b i) := by
    intro i
    rw [real_inner_smul_right]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have h_sum_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, c • T⟫_ℝ • b i) =
      (fun i => c • (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, T⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  exact (tensorSummable_heatPowerTerm
    (I := I) (M := M) h_atlas k ht T).tsum_const_smul c

/-! ## The `tensorHeatPower` CLM -/

/-- The spectral power `(-Δ_∇)^k · e^{t Δ_∇}` on `TensorL2 r s g`.
For `k = 0` and any `t : ℝ`: equals `tensorHeatSemigroup … t`.
For `k ≥ 1` and `t > 0`: a bounded operator with op-norm `≤ (k/t)^k · e^{-k}`.
For `k ≥ 1` and `t ≤ 0`: junk, set to `0`. -/
noncomputable def tensorHeatPower
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g := by
  by_cases hk : k = 0
  · exact tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
  by_cases ht : 0 < t
  · refine LinearMap.mkContinuous
      { toFun := tensorHeatPowerFun (I := I) (M := M) h_atlas k t
        map_add' := tensorHeatPowerFun_add (I := I) (M := M) h_atlas k ht
        map_smul' := fun c T =>
          tensorHeatPowerFun_smul (I := I) (M := M) h_atlas k ht c T }
      (tensorHeatPowerCoeffBound k t) ?_
    intro T
    exact tensorNorm_heatPowerTerm_sum_le
      (I := I) (M := M) h_atlas k ht T
  · exact 0

/-! ## Identification at `k = 0` -/

/-- `tensorHeatPower … 0 t = tensorHeatSemigroup … t`. -/
theorem tensorHeatPower_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M) (t : ℝ) :
    tensorHeatPower (I := I) (M := M) g r s h_atlas 0 t =
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t := by
  unfold tensorHeatPower
  rw [dif_pos rfl]

/-! ## Application formulas -/

/-- Explicit spectral-series formula for `1 ≤ k` and `0 < t`. -/
theorem tensorHeatPower_apply_of_pos_one_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    tensorHeatPower (I := I) (M := M) g r s h_atlas k t T =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_atlas i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold tensorHeatPower
  rw [dif_neg hk_ne, dif_pos ht]
  rfl

/-- Zero map for `1 ≤ k` and `t ≤ 0`. -/
theorem tensorHeatPower_eq_zero_of_one_le_of_nonpos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ≤ 0) :
    tensorHeatPower (I := I) (M := M) g r s h_atlas k t = 0 := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold tensorHeatPower
  rw [dif_neg hk_ne, dif_neg (not_lt.mpr ht)]

/-- Unified spectral-series formula for any `k` and `0 < t`. -/
theorem tensorHeatPower_apply_of_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    tensorHeatPower (I := I) (M := M) g r s h_atlas k t T =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_atlas i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_atlas i := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    rw [tensorHeatPower_zero,
        tensorHeatSemigroup_apply_of_nonneg
          (I := I) (M := M) h_atlas ht.le T]
    apply tsum_congr
    intro i; rw [pow_zero, one_mul]
  · exact tensorHeatPower_apply_of_pos_one_le
      (I := I) (M := M) h_atlas hk_pos ht T

/-! ## Operator-norm bound -/

/-- Operator-norm bound `(k/t)^k · exp(-k)` for `1 ≤ k`, `0 < t`. -/
theorem tensorHeatPower_opNorm_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    ‖tensorHeatPower (I := I) (M := M) g r s h_atlas k t‖ ≤
      (k / t : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold tensorHeatPower
  rw [dif_neg hk_ne, dif_pos ht]
  have hC_nn : 0 ≤ tensorHeatPowerCoeffBound k t :=
    tensorHeatPowerCoeffBound_nonneg k ht
  exact LinearMap.mkContinuous_norm_le _ hC_nn _

/-! ## Action on basis vectors -/

/-- Diagonal action: `tensorHeatPower … k t (b i) = λ_i^k · exp(-λ_i t) • b i`
for `0 < t`. -/
theorem tensorHeatPower_apply_basis_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHeatPower (I := I) (M := M) g r s h_atlas k t
        (tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_atlas i) =
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_atlas i := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  rw [tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht]
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ⟪b j, b i⟫_ℝ = if j = i then 1 else 0 := by
    intro j
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ((TensorEigenIdx.lambda (I := I) (M := M) j) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t)) •
        ⟪b j, b i⟫_ℝ • b j =
      if j = i then
        ((TensorEigenIdx.lambda (I := I) (M := M) j) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t)) • b j
      else 0 := by
    intro j
    rw [h_inner_eq]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h_sum_eq :
      (fun j : TensorEigenIdx (I := I) (M := M) g r s =>
        ((TensorEigenIdx.lambda (I := I) (M := M) j) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t)) •
          ⟪b j, b i⟫_ℝ • b j) =
      (fun j =>
        if j = i then
          ((TensorEigenIdx.lambda (I := I) (M := M) j) ^ k *
              Real.exp
                (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t)) • b j
        else 0) := by
    funext j; exact h_summand_eq j
  rw [h_sum_eq]
  rw [tsum_ite_eq i]

/-! ## Self-adjointness for `0 < t` -/

/-- Self-adjointness of `tensorHeatPower … k t` for `0 < t`. -/
theorem tensorHeatPower_isSelfAdjoint
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    IsSelfAdjoint
      (tensorHeatPower (I := I) (M := M) g r s h_atlas k t :
        TensorL2 r s g →L[ℝ] TensorL2 r s g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  change ⟪(tensorHeatPower (I := I) (M := M) g r s h_atlas k t) u, v⟫_ℝ =
      ⟪u, (tensorHeatPower (I := I) (M := M) g r s h_atlas k t) v⟫_ℝ
  rw [tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht u,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht v]
  let φv : TensorL2 r s g →L[ℝ] ℝ := (innerSL ℝ).flip v
  let φu : TensorL2 r s g →L[ℝ] ℝ := innerSL ℝ u
  have h_lhs : ⟪∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u⟫_ℝ • b i, v⟫_ℝ =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable :=
      tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht u
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φv
    have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        φv (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i) =
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ = _
      rw [real_inner_smul_left, real_inner_smul_left]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φv (∑' i, ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φv (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp
                (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i) =
        ⟪∑' i, ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  have h_rhs : ⟪u, ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, v⟫_ℝ • b i⟫_ℝ =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable :=
      tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht v
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φu
    have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        φu (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i) =
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪u, ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ = _
      rw [real_inner_smul_right, real_inner_smul_right,
          show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φu (∑' i, ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φu (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp
                (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i) =
        ⟪u, ∑' i, ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  rw [h_lhs, h_rhs]

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
