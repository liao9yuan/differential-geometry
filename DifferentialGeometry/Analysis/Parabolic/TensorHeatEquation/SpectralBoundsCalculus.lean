import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SpectralBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Time differentiability and `C^∞`-ness of the tensor spectral power family

For a closed Riemannian manifold `(M, g)` with a uniform tensor Sobolev
bound `h_atlas`, this file proves the time-calculus properties of the
family `tensorHeatPower g r s h_atlas k t` on `TensorL2 r s g`:

* `tensorHeatPower_comp_tensorHeatSemigroup`,
  `tensorHeatSemigroup_comp_tensorHeatPower` — both directions of the
  composition law `(-Δ_∇)^k e^{t₁ Δ_∇} ∘ e^{t₂ Δ_∇} =
  (-Δ_∇)^k e^{(t₁+t₂) Δ_∇}` (for `0 < t₁`, `0 ≤ t₂`).
* `hasDerivAt_tensorHeatPower` — `(d/ds) tensorHeatPower g r s h_atlas k s
  = -tensorHeatPower g r s h_atlas (k+1) s` at every `t > 0`, in the
  operator-norm topology.
* `hasDerivAt_tensorHeatSemigroup` — specialization of the above for
  `k = 0`.
* `iteratedDerivWithin_tensorHeatSemigroup_Ioi` — the iterated form
  `(d/ds)^j e^{s Δ_∇} = (-1)^j tensorHeatPower g r s h_atlas j s`.
* `contDiffOn_tensorHeatPower_Ioi`,
  `contDiffOn_tensorHeatSemigroup_Ioi` — `C^∞`-ness on `(0, ∞)` in the
  operator-norm topology.

All proofs mirror the scalar template in
`Analysis/HeatEquation/SpectralBounds.lean`, replacing the scalar
eigenbasis by the tensor eigenbasis
`tensorResolventHilbertEigenbasisSigma`. The key Taylor-remainder
estimate `tensor_exp_neg_taylor_bound` provides a uniform spectral bound
that, lifted through Parseval, yields the operator-norm derivative.
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

/-! ## Local pointwise spectral bound

We re-introduce the bound `λ^k · exp(-λ t) ≤ (k/t)^k · e^{-k}` for use in
the Taylor-remainder argument; the private constant from
`SpectralBounds.lean` is not exported. -/

/-- Local copy of the constant `(k/t)^k · e^{-k}`. -/
private noncomputable def tensorHeatPowerCoeffBoundCalc (k : ℕ) (t : ℝ) : ℝ :=
  (k / t : ℝ) ^ k * Real.exp (-(k : ℝ))

private lemma tensorHeatPowerCoeffBoundCalc_nonneg (k : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ tensorHeatPowerCoeffBoundCalc k t := by
  unfold tensorHeatPowerCoeffBoundCalc
  apply mul_nonneg
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) ht.le) k
  · exact (Real.exp_pos _).le

/-- Local copy of `λ^k · exp(-λt) ≤ (k/t)^k · e^{-k}` for `λ ≥ 0`,
`t > 0`. -/
private lemma tensor_lambda_pow_mul_exp_le_calc
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ^ k * Real.exp (-(lam * t)) ≤ tensorHeatPowerCoeffBoundCalc k t := by
  unfold tensorHeatPowerCoeffBoundCalc
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

/-! ## Compositions -/

set_option linter.unusedVariables false in
/-- Right-composition: `tensorHeatPower g r s h_atlas k t₁ ∘L
tensorHeatSemigroup g r s h_atlas t₂ = tensorHeatPower g r s h_atlas
k (t₁ + t₂)`, valid for `0 < t₁` and `0 ≤ t₂`. -/
theorem tensorHeatPower_comp_tensorHeatSemigroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {k : ℕ} (hk : 1 ≤ k) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 ≤ t₂) :
    (tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁).comp
        (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂) =
      tensorHeatPower (I := I) (M := M) g r s h_atlas k (t₁ + t₂) := by
  classical
  apply ContinuousLinearMap.ext
  intro T
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have ht12_pos : 0 < t₁ + t₂ := by linarith
  rw [ContinuousLinearMap.comp_apply,
      tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas ht₂ T,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht12_pos T]
  -- Pull `tensorHeatPower g r s h_atlas k t₁` inside the tsum.
  have h_summable_t₂ :=
    tensorSummable_heatTerm (I := I) (M := M) h_atlas ht₂ T
  have h_pull :
      tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁
          (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
              ⟪b i, T⟫_ℝ • b i) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
            ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum := h_summable_t₂.hasSum
    exact (h_hsum.mapL
      (tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁).map_smul,
      (tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁).map_smul]
  -- tensorHeatPower k t₁ (b i) = λ^k · exp(-λ t₁) • b i.
  have h_basis_apply :
      tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁ (b i) =
      ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) • b i :=
    tensorHeatPower_apply_basis_pos (I := I) (M := M) h_atlas k ht₁ i
  rw [h_basis_apply]
  rw [show (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
        (⟪b i, T⟫_ℝ • ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) •
          b i)) =
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) *
          ⟪b i, T⟫_ℝ *
          ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁))) •
          b i from by
    rw [smul_smul, smul_smul]]
  rw [show ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂))) •
        ⟪b i, T⟫_ℝ • b i =
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) *
          ⟪b i, T⟫_ℝ) • b i from by rw [smul_smul]]
  congr 1
  have h_exp_add :
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁) *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) := by
    rw [show -(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁ +
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂ from by ring,
        Real.exp_add]
  rw [h_exp_add]
  ring

set_option linter.unusedVariables false in
/-- Left-composition: `tensorHeatSemigroup g r s h_atlas t₂ ∘L
tensorHeatPower g r s h_atlas k t₁ = tensorHeatPower g r s h_atlas k
(t₁ + t₂)`, valid for `0 < t₁` and `0 ≤ t₂`. -/
theorem tensorHeatSemigroup_comp_tensorHeatPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {k : ℕ} (hk : 1 ≤ k) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 ≤ t₂) :
    (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂).comp
        (tensorHeatPower (I := I) (M := M) g r s h_atlas k t₁) =
      tensorHeatPower (I := I) (M := M) g r s h_atlas k (t₁ + t₂) := by
  classical
  apply ContinuousLinearMap.ext
  intro T
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have ht12_pos : 0 < t₁ + t₂ := by linarith
  rw [ContinuousLinearMap.comp_apply,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht₁ T,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht12_pos T]
  -- Pull `tensorHeatSemigroup g r s h_atlas t₂` inside the tsum.
  have h_summable_t₁ :=
    tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht₁ T
  have h_pull :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂
          (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
            ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) •
              ⟪b i, T⟫_ℝ • b i) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂
          (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) •
            ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum := h_summable_t₁.hasSum
    exact (h_hsum.mapL
      (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂).map_smul,
      (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂).map_smul]
  -- tensorHeatSemigroup t₂ (b i) = exp(-λ t₂) • b i.
  have h_basis_apply :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂ (b i) =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) • b i :=
    tensorHeatSemigroup_apply_basis (I := I) (M := M) h_atlas ht₂ i
  rw [h_basis_apply]
  rw [show (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) •
          (⟪b i, T⟫_ℝ •
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
            b i)) =
        (((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁)) *
          ⟪b i, T⟫_ℝ *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂)) •
          b i from by
    rw [smul_smul, smul_smul]]
  rw [show ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂))) •
        ⟪b i, T⟫_ℝ • b i =
        ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) *
          ⟪b i, T⟫_ℝ) • b i from by rw [smul_smul]]
  congr 1
  have h_exp_add :
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁) *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) := by
    rw [show -(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁ +
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂ from by ring,
        Real.exp_add]
  rw [h_exp_add]
  ring

/-! ## Time differentiability

We prove that `s ↦ tensorHeatPower g r s h_atlas k s` is differentiable
at every `t > 0` in the operator-norm topology, with derivative
`-tensorHeatPower g r s h_atlas (k+1) t`. The key ingredient is a
uniform Taylor remainder bound on the spectrum, which gives a
Lipschitz-type estimate on the difference quotient, controlled by a
finite spectral supremum. -/

/-- Uniform spectral Taylor estimate: for `λ ≥ 0`, `0 < t`, `|h| ≤ t/2`
and `k : ℕ`, `|λ^k · (exp(-λ(t+h)) - exp(-λ t) + λ h · exp(-λ t))| ≤ K ·
h²` where `K = tensorHeatPowerCoeffBoundCalc (k+2) (t/2)`. -/
private lemma tensor_exp_neg_taylor_bound
    (k : ℕ) {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : |h| ≤ t / 2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    |lam ^ k * (Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
        lam * h * Real.exp (-(lam * t)))| ≤
      tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2 := by
  have h_factor :
      Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
          lam * h * Real.exp (-(lam * t)) =
        Real.exp (-(lam * t)) *
          (Real.exp (-(lam * h)) - 1 - (-(lam * h))) := by
    rw [show -(lam * (t + h)) = -(lam * t) + -(lam * h) from by ring,
      Real.exp_add]
    ring
  rw [h_factor]
  -- Taylor remainder bound: `|exp s - 1 - s| ≤ s² · exp |s|`.
  have h_taylor : ∀ s : ℝ, |Real.exp s - 1 - s| ≤ s ^ 2 * Real.exp |s| := by
    intro s
    have hc :=
      Complex.norm_exp_sub_sum_le_norm_mul_exp (s : ℂ) 2
    have h_sum : ∑ m ∈ Finset.range 2, (s : ℂ) ^ m / (m.factorial : ℂ) =
        1 + (s : ℂ) := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [h_sum] at hc
    have hc' : ‖Complex.exp (s : ℂ) - (1 + (s : ℂ))‖ ≤
        ‖(s : ℂ)‖ ^ 2 * Real.exp ‖(s : ℂ)‖ := hc
    have h_eq : Complex.exp (s : ℂ) - (1 + (s : ℂ)) =
        ((Real.exp s - 1 - s : ℝ) : ℂ) := by
      have h_exp_real : Complex.exp (s : ℂ) = ((Real.exp s : ℝ) : ℂ) :=
        (Complex.ofReal_exp s).symm
      rw [h_exp_real]
      push_cast
      ring
    rw [h_eq] at hc'
    have h_lhs_norm : ‖((Real.exp s - 1 - s : ℝ) : ℂ)‖ =
        |Real.exp s - 1 - s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_lhs_norm] at hc'
    have h_rhs_norm : ‖(s : ℂ)‖ = |s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_rhs_norm] at hc'
    convert hc' using 1
    rw [sq_abs]
  have h_step1 :
      |Real.exp (-(lam * h)) - 1 - (-(lam * h))| ≤
        (-(lam * h)) ^ 2 * Real.exp |-(lam * h)| :=
    h_taylor (-(lam * h))
  have h_neg_sq : (-(lam * h)) ^ 2 = (lam * h) ^ 2 := by ring
  have h_neg_abs : |-(lam * h)| = |lam * h| := abs_neg _
  have h_lam_h_abs : |lam * h| = lam * |h| := by
    rw [abs_mul, abs_of_nonneg hlam]
  rw [h_neg_sq, h_neg_abs, h_lam_h_abs] at h_step1
  have h_exp_t_pos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  rw [show lam ^ k * (Real.exp (-(lam * t)) *
      (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) =
      Real.exp (-(lam * t)) *
      (lam ^ k * (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) from by ring]
  rw [abs_mul]
  rw [abs_of_pos h_exp_t_pos]
  rw [abs_mul]
  rw [show |lam ^ k| = lam ^ k from abs_of_nonneg (pow_nonneg hlam k)]
  have h_step2 :
      Real.exp (-(lam * t)) *
        (lam ^ k * |Real.exp (-(lam * h)) - 1 - (-(lam * h))|) ≤
      Real.exp (-(lam * t)) *
        (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) := by
    apply mul_le_mul_of_nonneg_left _ h_exp_t_pos.le
    apply mul_le_mul_of_nonneg_left h_step1 (pow_nonneg hlam k)
  refine le_trans h_step2 ?_
  have h_t_minus_h_pos : 0 < t - |h| := by
    have ht_half_pos : 0 < t / 2 := by linarith
    have : |h| ≤ t / 2 := hh
    linarith
  have h_t_minus_h_ge : t / 2 ≤ t - |h| := by linarith
  have h_combine : Real.exp (-(lam * t)) *
      (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) =
      lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) := by
    rw [show -(lam * (t - |h|)) = -(lam * t) + lam * |h| from by ring]
    rw [Real.exp_add]
    rw [show (lam * h) ^ 2 = lam ^ 2 * h ^ 2 from by ring]
    rw [pow_add]
    ring
  rw [h_combine]
  have h_lam_pow_exp_le :
      lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) ≤
        lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
    apply Real.exp_le_exp.mpr
    have : -(lam * (t - |h|)) ≤ -(lam * (t / 2)) := by
      have hlt : lam * (t / 2) ≤ lam * (t - |h|) :=
        mul_le_mul_of_nonneg_left h_t_minus_h_ge hlam
      linarith
    exact this
  have h_h_sq_nn : 0 ≤ h ^ 2 := sq_nonneg _
  have h_step3 : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) ≤
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) * h ^ 2 := by
    have hp : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) =
        lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) * h ^ 2 := by ring
    rw [hp]
    exact mul_le_mul_of_nonneg_right h_lam_pow_exp_le h_h_sq_nn
  refine le_trans h_step3 ?_
  have h_t2_pos : 0 < t / 2 := by linarith
  have h_final :
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) ≤
        tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) :=
    tensor_lambda_pow_mul_exp_le_calc (k + 2) h_t2_pos hlam
  exact mul_le_mul_of_nonneg_right h_final h_h_sq_nn

/-- For `0 < t` and `|h| ≤ t/2`, the L²-norm of the Taylor remainder of
`s ↦ tensorHeatPower … k s` at `t`, applied to a tensor `T`, is bounded:
`‖tensorHeatPower k (t+h) T - tensorHeatPower k t T + h •
tensorHeatPower (k+1) t T‖ ≤
tensorHeatPowerCoeffBoundCalc (k+2) (t/2) · h² · ‖T‖`. -/
private lemma tensorNorm_heatPower_taylor_remainder
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t)
    {h : ℝ} (hh : |h| ≤ t / 2) (T : TensorL2 r s g) :
    ‖tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) T -
        tensorHeatPower (I := I) (M := M) g r s h_atlas k t T +
        h • tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t T‖ ≤
      tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2 * ‖T‖ := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_th_pos : 0 < t + h := by
    have : -h ≤ t / 2 := by
      have := abs_le.mp hh
      linarith [this.1]
    linarith
  rw [tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k h_th_pos T,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas k ht T,
      tensorHeatPower_apply_of_pos (I := I) (M := M) h_atlas (k + 1) ht T]
  have h_sum_th :=
    tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k h_th_pos T
  have h_sum_t :=
    tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas k ht T
  have h_sum_t1 :=
    tensorSummable_heatPowerTerm (I := I) (M := M) h_atlas (k + 1) ht T
  set A : TensorEigenIdx (I := I) (M := M) g r s → TensorL2 r s g := fun i =>
    ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t + h))) •
      ⟪b i, T⟫_ℝ • b i with hA_def
  set B : TensorEigenIdx (I := I) (M := M) g r s → TensorL2 r s g := fun i =>
    ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪b i, T⟫_ℝ • b i with hB_def
  set C : TensorEigenIdx (I := I) (M := M) g r s → TensorL2 r s g := fun i =>
    ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪b i, T⟫_ℝ • b i with hC_def
  have h_hsum_combined :
      HasSum (fun i => A i - B i + h • C i)
        ((∑' i, A i) - (∑' i, B i) + h • (∑' i, C i)) := by
    have hA := h_sum_th.hasSum
    have hB := h_sum_t.hasSum
    have hC := h_sum_t1.hasSum
    exact (hA.sub hB).add (hC.const_smul h)
  set ψ : TensorEigenIdx (I := I) (M := M) g r s → ℝ := fun i =>
    (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t + h)) -
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) +
      h * ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) with hψ_def
  have h_combined_eq : ∀ i,
      A i - B i + h • C i = ψ i • ⟪b i, T⟫_ℝ • b i := by
    intro i
    simp only [hA_def, hB_def, hC_def, hψ_def]
    rw [show h • ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, T⟫_ℝ • b i =
          (h * ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t))) •
            ⟪b i, T⟫_ℝ • b i from by rw [smul_smul]]
    rw [← sub_smul, ← add_smul]
    congr 1
    ring
  have h_combined_sum_eq :
      (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (A i - B i + h • C i)) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ψ i • ⟪b i, T⟫_ℝ • b i :=
    tsum_congr h_combined_eq
  have h_combined_sum :
      (∑' i, A i) - (∑' i, B i) + h • (∑' i, C i) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ψ i • ⟪b i, T⟫_ℝ • b i := by
    have hh' := h_hsum_combined.tsum_eq
    rw [← hh']
    exact h_combined_sum_eq
  rw [show ((∑' i, A i) : TensorL2 r s g)
      - (∑' i, B i) + h • (∑' i, C i) = _ from h_combined_sum]
  -- Pointwise bound on |ψ i|.
  have h_psi_bound : ∀ i,
      |ψ i| ≤ tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2 := by
    intro i
    simp only [hψ_def]
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have h_taylor := tensor_exp_neg_taylor_bound
      (k := k) (t := t) ht (h := h) hh hlam
    have h_paren_eq : ∀ x y : ℝ,
        Real.exp (-x * y) = Real.exp (-(x * y)) := by
      intro x y; congr 1; ring
    have h_lhs_eq :
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
            (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t + h)) -
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) +
          h * ((TensorEigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) =
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * (t + h))) -
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t)) +
            TensorEigenIdx.lambda (I := I) (M := M) i * h *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t))) := by
      rw [h_paren_eq (TensorEigenIdx.lambda (I := I) (M := M) i) (t + h),
          h_paren_eq (TensorEigenIdx.lambda (I := I) (M := M) i) t]
      rw [pow_succ]
      ring
    rw [h_lhs_eq]
    exact h_taylor
  set Cψ : ℝ := tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2
    with hCψ_def
  have hCψ_nn : 0 ≤ Cψ := by
    simp only [hCψ_def]
    apply mul_nonneg
    · exact tensorHeatPowerCoeffBoundCalc_nonneg (k + 2)
        (by linarith : (0 : ℝ) < t / 2)
    · exact sq_nonneg _
  have h_summand_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ψ i • ⟪b i, T⟫_ℝ • b i) =
      (fun i => (ψ i * ⟪b i, T⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_summand_eq]
  have h_psi_sq_le : ∀ i, (ψ i) ^ 2 ≤ Cψ ^ 2 := by
    intro i
    have h_abs := h_psi_bound i
    have h_abs_nn : 0 ≤ |ψ i| := abs_nonneg _
    have h_sq_eq : (ψ i) ^ 2 = |ψ i| ^ 2 := (sq_abs _).symm
    rw [h_sq_eq]
    exact pow_le_pow_left₀ h_abs_nn h_abs 2
  have h_f_sq_le : ∀ i, (ψ i * ⟪b i, T⟫_ℝ) ^ 2 ≤ Cψ ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 := by
    intro i
    have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
    calc (ψ i * ⟪b i, T⟫_ℝ) ^ 2
        = (ψ i) ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 := by ring
      _ ≤ Cψ ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (h_psi_sq_le i) h_inner_sq_nn
  -- Square-summability of basis coefficients.
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
  have h_summable_f_sq :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (ψ i * ⟪b i, T⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ h_f_sq_le
      (h_coeff_sq_summable.mul_left (Cψ ^ 2))
    intro i; positivity
  have h_norm_sq_eq := tensorOrthonormal_norm_sq_eq_tsum_sq
    (I := I) (M := M) h_atlas (fun i => ψ i * ⟪b i, T⟫_ℝ) h_summable_f_sq
  change ‖∑' i, (ψ i * ⟪b i, T⟫_ℝ) • b i‖ ≤ Cψ * ‖T‖
  have h_norm_sq_le : ‖∑' i, (ψ i * ⟪b i, T⟫_ℝ) • b i‖ ^ 2 ≤
      Cψ ^ 2 * ‖T‖ ^ 2 := by
    rw [h_norm_sq_eq]
    have h_dom : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (ψ i * ⟪b i, T⟫_ℝ) ^ 2 ≤
          Cψ ^ 2 * ∑' i, (⟪b i, T⟫_ℝ) ^ 2 := by
      have h_step : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          (ψ i * ⟪b i, T⟫_ℝ) ^ 2 ≤
            ∑' i, Cψ ^ 2 * (⟪b i, T⟫_ℝ) ^ 2 :=
        Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq
          (h_coeff_sq_summable.mul_left (Cψ ^ 2))
      rw [tsum_mul_left] at h_step
      exact h_step
    refine le_trans h_dom ?_
    have h_parseval :=
      tensorParseval_norm_sq (I := I) (M := M) h_atlas T
    have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪b i, T⟫_ℝ‖ ^ 2) =
        (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
      funext i
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq] at h_parseval
    nlinarith [h_parseval, sq_nonneg Cψ]
  have h_lhs_nn : 0 ≤ ‖∑' i, (ψ i * ⟪b i, T⟫_ℝ) • b i‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ Cψ * ‖T‖ := mul_nonneg hCψ_nn (norm_nonneg _)
  have h_rhs_sq : (Cψ * ‖T‖) ^ 2 = Cψ ^ 2 * ‖T‖ ^ 2 := by ring
  rw [← h_rhs_sq] at h_norm_sq_le
  exact (abs_le_of_sq_le_sq' h_norm_sq_le h_rhs_nn).2

/-! ## Operator-norm differentiability -/

set_option synthInstance.maxHeartbeats 400000 in
/-- For `0 < t`, `s ↦ tensorHeatPower g r s h_atlas k s` has
operator-norm derivative `-tensorHeatPower g r s h_atlas (k+1) t` at
`t`. -/
theorem hasDerivAt_tensorHeatPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
      (-tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have ht2_pos : (0 : ℝ) < t / 2 := by linarith
  set Cb := tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) with hCb_def
  have hCb_nn : 0 ≤ Cb := tensorHeatPowerCoeffBoundCalc_nonneg (k + 2) ht2_pos
  have hCb1_pos : 0 < Cb + 1 := by linarith
  set δ : ℝ := min (t / 2) (ε / (Cb + 1)) with hδ_def
  have hδ_pos : 0 < δ := by
    apply lt_min ht2_pos
    exact div_pos hε hCb1_pos
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Metric.ball (0 : ℝ) δ, Metric.ball_mem_nhds 0 hδ_pos, ?_⟩
  intro h hh
  rw [Metric.mem_ball] at hh
  rw [dist_zero_right, Real.norm_eq_abs] at hh
  have h_abs_le_t2 : |h| ≤ t / 2 := by
    have := min_le_left (t / 2) (ε / (Cb + 1))
    linarith [hh]
  have h_abs_lt_eC : |h| < ε / (Cb + 1) := by
    have := min_le_right (t / 2) (ε / (Cb + 1))
    linarith [hh]
  have h_op_bound :
      ‖tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) -
          tensorHeatPower (I := I) (M := M) g r s h_atlas k t -
          h • -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t‖ ≤
        Cb * h ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro T
    have h_eq :
        tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) -
            tensorHeatPower (I := I) (M := M) g r s h_atlas k t -
            h • -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t =
          tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) -
            tensorHeatPower (I := I) (M := M) g r s h_atlas k t +
            h • tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t := by
      rw [show h • -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t =
          -(h • tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t) from by
        rw [smul_neg]]
      abel
    rw [h_eq]
    rw [show (tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) -
          tensorHeatPower (I := I) (M := M) g r s h_atlas k t +
            h • tensorHeatPower
              (I := I) (M := M) g r s h_atlas (k + 1) t) T =
        tensorHeatPower (I := I) (M := M) g r s h_atlas k (t + h) T -
          tensorHeatPower (I := I) (M := M) g r s h_atlas k t T +
            h • tensorHeatPower
              (I := I) (M := M) g r s h_atlas (k + 1) t T from rfl]
    have h_taylor := tensorNorm_heatPower_taylor_remainder
      (I := I) (M := M) h_atlas k ht h_abs_le_t2 T
    rw [show Cb * h ^ 2 * ‖T‖ =
        (tensorHeatPowerCoeffBoundCalc (k + 2) (t / 2) * h ^ 2) * ‖T‖ from rfl]
    exact h_taylor
  refine le_trans h_op_bound ?_
  have h_h2_eq : h ^ 2 = |h| * |h| := by
    rw [sq]
    rw [show h * h = |h| * |h| from by rw [← abs_mul]; rw [abs_mul_self]]
  rw [h_h2_eq]
  rw [show Cb * (|h| * |h|) = Cb * |h| * |h| from by ring]
  rw [show ε * ‖h‖ = ε * |h| from by rw [Real.norm_eq_abs]]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h_step : (Cb + 1) * |h| < ε := by
    have h_mul_lt : (Cb + 1) * |h| < (Cb + 1) * (ε / (Cb + 1)) :=
      mul_lt_mul_of_pos_left h_abs_lt_eC hCb1_pos
    rw [mul_div_cancel₀ ε (ne_of_gt hCb1_pos)] at h_mul_lt
    exact h_mul_lt
  linarith [abs_nonneg h, h_step]

/-- Specialization: `s ↦ tensorHeatSemigroup g r s h_atlas s` has
operator-norm derivative `-tensorHeatPower g r s h_atlas 1 t` at
`t > 0`. -/
theorem hasDerivAt_tensorHeatSemigroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u)
      (-tensorHeatPower (I := I) (M := M) g r s h_atlas 1 t) t := by
  have h := hasDerivAt_tensorHeatPower (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas 0 ht
  have h_funext :
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas 0 u) =
      (fun u : ℝ => tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u) := by
    funext u; exact tensorHeatPower_zero (I := I) (M := M) g r s h_atlas u
  rw [h_funext] at h
  exact h

/-! ## Iterated derivatives and `C^∞` on `(0, ∞)` -/

/-- For every `0 < t`, `s ↦ tensorHeatPower g r s h_atlas k s` is
differentiable at `t`. -/
theorem differentiableAt_tensorHeatPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u) t :=
  (hasDerivAt_tensorHeatPower (I := I) (M := M) h_atlas k ht).differentiableAt

/-- `s ↦ tensorHeatPower g r s h_atlas k s` is differentiable on
`(0, ∞)`. -/
theorem differentiableOn_tensorHeatPower_Ioi
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ) :
    DifferentiableOn ℝ
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
      (Set.Ioi 0) := by
  intro t ht
  exact (differentiableAt_tensorHeatPower
    (I := I) (M := M) h_atlas k ht).differentiableWithinAt

/-- Continuity of `s ↦ tensorHeatPower g r s h_atlas k s` at every
`t > 0`. -/
theorem continuousAt_tensorHeatPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u) t :=
  (hasDerivAt_tensorHeatPower (I := I) (M := M) h_atlas k ht).continuousAt

/-- `s ↦ tensorHeatPower g r s h_atlas k s` is continuous on
`(0, ∞)`. -/
theorem continuousOn_tensorHeatPower_Ioi
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ) :
    ContinuousOn
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
      (Set.Ioi 0) :=
  fun _ ht =>
    (continuousAt_tensorHeatPower
      (I := I) (M := M) h_atlas k ht).continuousWithinAt

/-- The derivative of `s ↦ tensorHeatPower g r s h_atlas k s` on
`(0, ∞)` is `-tensorHeatPower g r s h_atlas (k+1) s`. -/
theorem deriv_tensorHeatPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ =>
        tensorHeatPower (I := I) (M := M) g r s h_atlas k u) t =
      -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) t :=
  (hasDerivAt_tensorHeatPower (I := I) (M := M) h_atlas k ht).deriv

set_option synthInstance.maxHeartbeats 400000 in
/-- The `j`-th iterated derivative on `(0, ∞)` of `s ↦
tensorHeatSemigroup g r s h_atlas s` at `t` is `(-1)^j •
tensorHeatPower g r s h_atlas j t`. -/
theorem iteratedDerivWithin_tensorHeatSemigroup_Ioi
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    ∀ j : ℕ, ∀ {t : ℝ}, 0 < t →
      iteratedDerivWithin j
          (fun u : ℝ =>
            tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u)
          (Set.Ioi 0) t =
        (-1 : ℝ) ^ j •
          tensorHeatPower (I := I) (M := M) g r s h_atlas j t := by
  intro j
  induction j with
  | zero =>
    intro t ht
    simp only [iteratedDerivWithin_zero, pow_zero, one_smul]
    rw [tensorHeatPower_zero]
  | succ j ih =>
    intro t ht
    have hOi_unique : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := uniqueDiffOn_Ioi 0
    have ht_mem : t ∈ Set.Ioi (0 : ℝ) := ht
    rw [iteratedDerivWithin_succ]
    have h_eq_on : Set.EqOn
        (iteratedDerivWithin j
          (fun u : ℝ =>
            tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u)
          (Set.Ioi 0))
        (fun u : ℝ => (-1 : ℝ) ^ j •
          tensorHeatPower (I := I) (M := M) g r s h_atlas j u)
        (Set.Ioi 0) := by
      intro u hu
      exact ih hu
    have h_dw_eq :
        derivWithin (iteratedDerivWithin j
          (fun u : ℝ =>
            tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u)
          (Set.Ioi 0)) (Set.Ioi 0) t =
        derivWithin (fun u : ℝ => (-1 : ℝ) ^ j •
          tensorHeatPower (I := I) (M := M) g r s h_atlas j u)
          (Set.Ioi 0) t :=
      derivWithin_congr h_eq_on (h_eq_on ht_mem)
    rw [h_dw_eq]
    have hd : HasDerivAt
        (fun u : ℝ => (-1 : ℝ) ^ j •
          tensorHeatPower (I := I) (M := M) g r s h_atlas j u)
        ((-1 : ℝ) ^ j •
          -tensorHeatPower (I := I) (M := M) g r s h_atlas (j + 1) t) t := by
      have hbase := hasDerivAt_tensorHeatPower
        (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas j ht
      exact hbase.const_smul ((-1 : ℝ) ^ j)
    have hd_within :
        HasDerivWithinAt
          (fun u : ℝ => (-1 : ℝ) ^ j •
            tensorHeatPower (I := I) (M := M) g r s h_atlas j u)
          ((-1 : ℝ) ^ j •
            -tensorHeatPower (I := I) (M := M) g r s h_atlas (j + 1) t)
          (Set.Ioi 0) t :=
      hd.hasDerivWithinAt
    have h_unique : UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) t :=
      hOi_unique t ht
    rw [hd_within.derivWithin h_unique]
    rw [pow_succ]
    rw [show (-1 : ℝ) ^ j * -1 = -((-1 : ℝ) ^ j) from by ring]
    rw [neg_smul, smul_neg]

set_option synthInstance.maxHeartbeats 400000 in
/-- `s ↦ tensorHeatPower g r s h_atlas k s` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_tensorHeatPower_Ioi
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
      (Set.Ioi 0) := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing k with
  | zero =>
    change ContDiffOn ℝ 0
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
      (Set.Ioi 0)
    rw [contDiffOn_zero]
    exact continuousOn_tensorHeatPower_Ioi (I := I) (M := M) h_atlas k
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 from by
        push_cast; rfl]
    rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ioi 0)]
    refine ⟨?_, ?_, ?_⟩
    · exact differentiableOn_tensorHeatPower_Ioi
        (I := I) (M := M) h_atlas k
    · intro h_omega
      exfalso
      simp at h_omega
    · have h_deriv_eq : Set.EqOn
          (derivWithin (fun u : ℝ =>
              tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
            (Set.Ioi 0))
          (fun u : ℝ =>
            -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) u)
          (Set.Ioi 0) := by
        intro u hu
        have hd := hasDerivAt_tensorHeatPower
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas k hu
        have hd_within :
            HasDerivWithinAt
              (fun u : ℝ =>
                tensorHeatPower (I := I) (M := M) g r s h_atlas k u)
              (-tensorHeatPower
                (I := I) (M := M) g r s h_atlas (k + 1) u)
              (Set.Ioi 0) u :=
          hd.hasDerivWithinAt
        rw [hd_within.derivWithin ((uniqueDiffOn_Ioi 0) u hu)]
      apply ContDiffOn.congr _ h_deriv_eq
      have h_neg :
          (fun u : ℝ =>
              -tensorHeatPower (I := I) (M := M) g r s h_atlas (k + 1) u) =
          (fun u : ℝ =>
              -1 • tensorHeatPower
                (I := I) (M := M) g r s h_atlas (k + 1) u) := by
        funext u; rw [neg_one_smul]
      rw [h_neg]
      exact (ih (k + 1)).const_smul _

/-- `s ↦ tensorHeatSemigroup g r s h_atlas s` is `C^∞` on `(0, ∞)`. -/
theorem contDiffOn_tensorHeatSemigroup_Ioi
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    ContDiffOn ℝ ∞
      (fun u : ℝ => tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u)
      (Set.Ioi 0) := by
  have h := contDiffOn_tensorHeatPower_Ioi (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas 0
  have h_eq :
      (fun u : ℝ => tensorHeatPower (I := I) (M := M) g r s h_atlas 0 u) =
      (fun u : ℝ => tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u) := by
    funext u; exact tensorHeatPower_zero (I := I) (M := M) g r s h_atlas u
  rw [h_eq] at h
  exact h

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
