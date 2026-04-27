import DifferentialGeometry.Integral.Integration.GlobalPairing.Algebra

/-!
# Global `L²` Cauchy–Schwarz inequality and triangle inequality

Let `M` be a smooth finite-dimensional manifold modelled on a real normed
space `E` equipped with a smooth Riemannian metric `g`. Building on the
algebraic and `MemL2`-closure machinery from `GlobalPairing.Algebra`,
this file proves the global `L²` Cauchy–Schwarz inequality and its
absolute-value form, together with the triangle inequality for the
global `L²` norm.

The natural hypotheses are diagonal `MemL2` for both sections plus
integrability of the cross pointwise pairing — the same pattern as the
linearity statements in the companion file.

* `tensorL2Inner_sq_le_mul` — squared form
  `(∫ ⟨S, T⟩)² ≤ (∫ ⟨S, S⟩) (∫ ⟨T, T⟩)`;
* `abs_tensorL2Inner_le` — absolute-value form
  `|∫ ⟨S, T⟩| ≤ ‖S‖_{L²} ‖T‖_{L²}`;
* `tensorL2Norm_add_le` — triangle inequality
  `‖S + T‖_{L²} ≤ ‖S‖_{L²} + ‖T‖_{L²}`.

The squared form is established by the standard "discriminant" argument:
the real quadratic
`q(t) = ⟨S + t • T, S + t • T⟩_{L²} = a + 2 t b + t² c ≥ 0`
is non-negative for all `t : ℝ`, where `a = ⟨S, S⟩, b = ⟨S, T⟩,
c = ⟨T, T⟩`. Case analysis on `c = 0` vs `c > 0` then yields `b² ≤ a c`.
-/

noncomputable section

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Integration

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Canonical measurable-space and Borel-space instances on `E` and `M`

File-local Borel structures, matching the other files in this directory.
Declared `local` so they do not leak into external typeclass search. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- **Cauchy–Schwarz** for the global metric-induced `L²` inner product on
mixed `(r, s)`-tensor section fields, in squared form: the squared `L²`
inner product is bounded by the product of the diagonal `L²` inner
products. The hypotheses are diagonal `MemL2` of both sections plus
integrability of the cross pointwise pairing. -/
theorem tensorL2Inner_sq_le_mul
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (tensorL2Inner (I := I) (M := M) g r s S T) ^ 2 ≤
      tensorL2Inner (I := I) (M := M) g r s S S *
        tensorL2Inner (I := I) (M := M) g r s T T := by
  -- Set up `a, b, c`.
  set a := tensorL2Inner (I := I) (M := M) g r s S S with ha_def
  set b := tensorL2Inner (I := I) (M := M) g r s S T with hb_def
  set c := tensorL2Inner (I := I) (M := M) g r s T T with hc_def
  have ha_nn : 0 ≤ a := tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hc_nn : 0 ≤ c := tensorL2Inner_nonneg (I := I) (M := M) g r s T
  -- For every real `t`, the quadratic `a + 2tb + t² c ≥ 0`.
  -- Strategy: rewrite the LHS as an integral of the pointwise diagonal
  -- form on `S + t • T`, which is non-negative pointwise.
  have hquad : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) + t ^ 2 * c := by
    intro t
    -- Pointwise identity:
    -- ⟨S(x) + t T(x), S(x) + t T(x)⟩ = ⟨S(x), S(x)⟩ + 2 t ⟨S(x), T(x)⟩ + t² ⟨T(x), T(x)⟩
    have hpoint : ∀ x : M,
        tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x) =
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            2 * (t *
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
            t ^ 2 *
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x) := by
      intro x
      have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x (T x) (S x)
      change tensorInnerPointwise (I := I) (M := M) g r s x (S x + t • T x) (S x + t • T x) =
        _
      rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
          tensorInnerPointwise_add_right, tensorInnerPointwise_smul_left,
          tensorInnerPointwise_smul_right, tensorInnerPointwise_smul_left,
          tensorInnerPointwise_smul_right]
      -- After rewriting, goal has ⟨T, S⟩ ; replace with ⟨S, T⟩ via symm.
      rw [hsymm]
      ring
    -- Integrate the pointwise inequality `0 ≤ ⟨_, _⟩` from non-negativity
    -- pointwise.
    have h_nn_point : ∀ x : M,
        0 ≤ tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x) := fun x =>
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s x ((S + t • T) x)
    -- The integrand on the diagonal of `S + t • T` is integrable: it equals
    -- the pointwise expansion, whose pieces are `MemL2 S`, the cross, the
    -- cross again, and `MemL2 T` (with scalar coefficients).
    have h_cross_const_mul : MeasureTheory.Integrable
        (fun x => 2 * (t *
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      have : MeasureTheory.Integrable
          (fun x => t *
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
          (riemannianVolumeMeasure (I := I) (M := M) g) := hST.const_mul t
      exact this.const_mul 2
    have h_diag_T : MeasureTheory.Integrable
        (fun x => t ^ 2 *
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hTT.integrable_inner_self.const_mul (t ^ 2)
    -- Integral of the pointwise expansion: by linearity of the Bochner integral.
    have h_int_eq :
        ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          a + 2 * (t * b) + t ^ 2 * c := by
      -- Rewrite the integrand pointwise.
      have hcongr :
          (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
              ((S + t • T) x) ((S + t • T) x)) =
            (fun x =>
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
                2 * (t *
                  tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
                t ^ 2 *
                  tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)) :=
        funext hpoint
      rw [hcongr]
      -- Distribute the integral: `∫ (f + g + h) = ∫ f + ∫ g + ∫ h`.
      have hadd_outer :=
        MeasureTheory.integral_add
          (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (f := fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
              2 * (t * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
          (g := fun x =>
            t ^ 2 * tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
          (hSS.integrable_inner_self.add h_cross_const_mul) h_diag_T
      rw [hadd_outer]
      have hadd_mid :=
        MeasureTheory.integral_add
          (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (f := fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
          (g := fun x =>
            2 * (t * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
          hSS.integrable_inner_self h_cross_const_mul
      rw [hadd_mid]
      -- Reduce the constant-multiple integrals.
      have hb_const :
          ∫ x, 2 * (t *
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            2 * (t *
              ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hc_const :
          ∫ x, t ^ 2 *
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            t ^ 2 *
              ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_const_mul (t ^ 2) _
      rw [hb_const, hc_const]
      -- Now unfold `a, b, c` to match.
      change _ = tensorL2Inner (I := I) (M := M) g r s S S +
        2 * (t * tensorL2Inner (I := I) (M := M) g r s S T) +
        t ^ 2 * tensorL2Inner (I := I) (M := M) g r s T T
      unfold tensorL2Inner
      rfl
    -- Combine non-negativity with the integral identity.
    have h_int_nn :
        0 ≤ ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integral_nonneg (fun x => h_nn_point x)
    rw [h_int_eq] at h_int_nn
    exact h_int_nn
  -- Discriminant test. Two cases on `c = 0` vs `c > 0`.
  rcases (lt_or_eq_of_le hc_nn) with hc_pos | hc_zero
  · -- Case `c > 0`. Take `t = -b / c`. Then
    -- `0 ≤ a + 2 * (-b/c) * b + (-b/c)² * c = a - b²/c`,
    -- so `b² ≤ a c`.
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have h := hquad (-b / c)
    have hsimp : a + 2 * (-b / c * b) + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp
      ring
    rw [hsimp] at h
    -- Multiply both sides by `c > 0`.
    have hmul : 0 * c ≤ (a - b ^ 2 / c) * c :=
      mul_le_mul_of_nonneg_right h (le_of_lt hc_pos)
    rw [zero_mul] at hmul
    have hrhs : (a - b ^ 2 / c) * c = a * c - b ^ 2 := by
      field_simp
    rw [hrhs] at hmul
    linarith
  · -- Case `c = 0`. The affine function `t ↦ a + 2tb` is non-negative on all
    -- of ℝ, which forces `b = 0`. Then `b² = 0 ≤ a · 0 = a c`.
    have hc_eq : c = 0 := hc_zero.symm
    have hquad' : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) := by
      intro t
      have h := hquad t
      rw [hc_eq, mul_zero, add_zero] at h
      exact h
    have hb_zero : b = 0 := by
      by_contra hbne
      rcases lt_or_gt_of_ne hbne with hb_neg | hb_pos
      · -- `b < 0`, so for large `t`, `a + 2tb` is very negative. Take
        -- `t := (a + 1) / (-2 b)` so that `2 t b = -(a + 1)`.
        have hneg2b : -(2 * b) > 0 := by linarith
        set t₀ := (a + 1) / (-(2 * b)) with ht₀_def
        have ht₀_eq : 2 * (t₀ * b) = -(a + 1) := by
          rw [ht₀_def]
          field_simp
        have h := hquad' t₀
        rw [ht₀_eq] at h
        linarith
      · -- `b > 0`, so for very negative `t`, `a + 2tb` is very negative.
        -- Take `t := -(a + 1) / (2 b)` so that `2 t b = -(a + 1)`.
        have h2b : 2 * b > 0 := by linarith
        set t₀ := -(a + 1) / (2 * b) with ht₀_def
        have ht₀_eq : 2 * (t₀ * b) = -(a + 1) := by
          rw [ht₀_def]
          field_simp
        have h := hquad' t₀
        rw [ht₀_eq] at h
        linarith
    rw [hb_zero, hc_eq, mul_zero]
    simp

set_option linter.unusedSectionVars false in
/-- **Cauchy–Schwarz** for the global metric-induced `L²` inner product, in
absolute-value form: the absolute value of the `L²` inner product is
bounded by the product of the `L²` norms. -/
theorem abs_tensorL2Inner_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    |tensorL2Inner (I := I) (M := M) g r s S T| ≤
      tensorL2Norm (I := I) (M := M) g r s S *
        tensorL2Norm (I := I) (M := M) g r s T := by
  unfold tensorL2Norm
  have hSS_nn : 0 ≤ tensorL2Inner (I := I) (M := M) g r s S S :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hTT_nn : 0 ≤ tensorL2Inner (I := I) (M := M) g r s T T :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s T
  have hcs := tensorL2Inner_sq_le_mul (I := I) (M := M) g r s S T hSS hTT hST
  -- |b| = √(b²) ≤ √(a c) = √a √c.
  have habs_sq :
      |tensorL2Inner (I := I) (M := M) g r s S T| =
        Real.sqrt
          ((tensorL2Inner (I := I) (M := M) g r s S T) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs_sq]
  have h1 : Real.sqrt ((tensorL2Inner (I := I) (M := M) g r s S T) ^ 2) ≤
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S *
        tensorL2Inner (I := I) (M := M) g r s T T) :=
    Real.sqrt_le_sqrt hcs
  have h2 : Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S *
      tensorL2Inner (I := I) (M := M) g r s T T) =
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S) *
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s T T) :=
    Real.sqrt_mul hSS_nn _
  rw [h2] at h1
  exact h1

set_option linter.unusedSectionVars false in
/-- **Triangle inequality** for the global metric-induced `L²` norm. The
`L²` norm of the sum is bounded by the sum of the `L²` norms, under the
natural integrability hypotheses needed to expand the squared norm. -/
theorem tensorL2Norm_add_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Norm (I := I) (M := M) g r s (S + T) ≤
      tensorL2Norm (I := I) (M := M) g r s S +
        tensorL2Norm (I := I) (M := M) g r s T := by
  -- Set up `a, b, c, A := √a, B := √b in absolute, C := √c`.
  set a := tensorL2Inner (I := I) (M := M) g r s S S with ha_def
  set b := tensorL2Inner (I := I) (M := M) g r s S T with hb_def
  set c := tensorL2Inner (I := I) (M := M) g r s T T with hc_def
  have ha_nn : 0 ≤ a := tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hc_nn : 0 ≤ c := tensorL2Inner_nonneg (I := I) (M := M) g r s T
  have hA_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hC_nn : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  -- Step 1: `‖S + T‖² = a + 2 b + c` (no integrability needed beyond `hST`).
  have h_sumSq :
      tensorL2Inner (I := I) (M := M) g r s (S + T) (S + T) =
        a + 2 * b + c := by
    -- Pointwise: ⟨S+T, S+T⟩ = ⟨S, S⟩ + ⟨S, T⟩ + ⟨T, S⟩ + ⟨T, T⟩
    --                       = a + 2b + c (using symmetry).
    have hpoint : ∀ x : M,
        tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + T) x) ((S + T) x) =
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
            tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x) := by
      intro x
      have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x (T x) (S x)
      change tensorInnerPointwise (I := I) (M := M) g r s x (S x + T x) (S x + T x) =
        _
      rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
          tensorInnerPointwise_add_right, hsymm]
      ring
    -- Integrability of pieces: `⟨S, S⟩ + (⟨S, T⟩ + ⟨S, T⟩) + ⟨T, T⟩`.
    have h_two_cross : MeasureTheory.Integrable
        (fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hST.add hST
    -- Integrate.
    unfold tensorL2Inner
    have hcongr :
        (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + T) x) ((S + T) x)) =
          (fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
              (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
                tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)) :=
      funext hpoint
    rw [hcongr]
    -- Decompose by linearity step by step.
    have hadd_outer :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
        (hS.integrable_inner_self.add h_two_cross)
        hT.integrable_inner_self
    rw [hadd_outer]
    have hadd_mid :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        hS.integrable_inner_self h_two_cross
    rw [hadd_mid]
    have hadd_inner :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        hST hST
    rw [hadd_inner]
    -- Unfold `a, b, c` (definitions of `tensorL2Inner`).
    change _ = tensorL2Inner (I := I) (M := M) g r s S S +
        2 * tensorL2Inner (I := I) (M := M) g r s S T +
        tensorL2Inner (I := I) (M := M) g r s T T
    unfold tensorL2Inner
    ring
  -- Step 2: Use Cauchy–Schwarz `|b| ≤ √a · √c`. So
  -- `a + 2b + c ≤ a + 2 √a √c + c = (√a + √c)²`.
  have h_abs_le : |b| ≤ Real.sqrt a * Real.sqrt c := by
    have habs := abs_tensorL2Inner_le (I := I) (M := M) g r s S T hS hT hST
    -- `tensorL2Norm g r s S = √a` and similarly for `T`.
    have hSnorm : tensorL2Norm (I := I) (M := M) g r s S = Real.sqrt a := rfl
    have hTnorm : tensorL2Norm (I := I) (M := M) g r s T = Real.sqrt c := rfl
    rw [hSnorm, hTnorm] at habs
    exact habs
  have h_b_le : b ≤ Real.sqrt a * Real.sqrt c :=
    le_of_abs_le h_abs_le
  have h_sumSq_le : a + 2 * b + c ≤ (Real.sqrt a + Real.sqrt c) ^ 2 := by
    have hsq_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
    have hsq_c : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc_nn
    nlinarith [h_b_le, hA_nn, hC_nn, hsq_a, hsq_c]
  -- Step 3: Take square roots.
  unfold tensorL2Norm
  -- Goal: `√⟨S+T, S+T⟩_{L²} ≤ √a + √c`.
  rw [h_sumSq]
  have hAC_nn : 0 ≤ Real.sqrt a + Real.sqrt c := add_nonneg hA_nn hC_nn
  have hSqAC : Real.sqrt ((Real.sqrt a + Real.sqrt c) ^ 2) =
      Real.sqrt a + Real.sqrt c :=
    Real.sqrt_sq hAC_nn
  calc Real.sqrt (a + 2 * b + c)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt c) ^ 2) :=
        Real.sqrt_le_sqrt h_sumSq_le
    _ = Real.sqrt a + Real.sqrt c := hSqAC

end Integration
end Integral
end DifferentialGeometry

end
