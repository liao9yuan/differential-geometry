import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenBasis
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Tensor heat semigroup: eigen-index and per-eigenvalue heat coefficient

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
introduces the sigma-typed basis-index `TensorEigenIdx g r s` for the
L²-side tensor eigenbasis of the resolvent

  `R := tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`,

and proves the basic non-negativity / unit-interval bound of the per-
eigenvalue heat coefficient `exp(-λ_i · t)` for `t ≥ 0`, where `λ_i` is
the connection-Laplacian eigenvalue translated from the corresponding
nonzero resolvent eigenvalue via `λ = (1 - μ)/μ`.

This is the tensor analogue of the scalar `EigenIdx` / `lambda` /
`heat_coeff_mem_unit_interval` triple, and serves as the indexing layer
for the eventual tensor heat semigroup
`∑' i, exp(-λ_i · t) • ⟪b i, T⟫ • b i`.

## Main definitions

* `TensorEigenIdx g r s` — the sigma-indexed basis-index type for the
  L² eigenbasis: pairs of a nonzero resolvent eigenvalue and a finite
  index into its eigenspace orthonormal basis.
* `TensorEigenIdx.lambda` — the connection-Laplacian eigenvalue
  attached to a sigma-index, defined as
  `tensorLaplacianEigenvalueOf μ.val = (1 - μ.val) / μ.val`.

## Main results

* `tensor_lambda_nonneg` — `0 ≤ TensorEigenIdx.lambda i`.
* `tensor_heat_coeff_mem_unit_interval` — for `t ≥ 0`,
  `exp(-λ_i · t) ∈ (0, 1]`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`), so
the translated Laplacian eigenvalue `λ = (1 - μ)/μ` is non-negative for
`μ ∈ (0, 1]`. The per-eigenvalue heat coefficient is then
`exp(-λ · t)`, contractive for `t ≥ 0`.
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

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The tensor eigen-index type and the heat coefficient -/

/-- Sigma-index for the tensor eigenbasis: pairs an eigenvalue `μ`
(nonzero, nontrivial eigenspace) with a finite-dimensional eigenspace
index. -/
abbrev TensorEigenIdx (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  Σ μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s,
    Fin (Module.finrank ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val))

/-- The connection-Laplacian eigenvalue associated with the resolvent
eigenvalue at sigma index `i`, defined as `(1 - μ)/μ`. -/
noncomputable abbrev TensorEigenIdx.lambda
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorLaplacianEigenvalueOf i.fst.val

/-- The per-eigenvalue Laplacian eigenvalue is non-negative. -/
theorem tensor_lambda_nonneg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i := by
  -- Extract an eigenvector witness from the eigenvalue subtype.
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  have h_mem_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval
      (I := I) (M := M) g r s hu_in hu_ne
  exact tensorLaplacianEigenvalueOf_nonneg_of_resolventEigenvalue h_mem_unit

/-- The per-eigenvalue heat coefficient `exp(-λ_i · t)` is in `(0, 1]`
for non-negative time. -/
theorem tensor_heat_coeff_mem_unit_interval
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ∧
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff]
  have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

/-- The squared heat coefficient is bounded by `1` for `t ≥ 0`. -/
lemma tensor_heat_coeff_sq_le_one
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 := by
  obtain ⟨h_pos, h_le⟩ :=
    tensor_heat_coeff_mem_unit_interval (I := I) (M := M) i ht
  have h_nn : 0 ≤ Real.exp
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) := h_pos.le
  nlinarith [sq_nonneg
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1)]

/-! ## Square-summability of the basis Fourier coefficients (Parseval) -/

/-- Parseval-type square-summability of the tensor basis coefficients. -/
lemma tensorSummable_basis_coeff_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s) (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i, T⟫_ℝ‖ ^ 2) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_summable_smul : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum : HasSum (fun i => b.repr T i • b i) T := b.hasSum_repr T
    have h_eq : (fun i => b.repr T i • b i) =
        (fun i => ⟪b i, T⟫_ℝ • b i) := by
      funext i
      rw [b.repr_apply_apply]
    rw [h_eq] at h_hsum
    exact h_hsum.summable
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : TensorEigenIdx (I := I) (M := M) g r s => ⟪b i, T⟫_ℝ)
  have h_map_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i) (⟪b i, T⟫_ℝ)) =
      (fun i => ⟪b i, T⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
  rw [h_map_eq] at h_iff
  exact h_iff.mp h_summable_smul

/-- Parseval identity for the tensor eigenbasis: the squared L²-norm of
`T` equals the sum of the squared basis coefficients. -/
lemma tensorParseval_norm_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s) (T : TensorL2 r s g) :
    ‖T‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i, T⟫_ℝ‖ ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_par := b.tsum_inner_mul_inner T T
  have h_sq : ⟪T, T⟫_ℝ = ‖T‖ ^ 2 := real_inner_self_eq_norm_sq T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪T, b i⟫_ℝ * ⟪b i, T⟫_ℝ) =
      (fun i => ‖⟪b i, T⟫_ℝ‖ ^ 2) := by
    funext i
    rw [show ⟪T, b i⟫_ℝ = ⟪b i, T⟫_ℝ from real_inner_comm _ _,
        Real.norm_eq_abs, sq_abs, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

/-! ## Summability of the heat-eigenbasis series (for `t ≥ 0`) -/

/-- For `t ≥ 0`, the family of heat-coefficient–weighted tensor basis
terms is summable in `TensorL2 r s g`. -/
lemma tensorSummable_heatTerm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    {t : ℝ} (ht : 0 ≤ t) (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i, T⟫_ℝ •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_uniform i) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_sq_summable : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) ^ 2) := by
    have h_coeff_sq_summable :
        Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          (⟪b i, T⟫_ℝ) ^ 2) := by
      have h_norm_sq_summable :=
        tensorSummable_basis_coeff_sq
          (I := I) (M := M) h_uniform T
      have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
            ‖⟪b i, T⟫_ℝ‖ ^ 2) =
          (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
        funext i
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_eq] at h_norm_sq_summable
      exact h_norm_sq_summable
    refine Summable.of_nonneg_of_le ?_ ?_ h_coeff_sq_summable
    · intro i; positivity
    · intro i
      have h_sq_le :
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t))
              ^ 2 ≤ 1 :=
        tensor_heat_coeff_sq_le_one (I := I) (M := M) i ht
      have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
      calc
        (Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
              ⟪b i, T⟫_ℝ) ^ 2
            = (Real.exp
                (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
                (⟪b i, T⟫_ℝ) ^ 2 := by ring
        _ ≤ 1 * (⟪b i, T⟫_ℝ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
        _ = (⟪b i, T⟫_ℝ) ^ 2 := one_mul _
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪b i, T⟫_ℝ)
  have h_sq_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, T⟫_ℝ‖ ^ 2) =
      (fun i =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_map_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)
          (Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, T⟫_ℝ)) =
      (fun i =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
    rw [mul_smul]
  have h_summable_V : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)
          (Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, T⟫_ℝ)) := h_iff.mpr h_sq_summable
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

/-! ## Orthonormal lp-isometry identity for the tensor basis -/

/-- For any square-summable scalar family `f`, the orthonormal expansion
`∑' i, f i • b i` against the tensor eigenbasis has L²-squared-norm equal
to `∑' i, (f i)²`. -/
lemma tensorOrthonormal_norm_sq_eq_tsum_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_summable : Summable (fun i => (f i) ^ 2)) :
    ‖∑' i : TensorEigenIdx (I := I) (M := M) g r s, f i •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_uniform i‖ ^ 2 =
      ∑' i, (f i) ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_memℓp :
      Memℓp (fun i : TensorEigenIdx (I := I) (M := M) g r s => f i) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖f i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (f i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_cast
    rw [h_eq]
    exact h_summable
  set f_lp : lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 :=
    ⟨fun i => f i, h_memℓp⟩
  have h_iso_norm : ‖h_orthFam.linearIsometry f_lp‖ = ‖f_lp‖ :=
    h_orthFam.linearIsometry.norm_map f_lp
  have h_iso_apply : h_orthFam.linearIsometry f_lp =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s, f i • b i := by
    rw [h_orthFam.linearIsometry_apply f_lp]
    apply tsum_congr
    intro i
    rw [LinearIsometry.toSpanSingleton_apply]
  have h_lp_norm_sq : ‖f_lp‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s, (f i) ^ 2 := by
    have h_norm_sq := lp.norm_rpow_eq_tsum
      (p := 2)
      (E := fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
      (by norm_num) f_lp
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hpr] at h_norm_sq
    have h_lhs : ‖f_lp‖ ^ (2 : ℝ) = ‖f_lp‖ ^ 2 := by norm_cast
    rw [h_lhs] at h_norm_sq
    have h_rhs_eq :
        (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          ‖(f_lp : TensorEigenIdx (I := I) (M := M) g r s → ℝ) i‖
            ^ (2 : ℝ)) =
        ∑' i, (f i) ^ 2 := by
      apply tsum_congr
      intro i
      have h_eq_pt :
          (f_lp : TensorEigenIdx (I := I) (M := M) g r s → ℝ) i = f i :=
        rfl
      rw [h_eq_pt, Real.norm_eq_abs, ← sq_abs]
      norm_cast
    rw [h_rhs_eq] at h_norm_sq
    exact h_norm_sq
  have h_eq1 :
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s, f i • b i =
        h_orthFam.linearIsometry f_lp := h_iso_apply.symm
  rw [h_eq1, h_iso_norm, h_lp_norm_sq]

/-! ## Operator-norm bound on the heat-eigenbasis series (for `t ≥ 0`) -/

/-- For `t ≥ 0`, the squared L² norm of the heat-eigenbasis series is
bounded by `‖T‖²`. -/
private lemma tensorNorm_sq_heatTerm_sum_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    {t : ℝ} (ht : 0 ≤ t) (T : TensorL2 r s g) :
    ‖∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_uniform i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i‖ ^ 2 ≤
      ‖T‖ ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  -- Reform the summand: smul-smul folds into a single scalar smul.
  have h_summand_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T⟫_ℝ • b i) =
      (fun i =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, T⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_summand_eq]
  -- Define `f i := exp(-λ_i t) * ⟪b i, T⟫`.
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ := fun i =>
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
      ⟪b i, T⟫_ℝ
  -- Square-summability of `⟪b i, T⟫²` from Parseval.
  have h_coeff_sq_summable :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (⟪b i, T⟫_ℝ) ^ 2) := by
    have h_norm_sq_summable :=
      tensorSummable_basis_coeff_sq (I := I) (M := M) h_uniform T
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪b i, T⟫_ℝ‖ ^ 2) =
        (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
      funext i
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq] at h_norm_sq_summable
    exact h_norm_sq_summable
  -- Pointwise bound `(f i)² ≤ ⟪b i, T⟫²` from the heat-coefficient bound.
  have h_f_sq_le :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        (f i) ^ 2 ≤ (⟪b i, T⟫_ℝ) ^ 2 := by
    intro i
    have h_sq_le :
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2
            ≤ 1 :=
      tensor_heat_coeff_sq_le_one (I := I) (M := M) i ht
    have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ (⟪b i, T⟫_ℝ) ^ 2
    calc
      (f i) ^ 2
          = (Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, T⟫_ℝ) ^ 2 := by
                change (Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
                  ⟪b i, T⟫_ℝ) ^ 2 = _
                ring
      _ ≤ 1 * (⟪b i, T⟫_ℝ) ^ 2 := by
            apply mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
      _ = (⟪b i, T⟫_ℝ) ^ 2 := one_mul _
  have h_summable_f_sq :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ h_coeff_sq_summable
    · intro i; positivity
    · exact h_f_sq_le
  -- Apply the orthonormal `‖·‖² = ∑ (f i)²` formula and bound the tsum.
  have h_norm_sq_eq :=
    tensorOrthonormal_norm_sq_eq_tsum_sq
      (I := I) (M := M) h_uniform f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 ≤ ‖T‖ ^ 2
  rw [h_norm_sq_eq]
  have h_dom : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (f i) ^ 2 ≤
      ∑' i, (⟪b i, T⟫_ℝ) ^ 2 :=
    Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq h_coeff_sq_summable
  refine le_trans h_dom ?_
  -- Use Parseval to close.
  have h_parseval :=
    tensorParseval_norm_sq (I := I) (M := M) h_uniform T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖⟪b i, T⟫_ℝ‖ ^ 2) =
      (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_eq] at h_parseval
  linarith

/-- For `t ≥ 0`, the operator-norm bound `‖tensorHeatSemigroupFun T‖ ≤ ‖T‖`. -/
private lemma tensorNorm_heatTerm_sum_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    {t : ℝ} (ht : 0 ≤ t) (T : TensorL2 r s g) :
    ‖∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_uniform i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i‖ ≤ ‖T‖ := by
  have h_sq :=
    tensorNorm_sq_heatTerm_sum_le (I := I) (M := M) h_uniform ht T
  have h_rhs_nn : 0 ≤ ‖T‖ := norm_nonneg _
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

/-! ## Underlying linear map and CLM packaging -/

/-- The underlying function of the tensor heat semigroup at time `t`. -/
private noncomputable def tensorHeatSemigroupFun
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s) (t : ℝ)
    (T : TensorL2 r s g) : TensorL2 r s g :=
  ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
      ⟪tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_uniform i, T⟫_ℝ •
      tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_uniform i

/-- Additivity of `tensorHeatSemigroupFun` in the argument (for `t ≥ 0`). -/
private lemma tensorHeatSemigroupFun_add
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    {t : ℝ} (ht : 0 ≤ t) (T₁ T₂ : TensorL2 r s g) :
    tensorHeatSemigroupFun (I := I) (M := M) h_uniform t (T₁ + T₂) =
      tensorHeatSemigroupFun (I := I) (M := M) h_uniform t T₁ +
        tensorHeatSemigroupFun (I := I) (M := M) h_uniform t T₂ := by
  unfold tensorHeatSemigroupFun
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_summand_eq :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T₁ + T₂⟫_ℝ • b i =
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, T₁⟫_ℝ • b i) +
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, T₂⟫_ℝ • b i) := by
    intro i
    rw [inner_add_right, add_smul, smul_add]
  have h_sum_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T₁ + T₂⟫_ℝ • b i) =
      (fun i =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, T₁⟫_ℝ • b i) +
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, T₂⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  rw [Summable.tsum_add
    (tensorSummable_heatTerm (I := I) (M := M) h_uniform ht T₁)
    (tensorSummable_heatTerm (I := I) (M := M) h_uniform ht T₂)]

/-- Scalar-homogeneity of `tensorHeatSemigroupFun` (for `t ≥ 0`). -/
private lemma tensorHeatSemigroupFun_smul
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s)
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (T : TensorL2 r s g) :
    tensorHeatSemigroupFun (I := I) (M := M) h_uniform t (c • T) =
      c • tensorHeatSemigroupFun (I := I) (M := M) h_uniform t T := by
  unfold tensorHeatSemigroupFun
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  have h_summand_eq :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, c • T⟫_ℝ • b i =
        c • (Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, T⟫_ℝ • b i) := by
    intro i
    rw [real_inner_smul_right]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have h_sum_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, c • T⟫_ℝ • b i) =
      (fun i => c • (Real.exp
            (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  exact (tensorSummable_heatTerm (I := I) (M := M) h_uniform ht T).tsum_const_smul c

/-! ## The tensor heat semigroup CLM -/

/-- The tensor heat semigroup `e^{t Δ_∇}` on `TensorL2 r s g`.

For `t ≥ 0`: the spectral series
`T ↦ ∑' i, exp(-λ_i t) • ⟪b i, T⟫ • b i`
defines a contraction on `TensorL2 r s g` (operator norm `≤ 1`).

For `t < 0`: the operator is set to `0` (junk; downstream consumers should
always supply `0 ≤ t`). -/
noncomputable def tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g := by
  by_cases ht : 0 ≤ t
  · refine LinearMap.mkContinuous
      { toFun := tensorHeatSemigroupFun (I := I) (M := M) h_uniform t
        map_add' :=
          tensorHeatSemigroupFun_add (I := I) (M := M) h_uniform ht
        map_smul' := fun c T =>
          tensorHeatSemigroupFun_smul (I := I) (M := M) h_uniform ht c T } 1 ?_
    intro T
    change ‖tensorHeatSemigroupFun (I := I) (M := M) h_uniform t T‖ ≤ 1 * ‖T‖
    rw [one_mul]
    exact tensorNorm_heatTerm_sum_le (I := I) (M := M) h_uniform ht T
  · exact 0

/-- Application formula for `tensorHeatSemigroup g r s h_uniform t T` when
`t ≥ 0`: it equals the explicit eigenbasis sum. -/
theorem tensorHeatSemigroup_apply_of_nonneg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_uniform : uniformTensorChartSobolevBound g r s}
    {t : ℝ} (ht : 0 ≤ t) (T : TensorL2 r s g) :
    tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t T =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_uniform i, T⟫_ℝ •
          tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_uniform i := by
  unfold tensorHeatSemigroup
  rw [dif_pos ht]
  rfl

/-- For `t < 0`, the tensor heat semigroup is the zero map. -/
theorem tensorHeatSemigroup_of_neg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_uniform : uniformTensorChartSobolevBound g r s}
    {t : ℝ} (ht : t < 0) :
    tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t = 0 := by
  unfold tensorHeatSemigroup
  rw [dif_neg (not_le.mpr ht)]

/-- The operator norm of `tensorHeatSemigroup g r s h_uniform t` is at most
`1` for every `t : ℝ`. For `t ≥ 0` this is the spectral-series contraction
bound; for `t < 0` the operator is zero. -/
theorem tensorHeatSemigroup_opNorm_le_one
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_uniform : uniformTensorChartSobolevBound g r s} (t : ℝ) :
    ‖tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t‖ ≤ 1 := by
  unfold tensorHeatSemigroup
  by_cases ht : 0 ≤ t
  · rw [dif_pos ht]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · rw [dif_neg ht]
    rw [norm_zero]
    exact zero_le_one

/-! ## Action on basis vectors -/

/-- The tensor heat semigroup acts diagonally on basis vectors:
`e^{t Δ_∇} (b i) = exp(-λ_i t) • b i`. -/
theorem tensorHeatSemigroup_apply_basis
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_uniform : uniformTensorChartSobolevBound g r s}
    {t : ℝ} (ht : 0 ≤ t)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t
        (tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_uniform i) =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_uniform i := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_uniform
  rw [tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) ht (b i)]
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq :
      ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
        ⟪b j, b i⟫_ℝ = if j = i then 1 else 0 := by
    intro j
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq :
      ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, b i⟫_ℝ • b j =
        if j = i then
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) • b j
        else 0 := by
    intro j
    rw [h_inner_eq]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h_sum_eq :
      (fun j : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, b i⟫_ℝ • b j) =
      (fun j =>
        if j = i then
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) • b j
        else 0) := by
    funext j; exact h_summand_eq j
  rw [h_sum_eq]
  rw [tsum_ite_eq i]

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  TensorEigenIdx (I := I) (M := M) g r s

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  TensorEigenIdx.lambda (I := I) (M := M) i

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_uniform : uniformTensorChartSobolevBound g r s) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  tensorHeatSemigroup (I := I) (M := M) g r s h_uniform t

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_heat_coeff_mem_unit_interval

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSummable_basis_coeff_sq

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorParseval_norm_sq

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSummable_heatTerm

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_apply_of_nonneg

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_of_neg

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_opNorm_le_one

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_apply_basis

end Sanity
