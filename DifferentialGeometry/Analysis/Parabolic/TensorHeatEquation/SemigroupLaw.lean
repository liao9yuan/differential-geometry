import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup

/-!
# Tensor heat semigroup: self-adjointness, semigroup law, strong continuity at `0+`

This file establishes the three foundational analytic properties of the
tensor heat semigroup `e^{t Δ_∇}` on `TensorL2 r s g`:

* `tensorHeatSemigroup_isSelfAdjoint` — for every `t : ℝ`, the operator
  is self-adjoint. (For `t ≥ 0`, this follows from the symmetric form of
  the spectral series; for `t < 0`, the operator is the zero map.)
* `tensorHeatSemigroup_zero` — at `t = 0`, the semigroup is the identity.
* `tensorHeatSemigroup_add` — the semigroup law
  `e^{(s+t) Δ_∇} = e^{s Δ_∇} ∘ e^{t Δ_∇}` for `s, t ≥ 0`.
* `tensorHeatSemigroup_continuous_at_zero` — strong continuity at the
  right boundary `t = 0+`.

All proofs mirror the scalar templates from
`Analysis/HeatEquation/Semigroup.lean`, using the tensor eigenbasis
`tensorResolventHilbertEigenbasisSigma` in place of the scalar
`resolventHilbertEigenbasisSigma`, and the tensor-side helper lemmas
(`tensorSummable_heatTerm`, `tensorSummable_basis_coeff_sq`,
`tensorOrthonormal_norm_sq_eq_tsum_sq`,
`tensor_heat_coeff_sq_le_one`).
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

/-! ## Self-adjointness -/

/-- The tensor heat semigroup is self-adjoint at every `t : ℝ`. For
`t ≥ 0`, the spectral series is symmetric in its two arguments; for
`t < 0`, the operator is the zero map. -/
theorem tensorHeatSemigroup_isSelfAdjoint
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) (t : ℝ) :
    IsSelfAdjoint
      (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t :
        TensorL2 r s g →L[ℝ] TensorL2 r s g) := by
  by_cases ht : 0 ≤ t
  · -- Nonneg-time case: mirror the scalar self-adjointness proof.
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    set b := tensorResolventHilbertEigenbasisSigma
      (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
    change ⟪(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t) u, v⟫_ℝ =
        ⟪u, (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t) v⟫_ℝ
    rw [tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas ht u,
        tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas ht v]
    -- Inner-product CLMs.
    let φv : TensorL2 r s g →L[ℝ] ℝ := (innerSL ℝ).flip v
    let φu : TensorL2 r s g →L[ℝ] ℝ := innerSL ℝ u
    -- LHS: pull the inner product inside the tsum via continuity of `φv`.
    have h_lhs : ⟪∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ =
        ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      have h_summable :=
        tensorSummable_heatTerm (I := I) (M := M) h_atlas ht u
      have h_hsum := h_summable.hasSum
      have h_inner_hsum := h_hsum.mapL φv
      have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          φv (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, u⟫_ℝ • b i) =
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
        intro i
        change ⟪Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ = _
        rw [real_inner_smul_left, real_inner_smul_left]
        ring
      have h_inner_hsum' : HasSum (fun i =>
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
          (φv (∑' i, Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, u⟫_ℝ • b i)) := by
        convert h_inner_hsum using 1
        funext i; exact (h_summand_eq i).symm
      have h_apply : φv (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, u⟫_ℝ • b i) =
          ⟪∑' i, Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, u⟫_ℝ • b i, v⟫_ℝ := rfl
      rw [h_apply] at h_inner_hsum'
      exact h_inner_hsum'.tsum_eq.symm
    -- RHS: same trick with `φu`.
    have h_rhs : ⟪u, ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ =
        ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      have h_summable :=
        tensorSummable_heatTerm (I := I) (M := M) h_atlas ht v
      have h_hsum := h_summable.hasSum
      have h_inner_hsum := h_hsum.mapL φu
      have h_summand_eq : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          φu (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, v⟫_ℝ • b i) =
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
        intro i
        change ⟪u, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ = _
        rw [real_inner_smul_right, real_inner_smul_right,
            show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _]
        ring
      have h_inner_hsum' : HasSum (fun i =>
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
          (φu (∑' i, Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, v⟫_ℝ • b i)) := by
        convert h_inner_hsum using 1
        funext i; exact (h_summand_eq i).symm
      have h_apply : φu (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, v⟫_ℝ • b i) =
          ⟪u, ∑' i, Real.exp
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, v⟫_ℝ • b i⟫_ℝ := rfl
      rw [h_apply] at h_inner_hsum'
      exact h_inner_hsum'.tsum_eq.symm
    rw [h_lhs, h_rhs]
  · -- Negative-time case: the operator is `0`, trivially self-adjoint.
    have h_neg : t < 0 := lt_of_not_ge ht
    have h_zero :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t = 0 :=
      tensorHeatSemigroup_of_neg (I := I) (M := M) h_atlas (ht := h_neg)
    rw [h_zero]
    exact IsSelfAdjoint.zero _

/-! ## Zero-time identity -/

/-- At `t = 0`, the tensor heat semigroup is the identity. -/
theorem tensorHeatSemigroup_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    tensorHeatSemigroup (I := I) (M := M) g r s h_atlas 0 =
      ContinuousLinearMap.id ℝ (TensorL2 r s g) := by
  apply ContinuousLinearMap.ext
  intro T
  rw [tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas (le_refl 0) T]
  rw [ContinuousLinearMap.id_apply]
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h_coeff_one : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * 0) = 1 := by
    intro i
    have h_arg : -(TensorEigenIdx.lambda (I := I) (M := M) i) * 0 = 0 := by ring
    rw [h_arg, Real.exp_zero]
  have h_summand_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * 0) •
          ⟪b i, T⟫_ℝ • b i) =
      (fun i => ⟪b i, T⟫_ℝ • b i) := by
    funext i; rw [h_coeff_one i, one_smul]
  rw [h_summand_eq]
  have h_hsum : HasSum (fun i => b.repr T i • b i) T := b.hasSum_repr T
  have h_eq : (fun i => b.repr T i • b i) = (fun i => ⟪b i, T⟫_ℝ • b i) := by
    funext i; rw [b.repr_apply_apply]
  rw [h_eq] at h_hsum
  exact h_hsum.tsum_eq

/-! ## Semigroup law -/

/-- Semigroup law: `e^{(t₁+t₂) Δ_∇} = e^{t₁ Δ_∇} ∘ e^{t₂ Δ_∇}` for
`t₁, t₂ ≥ 0`. -/
theorem tensorHeatSemigroup_add
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t₁ + t₂) =
      (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₁).comp
        (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₂) := by
  apply ContinuousLinearMap.ext
  intro T
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  have h12_nn : 0 ≤ t₁ + t₂ := add_nonneg ht₁ ht₂
  rw [tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas h12_nn,
      ContinuousLinearMap.comp_apply,
      tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas ht₂ T]
  have h_summable_t₂ :=
    tensorSummable_heatTerm (I := I) (M := M) h_atlas ht₂ T
  -- Pull `tensorHeatSemigroup _ t₁` inside the tsum (continuous linear map).
  have h_pull :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₁
          (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
              ⟪b i, T⟫_ℝ • b i) =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₁
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
            ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum := h_summable_t₂.hasSum
    exact (h_hsum.mapL
      (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₁)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas t₁).map_smul,
      (tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas t₁).map_smul]
  -- The heat semigroup acts diagonally on basis vectors.
  have h_basis_apply :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₁ (b i) =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁) • b i :=
    tensorHeatSemigroup_apply_basis (I := I) (M := M) h_atlas ht₁ i
  rw [h_basis_apply]
  -- Goal: combine the two exponential factors via `Real.exp_add`.
  have h_exp_add :
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁) *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) := by
    rw [show -(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁ +
          -(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂ from by ring,
        Real.exp_add]
  -- Convert both sides to single-coefficient form.
  rw [show Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) •
      ⟪b i, T⟫_ℝ • b i =
      (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t₁ + t₂)) *
        ⟪b i, T⟫_ℝ) • b i from by rw [mul_smul]]
  rw [show Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) •
      ⟪b i, T⟫_ℝ •
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁) • b i =
      (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₂) *
        (⟪b i, T⟫_ℝ *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t₁))) •
            b i from by
    rw [mul_smul, mul_smul]]
  congr 1
  rw [h_exp_add]
  ring

/-! ## Strong continuity at `t = 0+` -/

/-- Strong continuity at `t = 0+`: as `t → 0+`,
`tensorHeatSemigroup g r s h_atlas t T → T`. -/
theorem tensorHeatSemigroup_continuous_at_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T : TensorL2 r s g) :
    Filter.Tendsto
      (fun t : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 T) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Square-summability of the basis Fourier coefficients (drop the norm bars).
  have h_summable_sq :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (⟪b i, T⟫_ℝ) ^ 2) := by
    have h_norm_sq :=
      tensorSummable_basis_coeff_sq (I := I) (M := M) h_atlas T
    have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪b i, T⟫_ℝ‖ ^ 2) =
        (fun i => (⟪b i, T⟫_ℝ) ^ 2) := by
      funext i
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq] at h_norm_sq
    exact h_norm_sq
  -- Find a finite set `T_fin` such that the tail of `∑ ⟪b i, T⟫²` is `< ε²/16`.
  have hε16_pos : (0 : ℝ) < ε ^ 2 / 16 := by positivity
  obtain ⟨T_fin, hT_fin⟩ : ∃ T_fin : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
        (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2 <
        ε ^ 2 / 16 := by
    have h_hsum := h_summable_sq.hasSum
    rw [HasSum, Metric.tendsto_nhds] at h_hsum
    have h_evt := h_hsum (ε ^ 2 / 16) hε16_pos
    obtain ⟨T_fin, hT_T⟩ := h_evt.exists
    refine ⟨T_fin, ?_⟩
    have h_split : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (⟪b i, T⟫_ℝ) ^ 2 =
        (∑ i ∈ T_fin, (⟪b i, T⟫_ℝ) ^ 2) +
        ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
          (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2 :=
      (h_summable_sq.sum_add_tsum_subtype_compl T_fin).symm
    rw [dist_eq_norm, h_split] at hT_T
    have h_simp : ∑ i ∈ T_fin, (⟪b i, T⟫_ℝ) ^ 2 -
        ((∑ i ∈ T_fin, (⟪b i, T⟫_ℝ) ^ 2) +
          ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
            (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2) =
        -(∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
            (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2) := by
      ring
    rw [h_simp, norm_neg, Real.norm_eq_abs] at hT_T
    have h_tail_nn : 0 ≤
        ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
          (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2 := by
      apply tsum_nonneg
      intro i; exact sq_nonneg _
    rwa [abs_of_nonneg h_tail_nn] at hT_T
  -- Head sum: as `t → 0`, each summand → 0; the finite sum follows.
  have h_head_tendsto : Tendsto (fun t : ℝ =>
      ∑ i ∈ T_fin,
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, T⟫_ℝ) ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h_each : ∀ i ∈ T_fin, Tendsto (fun t : ℝ =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, T⟫_ℝ) ^ 2) (𝓝 0) (𝓝 0) := by
      intro i _
      have h_arg : Tendsto (fun t : ℝ =>
          -(TensorEigenIdx.lambda (I := I) (M := M) i) * t)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h_id : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
        have := h_id.const_mul (-(TensorEigenIdx.lambda (I := I) (M := M) i))
        simpa using this
      have h_exp_to_one : Tendsto (fun t : ℝ =>
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t))
          (𝓝 (0 : ℝ)) (𝓝 1) := by
        have := h_arg.rexp
        simpa [Real.exp_zero] using this
      have h_diff_to_zero : Tendsto (fun t : ℝ =>
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_exp_to_one.sub_const 1
        simpa using this
      have h_sq_to_zero : Tendsto (fun t : ℝ =>
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_diff_to_zero.pow 2
        simpa using this
      have := h_sq_to_zero.mul_const ((⟪b i, T⟫_ℝ) ^ 2)
      simpa using this
    have h_total : Tendsto (fun t : ℝ =>
        ∑ i ∈ T_fin,
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
            (⟪b i, T⟫_ℝ) ^ 2) (𝓝 0) (𝓝 (∑ i ∈ T_fin, (0 : ℝ))) :=
      tendsto_finset_sum T_fin h_each
    simpa using h_total
  rw [Metric.tendsto_nhds] at h_head_tendsto
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp
    (h_head_tendsto (ε ^ 2 / 4) (by positivity))
  -- Restrict to `t ∈ [0, δ)`.
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{t : ℝ | 0 ≤ t ∧ t < δ}, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio δ, Iio_mem_nhds hδ_pos, ?_⟩
    intro x hx
    refine ⟨hx.2, ?_⟩
    exact hx.1
  intro t ht_in
  obtain ⟨ht_nn, ht_lt⟩ := ht_in
  rw [dist_eq_norm]
  suffices h_sq : ‖tensorHeatSemigroup
      (I := I) (M := M) g r s h_atlas t T - T‖ ^ 2 < ε ^ 2 by
    exact (abs_lt_of_sq_lt_sq' h_sq hε.le).2
  rw [tensorHeatSemigroup_apply_of_nonneg (I := I) (M := M) h_atlas ht_nn T]
  have h_summable_heat :=
    tensorSummable_heatTerm (I := I) (M := M) h_atlas ht_nn T
  -- HasSum for the heat-side and for the basis-side.
  have h_hsum_heat : HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, T⟫_ℝ • b i)
      (∑' i, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, T⟫_ℝ • b i) := h_summable_heat.hasSum
  have h_hsum_basis : HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ⟪b i, T⟫_ℝ • b i) T := by
    have h_repr : HasSum (fun i => b.repr T i • b i) T := b.hasSum_repr T
    have h_eq : (fun i => b.repr T i • b i) =
        (fun i => ⟪b i, T⟫_ℝ • b i) := by
      funext i; rw [b.repr_apply_apply]
    rw [h_eq] at h_repr
    exact h_repr
  -- Subtract: the difference is the series with coefficient `(exp(...) - 1)`.
  have h_hsum_diff : HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, T⟫_ℝ • b i - ⟪b i, T⟫_ℝ • b i)
      ((∑' i, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, T⟫_ℝ • b i) - T) :=
    h_hsum_heat.sub h_hsum_basis
  have h_sum_diff :
      (∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T⟫_ℝ • b i) - T =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
          ⟪b i, T⟫_ℝ • b i := by
    have h_summand_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, T⟫_ℝ • b i - ⟪b i, T⟫_ℝ • b i) =
        (fun i =>
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
            ⟪b i, T⟫_ℝ • b i) := by
      funext i; rw [sub_smul, one_smul]
    rw [h_summand_eq] at h_hsum_diff
    exact h_hsum_diff.tsum_eq.symm
  rw [h_sum_diff]
  -- Convert each term to single-coefficient form `((exp(...) - 1) * ⟪b i, T⟫) • b i`.
  have h_sum_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
          ⟪b i, T⟫_ℝ • b i) =
      (fun i =>
        ((Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
          ⟪b i, T⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_sum_eq]
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ := fun i =>
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
      ⟪b i, T⟫_ℝ
  -- Pointwise bound `(f i)² ≤ 4 ⟪b i, T⟫²`.
  have h_f_sq_le : ∀ i, (f i) ^ 2 ≤ 4 * (⟪b i, T⟫_ℝ) ^ 2 := by
    intro i
    have h_pos : 0 <
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    have h_le :
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      nlinarith
    have h_diff_sq :
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2
            ≤ 4 := by
      nlinarith [h_pos, h_le, sq_nonneg
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1)]
    have h_inner_sq_nn : 0 ≤ (⟪b i, T⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ 4 * (⟪b i, T⟫_ℝ) ^ 2
    have h_factor : (f i) ^ 2 =
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, T⟫_ℝ) ^ 2 := by
      change ((Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
        ⟪b i, T⟫_ℝ) ^ 2 = _
      ring
    rw [h_factor]
    nlinarith [h_diff_sq, h_inner_sq_nn]
  have h_summable_f_sq :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (h_summable_sq.mul_left 4)
    · intro i; positivity
    · intro i; exact h_f_sq_le i
  have h_norm_sq_eq :=
    tensorOrthonormal_norm_sq_eq_tsum_sq (I := I) (M := M) h_atlas f
      h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 < ε ^ 2
  rw [h_norm_sq_eq]
  -- Split the tsum into head + tail.
  have h_split : ∑' i : TensorEigenIdx (I := I) (M := M) g r s, (f i) ^ 2 =
      (∑ i ∈ T_fin, (f i) ^ 2) +
      ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
        (f (i : TensorEigenIdx (I := I) (M := M) g r s)) ^ 2 :=
    (h_summable_f_sq.sum_add_tsum_subtype_compl T_fin).symm
  rw [h_split]
  -- Head bound: `< ε²/4`.
  have h_head_bound : ∑ i ∈ T_fin, (f i) ^ 2 < ε ^ 2 / 4 := by
    have h_in_ball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht_nn]
      exact ht_lt
    have h_dist := hδ t h_in_ball
    rw [dist_zero_right, Real.norm_eq_abs] at h_dist
    have h_head_eq_f : ∀ i,
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, T⟫_ℝ) ^ 2 = (f i) ^ 2 := by
      intro i
      change _ =
        ((Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
          ⟪b i, T⟫_ℝ) ^ 2
      ring
    have h_sum_eq' : ∑ i ∈ T_fin,
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, T⟫_ℝ) ^ 2 = ∑ i ∈ T_fin, (f i) ^ 2 := by
      apply Finset.sum_congr rfl
      intros i _; exact h_head_eq_f i
    rw [h_sum_eq'] at h_dist
    have h_nn : 0 ≤ ∑ i ∈ T_fin, (f i) ^ 2 := by
      apply Finset.sum_nonneg; intros; exact sq_nonneg _
    rwa [abs_of_nonneg h_nn] at h_dist
  -- Tail bound: `≤ 4 * tail < 4 * ε²/16 = ε²/4`.
  have h_tail_bound :
      ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
        (f (i : TensorEigenIdx (I := I) (M := M) g r s)) ^ 2 <
        ε ^ 2 / 4 := by
    have h_tail_le :
        ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
          (f (i : TensorEigenIdx (I := I) (M := M) g r s)) ^ 2 ≤
        4 * ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
          (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2 := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => h_f_sq_le i) ?_ ?_
      · exact h_summable_f_sq.subtype _
      · exact (h_summable_sq.subtype _).mul_left 4
    have h_lt : 4 *
        ∑' i : { i : TensorEigenIdx (I := I) (M := M) g r s // i ∉ T_fin },
          (⟪b (i : TensorEigenIdx (I := I) (M := M) g r s), T⟫_ℝ) ^ 2 <
        4 * (ε ^ 2 / 16) := by
      apply mul_lt_mul_of_pos_left hT_fin (by norm_num : (0 : ℝ) < 4)
    have h_eq : 4 * (ε ^ 2 / 16) = ε ^ 2 / 4 := by ring
    linarith [h_tail_le, h_lt, h_eq]
  linarith [h_head_bound, h_tail_bound]

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_isSelfAdjoint

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_zero

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_add

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_continuous_at_zero

end Sanity
