import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensorInnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensorInnerJointCont
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensorInnerLowerBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Uniform upper bound for the chart-frame `(r, s)`-quadratic form

For a closed Riemannian manifold `(M, g)` and a chart base point `α : M`, the
chart-frame `(r, s)`-diagonal quadratic form
`(b, T) ↦ chartTensorInnerPointwise_rs_model g r s α b T T`
attains a finite maximum on the compact product
`tsupport (chartAtlasPOU I M α) × unit sphere(TensorRSModel r s ℝ E)`.

This is a uniform-boundedness statement: there is a single non-negative
constant `C` such that the quadratic form is bounded above by `C * ‖T‖^2`
for every `b` in the closed support of the chart-atlas partition-of-unity
weight at `α` and every model tensor `T`.

## Proof strategy

The argument mirrors the lower-bound companion:

1. The first factor `tsupport (chartAtlasPOU I M α)` is compact in `M`, as a
   closed subset of the compact ambient manifold.
2. The second factor `Metric.sphere (0 : TensorRSModel r s ℝ E) 1` is compact
   in any finite-dimensional normed space (proper space ⇒ closed bounded
   compact).
3. The product is compact, the quadratic form is jointly continuous on
   `baseSet × univ ⊇ tsupport × sphere` (by the joint continuity established
   earlier).
4. The extreme-value theorem produces a maximum on the unit sphere.
5. Homogeneity of the diagonal quadratic form in `T` (`Q(b, c • T, c • T) =
   c^2 Q(b, T, T)`) rescales the unit-sphere bound to the inequality
   `Q(b, T, T) ≤ C * ‖T‖^2` for every `T`.

## Main result

* `exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport` —
  the uniform upper bound in homogeneous-degree-two form.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Metric
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Headline uniform upper bound on the unit sphere

We first extract a finite maximum on the compact product
`tsupport(POU_α) × unit sphere`. This intermediate form is then rescaled
by homogeneity to the public headline. -/

section UpperBoundUnitSphere

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- **Uniform upper bound for the chart-frame `(r, s)`-diagonal quadratic
form on `tsupport(POU_α) × unit sphere`.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and
ranks `(r, s)`, there is a non-negative constant `M_ub` such that
`chartTensorInnerPointwise_rs_model g r s α b T T ≤ M_ub`
for every `b` in the closed support of the chart-atlas partition-of-unity
weight at `α` and every unit `(r, s)`-model tensor `T`. -/
private lemma exists_chartTensorInnerPointwise_rs_model_unit_sphere_upper_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ M_ub : ℝ, 0 ≤ M_ub ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T ≤ M_ub := by
  classical
  -- Provide the proper-space instance needed for compactness of the sphere.
  haveI : ProperSpace (TensorRSModel r s ℝ E) :=
    FiniteDimensional.proper_real (TensorRSModel r s ℝ E)
  -- Compact set `tsupport(POU_α) ⊆ M`.
  set K_M : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_M_def
  have hK_M_compact : IsCompact K_M :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  -- Compact set `S = unit sphere ⊆ TensorRSModel r s ℝ E`.
  set S_T : Set (TensorRSModel r s ℝ E) := Metric.sphere (0 : TensorRSModel r s ℝ E) 1
    with hS_T_def
  have hS_T_compact : IsCompact S_T :=
    isCompact_sphere (0 : TensorRSModel r s ℝ E) 1
  -- The compact product `K = K_M ×ˢ S_T`.
  set K : Set (M × TensorRSModel r s ℝ E) := K_M ×ˢ S_T with hK_def
  have hK_compact : IsCompact K := hK_M_compact.prod hS_T_compact
  -- Joint continuity of the quadratic form on `baseSet × univ`; restrict to `K`.
  set Q : M × TensorRSModel r s ℝ E → ℝ := fun bT =>
    chartTensorInnerPointwise_rs_model (I := I) (M := M)
      g r s α bT.1 bT.2 bT.2 with hQ_def
  have hQ_contOn_full :
      ContinuousOn Q
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    chartTensorInnerPointwise_rs_model_quadratic_continuousOn
      (I := I) (M := M) g r s α
  have hK_sub_full :
      K ⊆ ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
    intro p hp
    refine ⟨hK_M_sub_baseSet hp.1, ?_⟩
    exact Set.mem_univ _
  have hQ_contOn : ContinuousOn Q K :=
    hQ_contOn_full.mono hK_sub_full
  -- Determine whether `K` is empty or non-empty. If empty, any `C ≥ 0` works.
  by_cases hK_ne : K.Nonempty
  · -- Apply the extreme-value theorem to extract a maximum point.
    obtain ⟨p₀, hp₀_mem, hp₀_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne hQ_contOn
    -- `Q p₀` is the maximum value; show it is non-negative (since the form
    -- is non-negative at every base-set point).
    have hp₀_M : p₀.1 ∈ K_M := hp₀_mem.1
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hK_M_sub_baseSet hp₀_M
    have hp₀_nn : 0 ≤ Q p₀ :=
      chartTensorInnerPointwise_rs_model_nonneg
        (I := I) (M := M) g r s α hp₀_base p₀.2
    refine ⟨Q p₀, hp₀_nn, ?_⟩
    intro b hb T hT_norm
    -- Membership in `K` for `(b, T)`.
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    -- Apply the maximality of `p₀` at `(b, T)`.
    have := hp₀_max hp_mem
    -- `this : Q (b, T) ≤ Q p₀`. Unfold `Q`.
    exact this
  · -- `K` is empty: the conclusion is vacuous. Use any non-negative `C`.
    refine ⟨0, le_refl 0, ?_⟩
    intro b hb T hT_norm
    -- Derive contradiction from `K` being empty and `(b, T) ∈ K`.
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    exact absurd ⟨(b, T), hp_mem⟩ hK_ne

end UpperBoundUnitSphere

/-! ## Headline uniform upper bound in homogeneous-degree-two form

Homogeneity of the diagonal quadratic form rescales the unit-sphere
maximum to a universal `Q(b, T, T) ≤ C * ‖T‖^2` bound for every
`T : TensorRSModel r s ℝ E`. The zero tensor is handled separately
(both sides vanish); the non-zero case rescales by `‖T‖`. -/

section UpperBound

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- Rescaling of the unit-sphere upper bound to the homogeneous-degree-two
inequality on every model `(r, s)`-tensor `T`. On `tsupport(POU_α)`,
`chartTensorInnerPointwise_rs_model g r s α b T T ≤ M_ub * ‖T‖^2`
for every `T`, with the same `M_ub` produced by the unit-sphere maximum. -/
private lemma chartTensorInnerPointwise_rs_model_le_mul_sq_norm_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {M_ub : ℝ}
    (h_ub : ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
        chartTensorInnerPointwise_rs_model (I := I) (M := M)
          g r s α b T T ≤ M_ub) :
    ∀ b : M, b ∈ tsupport (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ∀ T : TensorRSModel r s ℝ E,
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T ≤
          M_ub * ‖T‖ ^ 2 := by
  classical
  intro b hb T
  by_cases hT0 : T = 0
  · -- Zero tensor: both sides vanish.
    subst hT0
    -- LHS = 0 via the same `zero_smul` trick used in the lower-bound rescaler.
    have h_left : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E) = 0 := by
      have h_zero_smul :
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
              (0 : TensorRSModel r s ℝ E) =
          (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
        chartTensorInnerPointwise_rs_model_smul_left
          (I := I) (M := M) g r s α b 0 (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E)
      have h_eq : (0 : TensorRSModel r s ℝ E) =
          ((0 : ℝ) • (0 : TensorRSModel r s ℝ E)) := by rw [zero_smul]
      calc chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b
              (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E)
          = chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                ((0 : ℝ) • (0 : TensorRSModel r s ℝ E))
                (0 : TensorRSModel r s ℝ E) := by rw [← h_eq]
        _ = (0 : ℝ) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b
                (0 : TensorRSModel r s ℝ E) (0 : TensorRSModel r s ℝ E) :=
              h_zero_smul
        _ = 0 := by ring
    have h_right : M_ub * ‖(0 : TensorRSModel r s ℝ E)‖ ^ 2 = 0 := by simp
    rw [h_left, h_right]
  · -- Non-zero tensor: rescale by `‖T‖` and apply the unit-sphere bound.
    have hT_ne : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT0
    have hT_pos : 0 < ‖T‖ := (norm_pos_iff).mpr hT0
    -- The unit-norm rescaling `T' := ‖T‖⁻¹ • T` has norm one.
    letI : NormSMulClass ℝ (TensorRSModel r s ℝ E) :=
      NormedSpace.toNormSMulClass
    set T' : TensorRSModel r s ℝ E := ‖T‖⁻¹ • T with hT'_def
    have hT'_norm : ‖T'‖ = 1 := by
      rw [hT'_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hT_pos]
      field_simp
    -- The upper bound at `T'`.
    have h_T' : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T' T' ≤ M_ub :=
      h_ub b hb T' hT'_norm
    -- Bilinearity: `Q(b, T', T') = (‖T‖⁻¹ * ‖T‖⁻¹) * Q(b, T, T)`.
    have h_bilin :
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T' T' =
          (‖T‖⁻¹ * ‖T‖⁻¹) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b T T := by
      rw [hT'_def]
      rw [chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T (‖T‖⁻¹ • T)]
      rw [chartTensorInnerPointwise_rs_model_smul_right
        (I := I) (M := M) g r s α b ‖T‖⁻¹ T T]
      ring
    rw [h_bilin] at h_T'
    -- From `(‖T‖⁻¹ * ‖T‖⁻¹) * Q ≤ M_ub`, multiply both sides by `‖T‖² ≥ 0`.
    have h_sq_nn : 0 ≤ ‖T‖ ^ 2 := by positivity
    have h_mul : ((‖T‖⁻¹ * ‖T‖⁻¹) *
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 ≤
        M_ub * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_T' h_sq_nn
    -- Simplify the LHS of `h_mul` to the bare quadratic-form value.
    have h_lhs :
        ((‖T‖⁻¹ * ‖T‖⁻¹) *
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 =
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T := by
      have h_sq_eq : ‖T‖ ^ 2 = ‖T‖ * ‖T‖ := by ring
      rw [h_sq_eq]
      field_simp
    rw [h_lhs] at h_mul
    exact h_mul

/-- **Uniform upper bound for the chart-frame `(r, s)`-diagonal quadratic
form on `tsupport(POU_α)` (homogeneous-degree-two form).**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and
ranks `(r, s)`, there is a non-negative constant `C` such that
`chartTensorInnerPointwise_rs_model g r s α b T T ≤ C * ‖T‖^2`
for every `b` in the closed support of the chart-atlas partition-of-unity
weight at `α` and every model `(r, s)`-tensor `T`. -/
theorem exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T ≤ C * ‖T‖ ^ 2 := by
  classical
  -- Extract the uniform upper bound on the unit sphere.
  obtain ⟨M_ub, hM_ub_nn, h_ub⟩ :=
    exists_chartTensorInnerPointwise_rs_model_unit_sphere_upper_bound
      (I := I) (M := M) g r s α
  refine ⟨M_ub, hM_ub_nn, ?_⟩
  -- Apply the rescaling lemma.
  exact chartTensorInnerPointwise_rs_model_le_mul_sq_norm_on_pouTsupport
    (I := I) (M := M) g r s α h_ub

end UpperBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
