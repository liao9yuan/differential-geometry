import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerJointCont
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Uniform positive lower bound for the chart-frame `(r, s)`-quadratic form

For a closed Riemannian manifold `(M, g)` and a chart base point `α : M`, the
chart-frame `(r, s)`-diagonal quadratic form
`(b, T) ↦ chartTensorInnerPointwise_rs_model g r s α b T T`
attains a strictly positive minimum on the compact product
`tsupport (chartAtlasPOU I M α) × unit sphere(TensorRSModel r s ℝ E)`.

This is a uniform-positivity statement: there is a single `ε > 0` such that
the quadratic form is bounded below by `ε` on the entire compact product.

## Proof strategy

The argument is the standard extreme-value-theorem application on a compact
domain:

1. The first factor `tsupport (chartAtlasPOU I M α)` is compact in `M`, as a
   closed subset of the compact ambient manifold.
2. The second factor `Metric.sphere (0 : TensorRSModel r s ℝ E) 1` is compact
   in any finite-dimensional normed space (proper space ⇒ closed bounded
   compact).
3. The product is compact, the quadratic form is jointly continuous on
   `baseSet × univ ⊇ tsupport × sphere` (by the joint continuity established
   earlier), and the form is strictly positive at every `(b, T)` in the
   compact product (since the chart-`(α, b)`-twist is invertible on `baseSet`
   and the bundle-fibre `(r, s)`-inner product is positive-definite on
   non-zero tensors).
4. The extreme-value theorem produces a minimum, which is strictly positive.

## Main result

* `exists_chartTensorInnerPointwise_rs_model_lower_bound_on_pouTsupport` —
  the uniform positive lower bound.
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

/-! ## Invertibility of the chart-`(α, b)`-twist on the chart base set

The forward twist `chartRSTwist α b r s T` precomposes the input on the
`r`-block with `chartJinv α b` and postcomposes the output on the `s`-block
with `chartJ α b`. The inverse twist swaps the roles: precompose input on
the `r`-block with `chartJ α b`, postcompose output on the `s`-block with
`chartJinv α b`. Round-trip equals the identity on the chart base set via
`chartJ ∘ chartJinv = id` and `chartJinv ∘ chartJ = id`. -/

section TwistInvertible

/-- The inverse chart-`(α, b)`-twist of a mixed model tensor: precompose the
input on the `r`-block with `chartJ α b`, and postcompose the output on
the `s`-block with `chartJinv α b`. Composes with `chartRSTwist` to the
identity on the chart base set. -/
noncomputable def chartRSTwistInv
    (α : M) (b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin s => chartJinv (I := I) (M := M) α b)).comp <|
    T.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin r => chartJ (I := I) (M := M) α b)))

@[simp]
lemma chartRSTwistInv_apply
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (α' : Tensor0SModel r ℝ E) :
    chartRSTwistInv (I := I) (M := M) α b r s T α' =
      (T (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) := by
  rfl

/-- On the chart base set, the inverse twist undoes the forward twist:
`chartRSTwistInv α b r s (chartRSTwist α b r s T) = T`. -/
lemma chartRSTwistInv_chartRSTwist
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    chartRSTwistInv (I := I) (M := M) α b r s
        (chartRSTwist (I := I) (M := M) α b r s T) = T := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwistInv_apply, chartRSTwist_apply]
  -- LHS = ((T (α'.compCLM chartJ).compCLM chartJinv).compCLM chartJ).compCLM chartJinv
  -- We need to simplify the two inner compositions and the two outer compositions
  -- separately, using chartJinv ∘ chartJ = id (on input, fresh variables in E)
  -- and chartJ ∘ chartJinv = id (on output, fresh variables in E).
  -- After the two inner compositions: α'.compCLM chartJ then compCLM chartJinv.
  -- The result is α'.compCLM (chartJinv ∘ chartJ) = α' on baseSet.
  refine ContinuousMultilinearMap.ext ?_
  intro w
  -- Evaluate both sides at the slot-vector `w : Fin s → E`.
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Now LHS is T applied to: (α'.compCLM chartJ).compCLM chartJinv, evaluated at chartJ ∘ w.
  -- Show that the inner composition collapses to α'.
  have hα' :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartJinv (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (v k)
  rw [hα']
  -- Now the goal is `T α' (chartJ ∘ (chartJinv ∘ w)) = T α' w`.
  -- Simplify the composition `chartJ ∘ chartJinv = id` on the outer slot.
  congr 1
  funext k
  exact chartJ_chartJinv (I := I) (M := M) α hb (w k)

/-- On the chart base set, the forward twist undoes the inverse twist:
`chartRSTwist α b r s (chartRSTwistInv α b r s T) = T`. -/
lemma chartRSTwist_chartRSTwistInv
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    chartRSTwist (I := I) (M := M) α b r s
        (chartRSTwistInv (I := I) (M := M) α b r s T) = T := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwist_apply, chartRSTwistInv_apply]
  -- After `chartRSTwist_apply` then `chartRSTwistInv_apply`, the LHS reads
  -- `((T ((α'.compCLM chartJinv).compCLM chartJ)).compCLM chartJinv).compCLM chartJ`.
  -- Inner: `(α'.compCLM chartJinv).compCLM chartJ = α'` via `chartJinv ∘ chartJ = id`.
  have hinner :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJinv_chartJ_self (I := I) (M := M) α hb (v k)
  rw [hinner]
  -- After eliminating the inner composition, the goal is
  --   `((T α').compCLM chartJinv).compCLM chartJ = T α'`.
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact chartJinv_chartJ_self (I := I) (M := M) α hb (w k)

/-- On the chart base set, the forward chart-`(α, b)`-twist is injective. -/
lemma chartRSTwist_injective
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) :
    Function.Injective
      (chartRSTwist (I := I) (M := M) α b r s) := by
  intro T₀ T₁ h
  have h0 := chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T₀
  have h1 := chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T₁
  rw [← h0, ← h1, h]

/-- On the chart base set, the forward chart-`(α, b)`-twist of a non-zero
tensor is non-zero. -/
lemma chartRSTwist_ne_zero
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r s : ℕ) {T : TensorRSModel r s ℝ E} (hT : T ≠ 0) :
    chartRSTwist (I := I) (M := M) α b r s T ≠ 0 := by
  intro hzero
  -- Apply the inverse twist to both sides of `hzero` and use the round-trip
  -- identity to conclude `T = 0`, contradicting `hT`.
  have hround : chartRSTwistInv (I := I) (M := M) α b r s
      (chartRSTwist (I := I) (M := M) α b r s T) = T :=
    chartRSTwistInv_chartRSTwist (I := I) (M := M) α hb r s T
  -- Compute `chartRSTwistInv α b r s 0 = 0`. By linearity of the inverse
  -- twist (it is built from continuous linear operations), `map_zero` gives
  -- the result directly.
  have hzero_inv :
      chartRSTwistInv (I := I) (M := M) α b r s
        (0 : TensorRSModel r s ℝ E) = 0 := by
    classical
    refine ContinuousLinearMap.ext ?_
    intro α'
    rw [chartRSTwistInv_apply]
    -- `(0 α'.compCLM chartJ : Tensor0SModel s ℝ E) = 0`, hence
    -- `(0).compCLM chartJinv = 0`.
    change ((0 : TensorRSModel r s ℝ E)
        (α'.compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) = 0
    rw [show ((0 : TensorRSModel r s ℝ E)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))) =
            (0 : Tensor0SModel s ℝ E) from rfl]
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  -- Substitute `hzero` into `hround` to get `T = 0`.
  rw [hzero, hzero_inv] at hround
  exact hT hround.symm

end TwistInvertible

/-! ## Strict positivity of the diagonal quadratic form on `baseSet × (T ≠ 0)`

For `b ∈ baseSet` and `T ≠ 0`, the bridge identity expresses the chart-frame
diagonal value as a bundle-fibre diagonal value on the twisted tensor, which
is `> 0` by positive-definiteness of `tensorInnerPointwise` on non-zero
tensors. -/

section Positivity

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]

/-- Strict positivity of the chart-frame `(r, s)`-diagonal quadratic form
at a non-zero tensor, on the chart base set. -/
lemma chartTensorInnerPointwise_rs_model_pos_of_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {T : TensorRSModel r s ℝ E} (hT : T ≠ 0) :
    0 < chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T := by
  classical
  -- Rewrite via the bridge to the bundle-fibre diagonal value on the twisted tensor.
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb T T]
  -- The twisted tensor is non-zero.
  have hTwist_ne : chartRSTwist (I := I) (M := M) α b r s T ≠ 0 :=
    chartRSTwist_ne_zero (I := I) (M := M) α hb r s hT
  -- Non-negativity + non-zero diagonal value gives strict positivity.
  set Q : ℝ :=
    tensorInnerPointwise (I := I) (M := M) g r s b
      (chartRSTwist (I := I) (M := M) α b r s T)
      (chartRSTwist (I := I) (M := M) α b r s T)
  have hQ_nn : 0 ≤ Q :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have := (tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g r s b
      (chartRSTwist (I := I) (M := M) α b r s T)).mp hQ0
    exact hTwist_ne this
  exact lt_of_le_of_ne hQ_nn (Ne.symm hQ_ne)

end Positivity

/-! ## Compactness of the product `tsupport × unit sphere`

Compactness of `tsupport (chartAtlasPOU I M α)` in `M` is immediate from
closed support inside compact `M`. Compactness of the unit sphere in the
finite-dimensional normed space `TensorRSModel r s ℝ E` follows from
`isCompact_sphere` (via the `ProperSpace` instance for finite-dimensional
real normed spaces). -/

section Compactness

variable [CompactSpace M]

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is compact in `M`. -/
lemma pouTsupport_isCompact
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is contained in the chart base set. -/
lemma pouTsupport_subset_baseSet
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α hx

end Compactness

/-! ## The headline uniform positive lower bound -/

section LowerBound

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

/-- **Uniform positive lower bound for the chart-frame `(r, s)`-diagonal
quadratic form on `K_M × unit sphere`, for an arbitrary compact subset `K_M`
of the chart base set.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, ranks
`(r, s)`, and a compact set `K_M` contained in the chart-`α` base set, there is
`ε > 0` such that `chartTensorInnerPointwise_rs_model g r s α b T T ≥ ε` for
every `b ∈ K_M` and every unit `(r, s)`-model tensor `T`. -/
theorem exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ b : M, b ∈ K_M →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T := by
  classical
  -- Provide the proper-space instance needed for compactness of the sphere.
  haveI : ProperSpace (TensorRSModel r s ℝ E) :=
    FiniteDimensional.proper_real (TensorRSModel r s ℝ E)
  -- Compact set `S = unit sphere ⊆ TensorRSModel r s ℝ E`.
  set S_T : Set (TensorRSModel r s ℝ E) := Metric.sphere (0 : TensorRSModel r s ℝ E) 1
    with hS_T_def
  have hS_T_compact : IsCompact S_T :=
    isCompact_sphere (0 : TensorRSModel r s ℝ E) 1
  -- Members of the unit sphere have norm 1 (and hence are non-zero).
  have hS_T_norm : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → ‖T‖ = 1 := by
    intro T hT
    rw [hS_T_def, Metric.mem_sphere, dist_zero_right] at hT
    exact hT
  have hS_T_ne_zero : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → T ≠ 0 := by
    intro T hT hT0
    have : ‖T‖ = 1 := hS_T_norm T hT
    rw [hT0, norm_zero] at this
    exact one_ne_zero this.symm
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
  -- Determine whether `K` is empty or non-empty. If empty, any `ε > 0` works.
  by_cases hK_ne : K.Nonempty
  · -- Apply the extreme-value theorem to extract a minimum point.
    obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hK_compact.exists_isMinOn hK_ne hQ_contOn
    -- `Q p₀` is the minimum value; show it is strictly positive.
    have hp₀_M : p₀.1 ∈ K_M := hp₀_mem.1
    have hp₀_S : p₀.2 ∈ S_T := hp₀_mem.2
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hK_M_sub_baseSet hp₀_M
    have hp₀_ne : p₀.2 ≠ 0 := hS_T_ne_zero p₀.2 hp₀_S
    have hp₀_pos : 0 < Q p₀ :=
      chartTensorInnerPointwise_rs_model_pos_of_ne_zero
        (I := I) (M := M) g r s α hp₀_base hp₀_ne
    refine ⟨Q p₀, hp₀_pos, ?_⟩
    intro b hb T hT_norm
    -- Membership in `K` for `(b, T)`.
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    -- Apply the minimality of `p₀` at `(b, T)`.
    have := hp₀_min hp_mem
    -- `this : Q p₀ ≤ Q (b, T)`. Unfold `Q`.
    exact this
  · -- `K` is empty: the conclusion is vacuous. Use any positive `ε`, say `1`.
    refine ⟨1, one_pos, ?_⟩
    intro b hb T hT_norm
    -- Derive contradiction from `K` being empty and `(b, T) ∈ K`.
    have hT_mem : T ∈ S_T := by
      rw [hS_T_def, Metric.mem_sphere, dist_zero_right]
      exact hT_norm
    have hp_mem : (b, T) ∈ K := ⟨hb, hT_mem⟩
    exact absurd ⟨(b, T), hp_mem⟩ hK_ne

/-- **Uniform positive lower bound for the chart-frame `(r, s)`-diagonal
quadratic form on `tsupport(POU_α) × unit sphere`.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and ranks
`(r, s)`, there is `ε > 0` such that
`chartTensorInnerPointwise_rs_model g r s α b T T ≥ ε`
for every `b` in the closed support of the chart-atlas partition-of-unity
weight at `α` and every unit `(r, s)`-model tensor `T`.

This is the specialisation of
`exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact` to the
compact closed support of the chart-atlas partition-of-unity weight. -/
theorem exists_chartTensorInnerPointwise_rs_model_lower_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T :=
  exists_chartTensorInnerPointwise_rs_model_lower_bound_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end LowerBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
