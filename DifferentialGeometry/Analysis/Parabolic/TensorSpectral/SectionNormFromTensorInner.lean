import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovTrivProjNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound

/-!
# Uniform bound: canonical section-fibre norm squared by pointwise tensor inner product

For a closed Riemannian manifold `(M, g)` and a chart base point `α`, the
canonical bundle-fibre norm `‖S.toSection b‖` of a smooth compactly-supported
`(r, s)`-tensor section `S` coincides (definitionally) with the model-space
norm `‖S.toFun b‖` of its model image, since the `TensorRSSpace` normed-group
instance is induced from the model norm.

This file ships the headline uniform bound on the closed support of the
chart-atlas partition-of-unity weight at `α`:

```
‖S.toSection b‖^2 ≤ K_S * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)
```

where `K_S ≥ 0` is independent of `S` and depends only on `(g, r, s, α)` (and
on the chart-selection locality hypothesis `HasLocallyConstantChartAt H M`).

## Strategy

The constant `K_S` is assembled from two existing per-`α` bounds:

1. The chart-trivialisation-inverse norm bound on the closed support
   (`chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport`):
   `‖chartRSTwistInv α b r s X‖^2 ≤ K * tensorInnerPointwise g r s b X X`
   for every model tensor `X`. The constant `K` is built from the
   Rayleigh-quotient lower bound on the inverse chart-Gram matrix on the
   compact `tsupport`.
2. The uniform chart-twist operator-norm bound on the closed support
   (`chartRSTwist_pointwise_opNorm_isBounded_on_compact`):
   `‖chartRSTwist α b r s Y‖ ≤ M * ‖Y‖` for every model tensor `Y` and every
   `b` in the compact `tsupport` (here `tsupport(ρ_α) ⊆ (chartAt H α).source`).
   The constant `M` is built from the chart-Jacobian uniform op-norm bound
   under the locality hypothesis.

Setting `Y := chartRSTwistInv α b r s (S.toFun b)` and using the round-trip
identity `chartRSTwist α b r s Y = S.toFun b` (valid on the chart base set),
the chart-twist bound yields
`‖S.toFun b‖ ≤ M * ‖chartRSTwistInv α b r s (S.toFun b)‖`,
hence `‖S.toFun b‖^2 ≤ M^2 * ‖chartRSTwistInv α b r s (S.toFun b)‖^2`.
Chaining with the inverse-twist norm bound gives
`‖S.toFun b‖^2 ≤ (M^2 * K) * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.

Since `‖S.toSection b‖ = ‖S.toFun b‖` definitionally (the normed-group
instance on `TensorRSSpace` is induced from the model norm), the headline
follows with `K_S := M^2 * K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Bundle-fibre norm identification

The `TensorRSSpace r s I b` normed-group instance is induced from the model
norm along `tensorRSSpace_continuousLinearEquiv`; hence `‖S.toSection b‖`
coincides definitionally with `‖TensorRSSpace.toModel (S.toSection b)‖ =
‖S.toFun b‖`. -/

private lemma section_norm_eq_toFun_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (b : M) :
    ‖S.toSection b‖ = ‖S.toFun b‖ := rfl

/-! ## The POU-`tsupport` lies in the chart source

We restate this auxiliary inclusion locally for use with the chart-twist
uniform op-norm bound, whose hypothesis is phrased on a compact subset of
`(chartAt H α).source`. -/

private lemma pouTsupport_subset_chartAt_source (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source := by
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hb_base
  exact hb_base

/-! ## Headline: section-fibre norm squared bounded by the tensor inner product

The headline result discharges the `K_S` parameter of downstream
`tensorInnerPointwise`-quadratic bounds: there is a uniform `K_S ≥ 0` such
that for every smooth compactly-supported `(r, s)`-tensor section `S` and
every `b` in the closed support of the chart-`α` partition-of-unity weight,
`‖S.toSection b‖^2 ≤ K_S * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`. -/

/-- **Section-fibre norm comparison by the pointwise tensor inner product.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α`, and ranks
`(r, s)`, under the locality hypothesis `HasLocallyConstantChartAt H M` on
the chart-selection function, there is a non-negative constant `K_S` such
that for every smooth compactly-supported `(r, s)`-tensor section `S` and
every base point `b` in the closed support of the chart-atlas
partition-of-unity weight at `α`,
`‖S.toSection b‖² ≤ K_S · tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.

The constant `K_S` depends only on `(g, r, s, α)` and on the locality
hypothesis; it is independent of `S`. -/
theorem norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K_S : ℝ, 0 ≤ K_S ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  -- Compact closed-support set `K := tsupport(ρ_α) ⊆ (chartAt H α).source`.
  set Kα : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_source : Kα ⊆ (chartAt H α).source :=
    pouTsupport_subset_chartAt_source (I := I) (M := M) α
  -- Step 1: chart-trivialisation-inverse norm bound on `Kα`.
  obtain ⟨K, hK_nn, hK_le⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α
  -- Step 2: uniform chart-twist op-norm bound on `Kα` (uses locality).
  obtain ⟨M_tw, hM_tw_pos, hM_tw_le⟩ :=
    chartRSTwist_pointwise_opNorm_isBounded_on_compact
      (I := I) (M := M) (E := E) h_atlas α hKα_compact hKα_sub_source r s
  -- Assemble `K_S := M_tw^2 * K`.
  refine ⟨M_tw ^ 2 * K, by positivity, ?_⟩
  intro S b hb
  -- `b ∈ baseSet` for the round-trip identity.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  -- Abbreviate `Y := chartRSTwistInv α b r s (S.toFun b)`.
  set Y : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s (S.toFun b) with hY_def
  -- Round-trip: `chartRSTwist α b r s Y = S.toFun b` on `baseSet`.
  have h_round : chartRSTwist (I := I) (M := M) α b r s Y = S.toFun b := by
    rw [hY_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s (S.toFun b)
  -- Chart-twist op-norm at `Y`: `‖chartRSTwist α b r s Y‖ ≤ M_tw * ‖Y‖`.
  have h_tw_Y : ‖chartRSTwist (I := I) (M := M) α b r s Y‖ ≤ M_tw * ‖Y‖ :=
    hM_tw_le b hb Y
  -- Rewrite using the round-trip on the LHS.
  rw [h_round] at h_tw_Y
  -- Inverse-twist norm bound at `S.toFun b`:
  -- `‖chartRSTwistInv α b r s (S.toFun b)‖^2 ≤ K * tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)`.
  have h_inv : ‖Y‖ ^ 2 ≤
      K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by
    rw [hY_def]
    exact hK_le hb (S.toFun b)
  -- Square the chart-twist bound: `‖S.toFun b‖^2 ≤ (M_tw * ‖Y‖)^2 = M_tw^2 * ‖Y‖^2`.
  have h_lhs_nn : 0 ≤ ‖S.toFun b‖ := norm_nonneg _
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_M_tw_nn : 0 ≤ M_tw := le_of_lt hM_tw_pos
  have h_rhs_nn : 0 ≤ M_tw * ‖Y‖ := mul_nonneg h_M_tw_nn h_Y_nn
  have h_sq : ‖S.toFun b‖ ^ 2 ≤ (M_tw * ‖Y‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tw_Y
    have h_lhs_sq : ‖S.toFun b‖ * ‖S.toFun b‖ = ‖S.toFun b‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_tw * ‖Y‖) * (M_tw * ‖Y‖) = (M_tw * ‖Y‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_tw * ‖Y‖) ^ 2 = M_tw ^ 2 * ‖Y‖ ^ 2 := by ring
  -- Chain: ‖S.toFun b‖^2 ≤ M_tw^2 * ‖Y‖^2 ≤ M_tw^2 * (K * tensorInnerPointwise ...).
  have h_chain : ‖S.toFun b‖ ^ 2 ≤
      M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) := by
    have h_M_tw_sq_nn : 0 ≤ M_tw ^ 2 := sq_nonneg _
    have h_step1 : ‖S.toFun b‖ ^ 2 ≤ M_tw ^ 2 * ‖Y‖ ^ 2 := by
      calc ‖S.toFun b‖ ^ 2 ≤ (M_tw * ‖Y‖) ^ 2 := h_sq
        _ = M_tw ^ 2 * ‖Y‖ ^ 2 := h_expand
    have h_step2 : M_tw ^ 2 * ‖Y‖ ^ 2 ≤
        M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) :=
      mul_le_mul_of_nonneg_left h_inv h_M_tw_sq_nn
    exact h_step1.trans h_step2
  -- Reassociate `M_tw^2 * (K * X) = (M_tw^2 * K) * X`.
  have h_assoc :
      M_tw ^ 2 * (K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) =
      M_tw ^ 2 * K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by ring
  -- Apply the definitional identification `‖S.toSection b‖ = ‖S.toFun b‖`.
  rw [section_norm_eq_toFun_norm S b]
  linarith

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
end Sanity
