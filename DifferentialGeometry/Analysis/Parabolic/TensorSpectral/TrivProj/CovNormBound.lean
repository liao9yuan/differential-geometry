import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.NormComparison
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerCovDiagonalBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerPointwiseUpperBound

/-!
# Sum-over-directions bound on the chart-twist-inverted covariant derivative

For a closed Riemannian manifold `(M, g)` and a chart base point `α`, this
file controls the sum over directions of the squared Euclidean norm of the
inverse chart-`(α, b)`-twist applied to the model-fibre image of the
covariant derivative of a smooth compactly-supported `(r, s)`-tensor section
along the chart-`α` basis fibres. The bound's right-hand side is the
intrinsic pointwise gradient inner product
`tensorCovDerivPointwiseInner g r s S S b` of the section against itself.

## Strategy

Let `cov_i := tensorCovDerivAt g r s S b (chartBasisVecFiber α i b)`. For each
`i`, set `T_i := chartRSTwistInv α b r s (TensorRSSpace.toModel cov_i)`. The
chart-frame quadratic norm bound (Group A's primary headline) gives
`‖T_i‖^2 ≤ K * chartTensorInnerPointwise_rs_model g r s α b T_i T_i`. The
bridge identity rewrites the chart-frame diagonal value as a bundle-fibre
diagonal value on the chart-twisted tensor, and the round-trip
`chartRSTwist ∘ chartRSTwistInv = id` (valid on the chart base set) collapses
the twisted argument to `TensorRSSpace.toModel cov_i`. Summing over `i` and
chaining with `TensorInnerCovDiagonalBound` (the diagonal-sum bound for the
covariant-derivative inner product) yields the headline.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Per-direction chart-trivialisation norm bound

For each direction `i`, the squared Euclidean norm of the inverse
chart-`(α, b)`-twist applied to the model image of the covariant derivative
along the chart-`α` basis fibre `chartBasisVecFiber α i b` is controlled by
the bundle-fibre diagonal pointwise inner product on the model image. This
is a one-line specialisation of Group A's primary headline composed with the
bridge identity and the chart-twist round-trip. -/

/-- **Per-direction chart-trivialisation norm bound.** For `b` in the closed
support of the chart-atlas partition-of-unity weight at `α`, and any model
`(r, s)`-tensor `X`,
`‖chartRSTwistInv α b r s X‖^2 ≤ K * tensorInnerPointwise g r s b X X`. -/
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X := by
  classical
  -- Group A's primary headline on the chart-frame quadratic form.
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro b hb X
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  -- Set `T := chartRSTwistInv α b r s X`. Apply the chart-frame bound at `T`.
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s X with hT_def
  have h_T : ‖T‖ ^ 2 ≤ K *
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T :=
    h_chart b hb T
  -- Bridge: chart-frame quad on `T` equals bundle-fibre quad on `chartRSTwist α b T`.
  have h_bridge :
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T)
          (chartRSTwist (I := I) (M := M) α b r s T) :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T
  -- Round-trip: `chartRSTwist α b (chartRSTwistInv α b X) = X` on the base set.
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = X := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s X
  rw [h_bridge, h_round] at h_T
  exact h_T

/-! ## Headline sum-over-directions bound -/

/-- **Sum-over-directions bound on the chart-twist-inverted covariant
derivative.** For a closed Riemannian manifold `(M, g)`, a chart base point
`α`, and ranks `(r, s)`, there exists a non-negative constant `C` such that
for every smooth compactly-supported `(r, s)`-tensor section `S` and every
base point `b` in the closed support of the chart-atlas partition-of-unity
weight at `α`, the sum over `i` of the squared Euclidean norm of
`chartRSTwistInv α b r s (TensorRSSpace.toModel (∇S(b)(e_i')))` is bounded
by `C` times the intrinsic gradient inner product
`tensorCovDerivPointwiseInner g r s S S b`, where
`e_i' = chartBasisVecFiber α i b` is the chart-`α` basis fibre at `b`.

The constant `C` decomposes as `K * C'`, where `K` is the Group A
chart-frame norm comparison constant and `C'` is the diagonal-sum control
constant from the chart-Gram inverse Rayleigh-quotient lower bound. -/
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  -- Per-direction chart-trivialisation norm bound (constant `K`).
  obtain ⟨K, hK_nn, h_per⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α
  -- Diagonal-sum bound (constant `C'`, from sub-substep 3.b).
  obtain ⟨C', hC'_nn, h_diag⟩ :=
    exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
      (I := I) (M := M) g r s α
  refine ⟨K * C', mul_nonneg hK_nn hC'_nn, ?_⟩
  intro S b hb
  -- Abbreviate `cov i := TensorRSSpace.toModel (∇S(b)(e_i' b))`.
  set cov : Fin (Module.finrank ℝ E) → TensorRSModel r s ℝ E := fun i =>
    TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) with hcov_def
  -- Diagonal sum of bundle-fibre inner products at `cov i`.
  set D : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b (cov i) (cov i) with hD_def
  -- The diagonal sum is bounded by `C' * tensorCovDerivPointwiseInner`.
  have h_D_le : D ≤ C' * tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s S S b := by
    rw [hD_def]
    exact h_diag S hb
  -- Per-direction sum bound: `∑ ‖chartRSTwistInv α b (cov i)‖^2 ≤ K * D`.
  have h_sum_le_KD :
      ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2 ≤
        K * D := by
    rw [hD_def, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    exact h_per hb (cov i)
  -- Non-negativity of `K` plus the diagonal-sum bound chains the two estimates.
  have h_KD_le : K * D ≤
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) :=
    mul_le_mul_of_nonneg_left h_D_le hK_nn
  -- Combine and reshape `K * (C' * X) = (K * C') * X`.
  have h_assoc :
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) =
        (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
    ring
  -- Conclude by transitivity.
  calc ∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2
      ≤ K * D := h_sum_le_KD
    _ ≤ K * (C' * tensorCovDerivPointwiseInner
              (I := I) (M := M) g r s S S b) := h_KD_le
    _ = (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := h_assoc

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
