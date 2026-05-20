import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartJUniformBoundLocallyConstant

/-!
# Uniform op-norm bound on the intrinsic chart Fréchet-derivative CLM

For ranks `r s : ℕ` and a chart centre `α : M`, the intrinsic chart
Fréchet-derivative piece
`tensorRSIntrinsicChartCLM r s α T b : TangentSpace I b →L[ℝ] TensorRSSpace r s I b`
admits a uniform pointwise operator-norm bound on any compact
`K ⊆ (chartAt H α).source` under the locally-constant-chart hypothesis
`HasLocallyConstantChartAt H M`. Concretely there is `C > 0` such that for
every `b ∈ K` and every tangent vector `X : TangentSpace I b`,

  `‖tensorRSIntrinsicChartCLM r s α T b X‖ ≤
      C * ‖fderiv ℝ (chart-pulled repr of T) (extChartAt I α b)‖ * ‖X‖`.

The constant `C` is independent of `T`, `b`, and `X`: it absorbs the uniform
op-norm bounds on the chart-`(r, s)` fibre right-inverse
`tensorRSChartFiberFromModel α b` and on the chart-Jacobian `chartJ α b`
(equivalently the tangent-bundle forward trivialisation `trivToE α b`).

## Strategy

By `tensorRSIntrinsicChartCLM_apply`,
`tensorRSIntrinsicChartCLM r s α T b X
  = tensorRSChartFiberFromModel r s α b (fderiv ℝ F (extChartAt I α b) (trivToE α b X))`
where `F = tensorRSChartE_section_repr r s α T ∘ (extChartAt I α).symm` is the
chart-pulled representation of `T`. The composition's norm is bounded by

  `‖tensorRSChartFiberFromModel α b‖ · ‖fderiv ℝ F (extChartAt I α b)‖
    · ‖trivToE α b‖ · ‖X‖`,

and the first and third factors admit uniform bounds on `K` from the
fibre-right-inverse op-norm bound and the chart-Jacobian op-norm bound.
-/

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
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Pointwise op-norm bound for `tensorRSIntrinsicChartCLM r s α T b` at a
single point `b`, parametrised by op-norm bounds on the two trivialisation
families. The Fréchet-derivative norm is read off the chart-pulled
representation of `T`. -/
private lemma tensorRSIntrinsicChartCLM_pointwise_opNorm_le_factors
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b') (b : M)
    {C_fib C_J : ℝ}
    (hC_fib : ∀ D : TensorRSModel r s ℝ E,
      ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * ‖D‖)
    (hC_fib_nn : 0 ≤ C_fib)
    (hC_J : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J)
    (_hC_J_nn : 0 ≤ C_J)
    (X : TangentSpace I b) :
    ‖tensorRSIntrinsicChartCLM (I := I) r s α T b X‖ ≤
      C_fib * C_J *
        ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T ∘
          (extChartAt I α).symm) (extChartAt I α b)‖ * ‖X‖ := by
  classical
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm with hF_def
  set p : E := extChartAt I α b with hp_def
  set D : TensorRSModel r s ℝ E := fderiv ℝ F p (trivToE (I := I) α b X) with hD_def
  -- Step 1: rewrite using the pointwise formula.
  have h_apply :
      tensorRSIntrinsicChartCLM (I := I) r s α T b X =
        tensorRSChartFiberFromModel (I := I) r s α b D := by
    rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T b X]
  rw [h_apply]
  -- Step 2: apply the fibre right-inverse pointwise op-norm bound.
  have h_fib_le : ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * ‖D‖ :=
    hC_fib D
  -- Step 3: bound `‖D‖` by `‖fderiv ℝ F p‖ * ‖trivToE α b X‖`.
  have h_D_le_fderiv :
      ‖D‖ ≤ ‖fderiv ℝ F p‖ * ‖trivToE (I := I) α b X‖ := by
    rw [hD_def]
    exact (fderiv ℝ F p).le_opNorm (trivToE (I := I) α b X)
  -- Step 4: bound `‖trivToE α b X‖ ≤ ‖trivToE α b‖ * ‖X‖`.
  have h_trivToE_le :
      ‖trivToE (I := I) α b X‖ ≤ ‖trivToE (I := I) α b‖ * ‖X‖ :=
    (trivToE (I := I) α b).le_opNorm X
  -- `‖trivToE α b‖ = ‖chartJ α b‖` definitionally.
  have h_triv_J :
      ‖trivToE (I := I) α b‖ = ‖chartJ (I := I) (M := M) α b‖ := rfl
  have h_X_nn : 0 ≤ ‖X‖ := norm_nonneg _
  have h_trivToE_le_CJ : ‖trivToE (I := I) α b X‖ ≤ C_J * ‖X‖ := by
    refine h_trivToE_le.trans ?_
    rw [h_triv_J]
    exact mul_le_mul_of_nonneg_right hC_J h_X_nn
  -- Step 5: combine `‖D‖ ≤ ‖fderiv ℝ F p‖ * (C_J * ‖X‖)`.
  set N : ℝ := ‖fderiv ℝ F p‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_trivToE_nn : 0 ≤ ‖trivToE (I := I) α b X‖ := norm_nonneg _
  have h_D_le :
      ‖D‖ ≤ N * (C_J * ‖X‖) :=
    h_D_le_fderiv.trans (mul_le_mul_of_nonneg_left h_trivToE_le_CJ hN_nn)
  -- Step 6: combine with the fibre bound.
  have h_D_nn : 0 ≤ ‖D‖ := norm_nonneg _
  have h_main_step :
      ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * (N * (C_J * ‖X‖)) :=
    h_fib_le.trans (mul_le_mul_of_nonneg_left h_D_le hC_fib_nn)
  -- Step 7: rearrange `C_fib * (N * (C_J * ‖X‖)) = C_fib * C_J * N * ‖X‖`.
  have h_rearrange :
      C_fib * (N * (C_J * ‖X‖)) = C_fib * C_J * N * ‖X‖ := by ring
  rw [h_rearrange] at h_main_step
  exact h_main_step

/-- **Uniform pointwise operator-norm bound** on the intrinsic chart
Fréchet-derivative CLM `tensorRSIntrinsicChartCLM r s α T b` over any compact
subset of the chart-`α` source.

The constant `C` is independent of `T`, `b ∈ K`, and `X : TangentSpace I b`,
and only depends on the chart at `α`, the locality hypothesis, and the
compact set `K`. The bound is in the natural form that pulls the
Fréchet-derivative norm out as a factor, since the CLM only depends on `T`
through this derivative. -/
theorem tensorRSIntrinsicChartCLM_opNorm_isBounded_on_compact
    (h_atlas : HasLocallyConstantChartAt H M)
    (r s : ℕ) (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Π b : M, TensorRSSpace r s I b),
      ∀ b ∈ K, ∀ X : TangentSpace I b,
        ‖tensorRSIntrinsicChartCLM (I := I) r s α T b X‖ ≤
          C * ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T ∘
            (extChartAt I α).symm) (extChartAt I α b)‖ * ‖X‖ := by
  classical
  -- Step 1: uniform fibre-right-inverse op-norm bound on K.
  obtain ⟨C_fib, hC_fib_pos, hC_fib_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) h_atlas r s α hK hKsub
  have hC_fib_nn : 0 ≤ C_fib := le_of_lt hC_fib_pos
  -- Step 2: uniform chart-Jacobian op-norm bound on K.
  obtain ⟨C_J, hC_J_pos, hC_J_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK hKsub
  have hC_J_nn : 0 ≤ C_J := le_of_lt hC_J_pos
  -- Set the headline constant.
  set C : ℝ := C_fib * C_J with hC_def
  have hC_pos : 0 < C := mul_pos hC_fib_pos hC_J_pos
  refine ⟨C, hC_pos, ?_⟩
  intro T b hb X
  have hC_fib_b : ∀ D : TensorRSModel r s ℝ E,
      ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * ‖D‖ :=
    fun D => hC_fib_bound b hb D
  have hC_J_b : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J := hC_J_bound b hb
  exact tensorRSIntrinsicChartCLM_pointwise_opNorm_le_factors
    (I := I) (M := M) r s α T b
    hC_fib_b hC_fib_nn hC_J_b hC_J_nn X

end Connection
end Integral
end DifferentialGeometry

end
