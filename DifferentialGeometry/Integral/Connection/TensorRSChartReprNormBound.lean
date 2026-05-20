import DifferentialGeometry.Integral.Connection.TensorRSChartFiberOpNorm
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm

/-!
# Reverse uniform bound: fibre norm by the model-side representation norm

For a chart centre `α : M` and ranks `r s : ℕ`, the fibre norm of any
`T : TensorRSSpace r s I b` is uniformly controlled by the norm of its
chart-`α` model-side image
`((triv α).continuousLinearMapAt ℝ b T : TensorRSModel r s ℝ E)` on any compact
`K ⊆ (chartAt H α).source`. Concretely there exists `C > 0` such that
`‖T‖ ≤ C * ‖(triv α).continuousLinearMapAt ℝ b T‖` for every `b ∈ K` and every
`T : TensorRSSpace r s I b`.

This is the reverse-direction counterpart to
`tensorRSChartFiberToModel_opNorm_isBounded_on_compact` and is an immediate
consequence of the previously established right-inverse bound
`tensorRSChartFiberFromModel_opNorm_isBounded_on_compact` together with the
identity `(triv α).symmL ((triv α).continuousLinearMapAt T) = T` valid on the
trivialisation base set.

## Main result

* `tensorRSSpace_norm_le_chartRepr_norm_on_compact` — uniform pointwise
  bound `‖T‖ ≤ C * ‖(triv α).clmAt T‖` over a compact subset of the chart-`α`
  source.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Reverse uniform pointwise bound** for the chart-`(r, s)` fibre forward
trivialisation: the source-side fibre norm `‖T‖` is uniformly controlled by the
norm of the chart-`α` model image
`((triv α).continuousLinearMapAt ℝ b T : TensorRSModel r s ℝ E)` over any
compact subset of the chart-`α` source. -/
theorem tensorRSSpace_norm_le_chartRepr_norm_on_compact
    (h_atlas : HasLocallyConstantChartAt H M)
    (r s : ℕ) (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ T : TensorRSSpace r s I b,
      ‖T‖ ≤ C * ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E)‖ := by
  -- The right-inverse `(triv α).symmL ℝ b = tensorRSChartFiberFromModel r s α b`
  -- has uniform op-norm bound on `K`; apply this bound to
  -- `D := (triv α).clmAt ℝ b T` and use `symmL ∘ clmAt = id` on the base set.
  obtain ⟨C, hC_pos, hC⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK) (hKsub := hKsub)
  refine ⟨C, hC_pos, ?_⟩
  intro b hb T
  -- Translate `b ∈ chart source` into membership in the tensor-RS bundle's
  -- base set at `α`, using the `(r, s)`-bundle's base set computation from
  -- the forward file's pattern.
  have hb_α : b ∈ (chartAt H α).source := hKsub hb
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hb_α
  have hb_α' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  -- The fundamental inverse identity: `symmL ∘ clmAt = id` on the base set.
  have h_inv :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T) = T :=
    Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) hb_α' T
  -- Apply the right-inverse bound to `D := (triv α).clmAt ℝ b T`.
  have h_bound := hC b hb
    (((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
        TensorRSModel r s ℝ E))
  -- `tensorRSChartFiberFromModel r s α b` is definitionally `(triv α).symmL ℝ b`.
  have h_unfold :
      tensorRSChartFiberFromModel (I := I) r s α b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T) =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T) :=
    rfl
  rw [h_unfold, h_inv] at h_bound
  exact h_bound

end DifferentialGeometry.Integral.Connection

end
