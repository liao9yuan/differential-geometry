import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Tensor.RSTensor.TangentContinuousRiemannianMetric
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Unconditional operator-norm bound for the chart Jacobian on compact sets

Given a smooth Riemannian metric `g` on a compact boundaryless manifold `M`,
the operator norm `‖chartJ α b‖` is uniformly bounded for `b` in any compact
`K ⊆ (trivializationAt E (TangentSpace I) α).baseSet`.
-/

noncomputable section

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Decomposition: chartJ α b = coordChangeL(y₀→α) ∘ chartJ y₀ b -/

private lemma chartJ_eq_coordChangeL_comp_apply (α y₀ : M) {b : M}
    (hb_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hb_y₀ : b ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) (v : E) :
    chartJ (I := I) (M := M) α b v =
      (Trivialization.coordChangeL ℝ
        (trivializationAt E (TangentSpace I) y₀)
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)
        (chartJ (I := I) (M := M) y₀ b v) := by
  have h1 := chartJinv_chartJ_self (I := I) (M := M) y₀ hb_y₀ v
  suffices h : (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) y₀)
      (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)
      (chartJ (I := I) (M := M) y₀ b v) =
    chartJ (I := I) (M := M) α b (chartJinv (I := I) (M := M) y₀ b
      (chartJ (I := I) (M := M) y₀ b v)) by rw [h, h1]
  unfold chartJ chartJinv
  have hboth : b ∈ (trivializationAt E (TangentSpace I) y₀).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet := ⟨hb_y₀, hb_α⟩
  change ((trivializationAt E (TangentSpace I) y₀).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) α) b)
      ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ b v) =
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
      ((trivializationAt E (TangentSpace I) y₀).symmL ℝ b
        ((trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ b v))
  rw [Trivialization.coordChangeL_apply _ _ hboth]
  simp only [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.symmL_apply]
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α]

/-! ## Main theorem -/

theorem chartJ_opNorm_isBounded_on_compact_unconditional
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {K : Set M} (hK : IsCompact K)
    (hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ‖chartJ (I := I) (M := M) α b‖ ≤ C := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock

end
