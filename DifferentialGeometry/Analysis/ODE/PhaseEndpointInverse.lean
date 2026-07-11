import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness

/-!
# Quantitative inverse for a retained phase endpoint

This file packages the direct `ApproximatesLinearOn` construction for a map
close to the free retained-endpoint equivalence.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry
namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- On a nontrivial phase space, the reciprocal inverse norm of the free
retained-endpoint equivalence is positive. -/
theorem freeDiagInv_pos [Nontrivial E] :
    0 < ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  let L : (E × E) →L[Real] (E × E) :=
    ((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))
  have hL : L ≠ 0 := by
    intro hzero
    apply not_subsingleton (E × E)
    constructor
    intro x y
    apply (freeDiagCLE (E := E)).symm.injective
    change L x = L y
    rw [hzero]
    rfl
  have hnorm : (0 : Real) < ‖L‖ := norm_pos_iff.mpr hL
  have hnn : (0 : NNReal) < ‖L‖₊ := by exact_mod_cast hnorm
  exact inv_pos.mpr hnn

/-- A map uniformly close to the free retained-endpoint equivalence on a
positive closed ball has a quantitative inverse branch on the corresponding
open ball.  Its target contains the displayed positive closed ball. -/
theorem exists_quant_inv [CompleteSpace E]
    {f : E × E → E × E} {q c : NNReal}
    (hq : 0 < q)
    (hf : ApproximatesLinearOn f freeDiag
      (closedBall (0 : E × E) q) c)
    (hc : c <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < δ ∧
      e.source = ball (0 : E × E) q ∧
      (e : E × E → E × E) = f ∧
      closedBall (f 0) δ ⊆ e.target ∧
      δ = ((‖((freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ - c : NNReal) : Real) *
        ((q : Real) / 2) := by
  let s : Set (E × E) := ball (0 : E × E) q
  have hfo : ApproximatesLinearOn f freeDiag s c :=
    hf.mono_set Metric.ball_subset_closedBall
  have hc' : Subsingleton (E × E) ∨ c <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ :=
    Or.inr hc
  let e : OpenPartialHomeomorph (E × E) (E × E) :=
    hfo.toOpenPartialHomeomorph (f' := freeDiagCLE (E := E)) f s hc' Metric.isOpen_ball
  let δ : Real := ((‖((freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹ - c : NNReal) : Real) *
    ((q : Real) / 2)
  have hmargin : 0 <
      ‖((freeDiagCLE (E := E)).symm : (E × E) →L[Real] (E × E))‖₊⁻¹ - c :=
    tsub_pos_iff_lt.mpr hc
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (by exact_mod_cast hmargin) (div_pos hqReal (by norm_num))
  have hhalf : closedBall (0 : E × E) ((q : Real) / 2) ⊆ s := by
    exact Metric.closedBall_subset_ball (half_lt_self hqReal)
  have htarget := hfo.closedBall_subset_target
    (f' := freeDiagCLE (E := E)) hc' Metric.isOpen_ball
    (b := (0 : E × E)) (ε := (q : Real) / 2) (by positivity) hhalf
  refine ⟨e, δ, hδ, ?_, ?_, ?_, rfl⟩
  · rfl
  · rfl
  · simpa [e, δ, s, NNReal.coe_sub hc.le] using htarget

end PhaseFlow
end DifferentialGeometry
