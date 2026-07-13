import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Quantitative inverse for a retained phase endpoint

This file packages the direct `ApproximatesLinearOn` construction for a map
close to the free retained-endpoint equivalence.
-/

noncomputable section

open Set Metric
open scoped ContDiff NNReal

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

/-- An open partial homeomorphism whose source and forward map realize a
quantitative approximation has a smooth inverse whenever its forward map is
smooth on that source. -/
theorem inv_smooth_of_approx [CompleteSpace E] [FiniteDimensional Real E]
    {f : E → E} {A : E ≃L[Real] E} {s : Set E} {c : NNReal}
    (hf : ApproximatesLinearOn f (A : E →L[Real] E) s c)
    (hc : Subsingleton E ∨ c < ‖(A.symm : E →L[Real] E)‖₊⁻¹)
    (hs : IsOpen s) (hsm : ContDiffOn Real ∞ f s)
    (e : OpenPartialHomeomorph E E) (hsource : e.source = s)
    (hcoe : (e : E → E) = f) :
    ContDiffOn Real ∞ e.symm e.target := by
  intro y hy
  have hx : e.symm y ∈ s := by
    rw [← hsource]
    exact e.map_target hy
  have hsmx : ContDiffAt Real ∞ f (e.symm y) :=
    hsm.contDiffAt (hs.mem_nhds hx)
  let D : E →L[Real] E := fderiv Real f (e.symm y)
  have hfD : HasFDerivAt f D (e.symm y) := by
    exact (hsmx.differentiableAt (by simp)).hasFDerivAt
  have hres : HasFDerivAt (f - (A : E → E)) (D - (A : E →L[Real] E))
      (e.symm y) := by
    simpa only [Pi.sub_apply] using hfD.sub A.hasFDerivAt
  have hDnorm : ‖D - (A : E →L[Real] E)‖ ≤ (c : Real) :=
    hres.le_of_lipschitzOn (hs.mem_nhds hx) hf.lipschitzOnWith
  have hDapprox : ApproximatesLinearOn (D : E → E) (A : E →L[Real] E)
      Set.univ c := by
    intro u _ v _
    have hbound := (D - (A : E →L[Real] E)).le_opNorm (u - v)
    have hmul : ‖D - (A : E →L[Real] E)‖ * ‖u - v‖ ≤
        (c : Real) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
    calc
      ‖D u - D v - A (u - v)‖ =
          ‖(D - (A : E →L[Real] E)) (u - v)‖ := by
        rw [← D.map_sub]
        rfl
      _ ≤ ‖D - (A : E →L[Real] E)‖ * ‖u - v‖ := hbound
      _ ≤ (c : Real) * ‖u - v‖ := hmul
  have hDinj : Function.Injective D := by
    rw [← Set.injOn_univ]
    exact hDapprox.injOn hc
  have hDsurj : Function.Surjective D :=
    LinearMap.surjective_of_injective hDinj
  let D' : E ≃L[Real] E := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hDinj) (LinearMap.range_eq_top.mpr hDsurj)
  have hfD' : HasFDerivAt f (D' : E →L[Real] E) (e.symm y) := by
    simpa only [D', ContinuousLinearEquiv.coe_ofBijective] using hfD
  have heD' : HasFDerivAt (e : E → E) (D' : E →L[Real] E) (e.symm y) := by
    rw [hcoe]
    exact hfD'
  have hesm : ContDiffAt Real ∞ (e : E → E) (e.symm y) := by
    rw [hcoe]
    exact hsmx
  exact (e.contDiffAt_symm hy heD' hesm).contDiffWithinAt

/-- The inverse of the exact quantitative partial homeomorphism is smooth on
its target whenever the forward map is smooth on the approximation domain. -/
theorem quantInv_smooth [CompleteSpace E] [FiniteDimensional Real E]
    {f : E → E} {A : E ≃L[Real] E} {s : Set E} {c : NNReal}
    (hf : ApproximatesLinearOn f (A : E →L[Real] E) s c)
    (hc : Subsingleton E ∨ c < ‖(A.symm : E →L[Real] E)‖₊⁻¹)
    (hs : IsOpen s) (hsm : ContDiffOn Real ∞ f s) :
    ContDiffOn Real ∞
      (hf.toOpenPartialHomeomorph (f' := A) f s hc hs).symm
      (hf.toOpenPartialHomeomorph (f' := A) f s hc hs).target := by
  apply inv_smooth_of_approx hf hc hs hsm
  · rfl
  · rfl

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
