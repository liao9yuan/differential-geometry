import DifferentialGeometry.Integral.Connection.IntrinsicPieceIteratedFDerivTwoBound
import DifferentialGeometry.Integral.Connection.SlotCorrectionIteratedFDerivTwoBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.IteratedFDerivFourTensorReprChartCompBound

/-!
# Squared order-2 iterated Fréchet derivative bound for the chart-pulled
representation of `covApply ∇ B T`

Combining the intrinsic-piece order-2 iteratedFDeriv bound with the input /
output Christoffel slot-correction order-2 iteratedFDeriv bounds yields a
uniform bound on the squared norm of the order-2 iterated Fréchet derivative
of the chart-pulled representation of `covApply ∇ B T` at chart-coordinate
points whose preimage lies in the partition-of-unity tsupport intersected
with the chart-`α` Levi-Civita good set.

Concretely, for a smooth Riemannian manifold `(M, g)`, a chart-centre
`α : M`, ranks `r, s : ℕ`, a smooth tangent vector field `B`, and a smooth
compactly supported `(r, s)`-tensor section `T`, there is a constant
`K ≥ 0` (depending on `h_atlas`, `g`, the chart at `α`, the ranks `r`, `s`,
and `B`, but independent of `T` and `b`) such that for any `b ∈ tsupport
(POU α) ∩ chartLeviCivitaGoodSet α`, the squared norm of the order-2 iterated
Fréchet derivative of the chart-pulled representation of `covApply ∇ B T` at
`extChartAt I α b` is bounded by

```
K * Σ_{j ∈ Fin 4} ‖iteratedFDeriv ℝ j.val (repr T ∘ symm) (extChartAt I α b)‖²
```

where `repr T = tensorRSChartE_section_repr r s α T.toSection`.

## Strategy

1. By `chart_pulled_covApply_repr_eventuallyEq`, the chart-pulled
   representation of `covApply ∇ B T` equals an explicit three-piece sum
   (intrinsic piece + input-slot Christoffel correction sum − output-slot
   Christoffel correction sum) on a neighbourhood of `extChartAt I α b`.

2. `Filter.EventuallyEq.iteratedFDeriv` then identifies the order-2 iterated
   Fréchet derivative of the LHS with that of the three-piece sum at the
   chart point.

3. Each individual piece is `ContDiffAt 2`, so the order-2 iterated Fréchet
   derivative distributes across the sums and the subtraction via
   `iteratedFDeriv_fun_sum_apply`, `iteratedFDeriv_add_apply`, and
   `iteratedFDeriv_sub_apply`.

4. The triangle inequality and the three per-piece bounds
   (`intrinsic_piece_iteratedFDeriv_two_bound`,
   `inputSlot_correction_iteratedFDeriv_two_bound`,
   `outputSlot_correction_iteratedFDeriv_two_bound`) bound the order-2
   iteratedFDeriv norm by `K' · (‖iter 3 F‖ + ‖iter 2 F‖ + ‖fderiv F‖ + ‖F‖)`
   where `F = repr T ∘ symm`.

5. Squaring and using `(a+b+c+d)² ≤ 4(a² + b² + c² + d²)` together with
   `norm_iteratedFDeriv_zero` and `norm_iteratedFDeriv_one` then expresses
   the bound as `K · Σ_{j ∈ Fin 4} ‖iter j F‖²`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## ContDiffAt-2 facts for each of the three pieces at the chart point -/

/-- The intrinsic piece is `ContDiffAt ∞` at `extChartAt I α b` whenever `b`
lies in the chart-`α` Levi-Civita good set. -/
private lemma intrinsicPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  -- ContDiffOn ∞ of `fderiv F` on U.
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hc_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)) U :=
    hF_cd.fderiv_of_isOpen hU_open h_le
  -- ContDiffOn ∞ of `u = chartE_section_repr α B ∘ symm` on U.
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  -- ContDiffAt 2 of `c · u` at the chart point.
  have hc_at : ContDiffAt ℝ 2
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by intro h; exact absurd h (by simp)
    have h_at_top : ContDiffAt ℝ ∞
        (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm))
        (extChartAt I α b) :=
      (hc_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hu_at : ContDiffAt ℝ 2
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hu_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  -- `clm_apply` lifts to ContDiffAt of `c y (u y)`.
  exact hc_at.clm_apply hu_at

/-- The chart-pulled input-slot correction is `ContDiffAt 2` at the chart
point. -/
private lemma inputSlotPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  -- ContDiffOn ∞ of the chart kernel pulled back by symm.
  have hK_cd : ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B k
  -- ContDiffOn ∞ of repr T pulled back by symm.
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  -- ContDiffAt 2 of kernel and repr T.
  have hK_at : ContDiffAt ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))
        (extChartAt I α b) :=
      (hK_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hF_at : ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hF_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  -- ContDiffAt 2 of `kernel · F`.
  have h_kernel_F_at : ContDiffAt ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y))
      (extChartAt I α b) := hK_at.clm_apply hF_at
  -- Pointwise equality on a neighbourhood of `extChartAt I α b`.
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    exact chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx'_inv]; exact hx'_src) k
  exact h_kernel_F_at.congr_of_eventuallyEq h_evt

/-- The chart-pulled output-slot correction is `ContDiffAt 2` at the chart
point. -/
private lemma outputSlotPiece_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ 2
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l))
      (extChartAt I α b) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈ U := ⟨b, hb_good, rfl⟩
  have hK_cd : ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B l
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hK_at : ContDiffAt ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))
        (extChartAt I α b) :=
      (hK_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have hF_at : ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have h_at_top : ContDiffAt ℝ ∞
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b) :=
      (hF_cd (extChartAt I α b) hx_mem).contDiffAt
        (hU_open.mem_nhds hx_mem)
    have h2_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
      show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact (WithTop.coe_le_coe.mpr h1 : _)
    exact h_at_top.of_le h2_le
  have h_kernel_F_at : ContDiffAt ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y))
      (extChartAt I α b) := hK_at.clm_apply hF_at
  have h_evt :
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
              (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    exact chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx'_inv]; exact hx'_src) l
  exact h_kernel_F_at.congr_of_eventuallyEq h_evt

/-! ## Pointwise eventual equality from the chart-pulled explicit formula -/

/-- The chart-pulled representation of `covApply ∇ B T` is, on an open
neighbourhood of `extChartAt I α b`, equal to the intrinsic piece plus
input-slot Christoffel corrections minus output-slot Christoffel
corrections. Re-derived here (mirrors the helper in
`ChartPulledCovApplyReprFderivBound`) to avoid relying on a private lemma. -/
private lemma chart_pulled_covApply_repr_eventuallyEq'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y)))
        + ∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
              ℝ ((extChartAt I α).symm y)
              (chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) k)
        - ∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
              ℝ ((extChartAt I α).symm y)
              (chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) l)) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hmem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  refine Filter.eventually_of_mem (hU_open.mem_nhds hmem) ?_
  intro y hy
  rcases hy with ⟨x, hx_good, hxy⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hx_extsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hy_target : y ∈ (extChartAt I α).target := by
    rw [← hxy]; exact (extChartAt I α).map_source hx_extsrc
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have hsymm_good :
      (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [hx_inv]; exact hx_good
  exact chart_pulled_covApply_explicit_formula_target_smoothCc
    (I := I) (M := M) g r s α T B hy_target hsymm_good

/-! ## Headline -/

/-- **Squared order-2 iterated Fréchet derivative bound for the chart-pulled
representation of the first covariant derivative.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a smooth tangent vector field `B`, and a smooth compactly
supported `(r, s)`-tensor section `T`, the squared norm of the order-2
iterated Fréchet derivative of the chart-pulled representation of
`covApply ∇ B T` at `extChartAt I α b` is bounded by `K · Σ_{j ∈ Fin 4} ‖iter
j F (extChartAt I α b)‖²`, where `F = repr T ∘ symm`.

The constant `K` depends only on `h_atlas`, `g`, `α`, `r`, `s`, and `B`. -/
theorem chart_pulled_covApply_repr_iteratedFDeriv_two_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun z : M =>
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)) B.toFun
                    (fun w : M => T.toSection w)) z)) ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 ≤
          K *
            (∑ j : Fin 4,
              ‖iteratedFDeriv ℝ j.val
                  ((tensorRSChartE_section_repr (I := I) r s α
                      (fun z : M => T.toSection z)) ∘ (extChartAt I α).symm)
                  (extChartAt I α b)‖ ^ 2) := by
  classical
  -- Step 1: collect the per-piece bounds.
  obtain ⟨K_I, hKI_nn, hKI_bound⟩ :=
    intrinsic_piece_iteratedFDeriv_two_bound (I := I) (M := M) g r s α B
  have h_in_choose : ∀ k : Fin r, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
          (fun y : E =>
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm y)
              (chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) k))
          (extChartAt I α b)‖ ≤
        K * (‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)
                ((extChartAt I α).symm (extChartAt I α b))‖) := fun k =>
    inputSlot_correction_iteratedFDeriv_two_bound
      (I := I) (M := M) h_atlas g r s α B k
  choose K_in hKin_nn hKin_bound using h_in_choose
  have h_out_choose : ∀ l : Fin s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
          (fun y : E =>
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm y)
              (chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) l))
          (extChartAt I α b)‖ ≤
        K * (‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)
                ((extChartAt I α).symm (extChartAt I α b))‖) := fun l =>
    outputSlot_correction_iteratedFDeriv_two_bound
      (I := I) (M := M) h_atlas g r s α B l
  choose K_out hKout_nn hKout_bound using h_out_choose
  -- Define the combined linear-in-(‖iter k F‖) constant K' :=
  -- K_I + (∑ k, K_in k) + (∑ l, K_out l).
  set K' : ℝ := K_I + (∑ k : Fin r, K_in k) + (∑ l : Fin s, K_out l) with hK'_def
  have hKin_sum_nn : 0 ≤ ∑ k : Fin r, K_in k :=
    Finset.sum_nonneg (fun k _ => hKin_nn k)
  have hKout_sum_nn : 0 ≤ ∑ l : Fin s, K_out l :=
    Finset.sum_nonneg (fun l _ => hKout_nn l)
  have hK'_nn : 0 ≤ K' := by
    rw [hK'_def]; linarith
  -- Now produce the headline constant: K := 4 · K'².
  refine ⟨4 * K' ^ 2, by positivity, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Step 2: eventually-equal three-piece sum on a neighbourhood of `extChartAt I α b`.
  have h_evt :=
    chart_pulled_covApply_repr_eventuallyEq' (I := I) (M := M) g r s α T B hb_good
  -- Step 3: write the iteratedFDeriv of the 3-piece sum as a sum of iteratedFDerivs.
  -- Set up abbreviations.
  set x : E := extChartAt I α b with hx_def
  set Pi_intr : E → TensorRSModel r s ℝ E := fun y : E =>
    fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
      (trivToE (I := I) α ((extChartAt I α).symm y)
        (B.toFun ((extChartAt I α).symm y))) with hPi_intr_def
  set Pi_in : Fin r → E → TensorRSModel r s ℝ E := fun (k : Fin r) (y : E) =>
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) k) with hPi_in_def
  set Pi_out : Fin s → E → TensorRSModel r s ℝ E := fun (l : Fin s) (y : E) =>
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) l) with hPi_out_def
  -- ContDiffAt-2 of each piece.
  have h_intr_at : ContDiffAt ℝ 2 Pi_intr x :=
    intrinsicPiece_contDiffAt_two (I := I) (M := M) g r s α T B hb_good
  have h_in_at : ∀ k : Fin r, ContDiffAt ℝ 2 (Pi_in k) x := fun k =>
    inputSlotPiece_contDiffAt_two (I := I) (M := M) g r s α T B k hb_good
  have h_out_at : ∀ l : Fin s, ContDiffAt ℝ 2 (Pi_out l) x := fun l =>
    outputSlotPiece_contDiffAt_two (I := I) (M := M) g r s α T B l hb_good
  -- Sum of inputs is ContDiffAt 2.
  have h_in_sum_at : ContDiffAt ℝ 2
      (fun y : E => ∑ k : Fin r, Pi_in k y) x :=
    ContDiffAt.sum (fun k _ => h_in_at k)
  have h_out_sum_at : ContDiffAt ℝ 2
      (fun y : E => ∑ l : Fin s, Pi_out l y) x :=
    ContDiffAt.sum (fun l _ => h_out_at l)
  -- Step 6: distribute iteratedFDeriv across +, -, ∑.
  -- iteratedFDeriv (intr + ∑in - ∑out) = iteratedFDeriv intr + iteratedFDeriv (∑in) - iteratedFDeriv (∑out)
  -- Use iteratedFDeriv_sub_apply on (intr + ∑in, ∑out), then iteratedFDeriv_add_apply on (intr, ∑in).
  have h_intr_plus_in_at : ContDiffAt ℝ 2
      (fun y : E => Pi_intr y + ∑ k : Fin r, Pi_in k y) x :=
    h_intr_at.add h_in_sum_at
  -- The 3-piece sum.
  set RHS_fn : E → TensorRSModel r s ℝ E := fun y : E =>
    Pi_intr y + (∑ k : Fin r, Pi_in k y) - (∑ l : Fin s, Pi_out l y) with hRHS_def
  -- The LHS function (the one we want to bound the iteratedFDeriv 2 of).
  set LHS_fn : E → TensorRSModel r s ℝ E :=
    (tensorRSChartE_section_repr (I := I) r s α
        (fun z : M =>
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun
            (fun w : M => T.toSection w)) z)) ∘
      (extChartAt I α).symm with hLHS_def
  -- h_evt is `LHS_fn =ᶠ[𝓝 x] RHS_fn` but written with `+` and `-` as binary ops.
  -- Verify h_evt unfolds correctly to LHS_fn =ᶠ[𝓝 x] RHS_fn.
  have h_evt' : LHS_fn =ᶠ[𝓝 x] RHS_fn := by
    refine h_evt.mono ?_
    intro y hy
    show LHS_fn y = RHS_fn y
    change (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun y' : M => T.toSection y')) ∘ (extChartAt I α).symm) y =
      Pi_intr y + (∑ k : Fin r, Pi_in k y) - (∑ l : Fin s, Pi_out l y)
    exact hy
  -- iteratedFDeriv 2 of LHS_fn = iteratedFDeriv 2 of RHS_fn at x.
  have h_iter_eq : iteratedFDeriv ℝ 2 LHS_fn x = iteratedFDeriv ℝ 2 RHS_fn x := by
    have := Filter.EventuallyEq.iteratedFDeriv ℝ h_evt' 2
    exact this.eq_of_nhds
  -- Distribute iteratedFDeriv 2 over sub on RHS_fn.
  -- RHS_fn = (Pi_intr + ∑Pi_in) - ∑Pi_out, so
  -- iteratedFDeriv 2 RHS_fn = iteratedFDeriv 2 (Pi_intr + ∑Pi_in) - iteratedFDeriv 2 (∑Pi_out).
  have h_iter_sub : iteratedFDeriv ℝ 2 RHS_fn x =
      iteratedFDeriv ℝ 2 (fun y : E => Pi_intr y + ∑ k : Fin r, Pi_in k y) x -
        iteratedFDeriv ℝ 2 (fun y : E => ∑ l : Fin s, Pi_out l y) x := by
    have h := fun_iteratedFDeriv_sub_apply (f := fun y : E => Pi_intr y + ∑ k : Fin r, Pi_in k y)
      (g := fun y : E => ∑ l : Fin s, Pi_out l y)
      (i := 2) (𝕜 := ℝ) (x := x)
      h_intr_plus_in_at h_out_sum_at
    change iteratedFDeriv ℝ 2
        (fun y : E => (Pi_intr y + ∑ k : Fin r, Pi_in k y) -
            ∑ l : Fin s, Pi_out l y) x = _
    convert h using 0
  -- iteratedFDeriv 2 (Pi_intr + ∑Pi_in) = iteratedFDeriv 2 Pi_intr + iteratedFDeriv 2 (∑Pi_in).
  have h_iter_add : iteratedFDeriv ℝ 2
      (fun y : E => Pi_intr y + ∑ k : Fin r, Pi_in k y) x =
      iteratedFDeriv ℝ 2 Pi_intr x +
        iteratedFDeriv ℝ 2 (fun y : E => ∑ k : Fin r, Pi_in k y) x := by
    have h := fun_iteratedFDeriv_add_apply (f := Pi_intr)
      (g := fun y : E => ∑ k : Fin r, Pi_in k y)
      (i := 2) (𝕜 := ℝ) (x := x) h_intr_at h_in_sum_at
    convert h using 0
  -- iteratedFDeriv 2 (∑ k, Pi_in k) = ∑ k, iteratedFDeriv 2 (Pi_in k).
  have h_iter_in_sum : iteratedFDeriv ℝ 2
      (fun y : E => ∑ k : Fin r, Pi_in k y) x =
      ∑ k : Fin r, iteratedFDeriv ℝ 2 (Pi_in k) x :=
    iteratedFDeriv_fun_sum_apply (h := fun k _ => h_in_at k)
  have h_iter_out_sum : iteratedFDeriv ℝ 2
      (fun y : E => ∑ l : Fin s, Pi_out l y) x =
      ∑ l : Fin s, iteratedFDeriv ℝ 2 (Pi_out l) x :=
    iteratedFDeriv_fun_sum_apply (h := fun l _ => h_out_at l)
  -- Combine: iteratedFDeriv 2 LHS_fn x =
  --   iteratedFDeriv 2 Pi_intr x + ∑k iter 2 (Pi_in k) - ∑l iter 2 (Pi_out l).
  have h_iter_decomp : iteratedFDeriv ℝ 2 LHS_fn x =
      iteratedFDeriv ℝ 2 Pi_intr x +
        (∑ k : Fin r, iteratedFDeriv ℝ 2 (Pi_in k) x) -
        ∑ l : Fin s, iteratedFDeriv ℝ 2 (Pi_out l) x := by
    rw [h_iter_eq, h_iter_sub, h_iter_add, h_iter_in_sum, h_iter_out_sum]
  -- Step 7: triangle inequality to bound the norm.
  -- ‖iter 2 LHS_fn x‖ ≤ ‖iter 2 Pi_intr x‖ + ∑k ‖iter 2 (Pi_in k)‖ + ∑l ‖iter 2 (Pi_out l)‖.
  have h_triangle :
      ‖iteratedFDeriv ℝ 2 LHS_fn x‖ ≤
        ‖iteratedFDeriv ℝ 2 Pi_intr x‖ +
          (∑ k : Fin r, ‖iteratedFDeriv ℝ 2 (Pi_in k) x‖) +
          ∑ l : Fin s, ‖iteratedFDeriv ℝ 2 (Pi_out l) x‖ := by
    rw [h_iter_decomp]
    have h1 := norm_sub_le
      (iteratedFDeriv ℝ 2 Pi_intr x +
        ∑ k : Fin r, iteratedFDeriv ℝ 2 (Pi_in k) x)
      (∑ l : Fin s, iteratedFDeriv ℝ 2 (Pi_out l) x)
    have h2 := norm_add_le
      (iteratedFDeriv ℝ 2 Pi_intr x)
      (∑ k : Fin r, iteratedFDeriv ℝ 2 (Pi_in k) x)
    have h3 := norm_sum_le (Finset.univ : Finset (Fin r))
      (fun k => iteratedFDeriv ℝ 2 (Pi_in k) x)
    have h4 := norm_sum_le (Finset.univ : Finset (Fin s))
      (fun l => iteratedFDeriv ℝ 2 (Pi_out l) x)
    linarith
  -- Step 8: apply per-piece bounds.
  -- Abbreviations.
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ with hV_def
  set F1 : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      x‖ with hF1_def
  set F2 : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      x‖ with hF2_def
  set F3 : ℝ := ‖iteratedFDeriv ℝ 3
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      x‖ with hF3_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF1_nn : 0 ≤ F1 := norm_nonneg _
  have hF2_nn : 0 ≤ F2 := norm_nonneg _
  have hF3_nn : 0 ≤ F3 := norm_nonneg _
  -- Intrinsic piece bound.
  have h_intr_bound :
      ‖iteratedFDeriv ℝ 2 Pi_intr x‖ ≤ K_I * (F3 + F2 + F1) := by
    have := hKI_bound T hb
    exact this
  -- Input slot bounds: each ≤ K_in k * (F2 + F1 + V'), where V' is
  -- ‖repr T (symm (extChartAt I α b))‖. We need V' = V.
  -- Note (extChartAt I α).symm (extChartAt I α b) = b under hb_good.
  have hsymm_b : (extChartAt I α).symm (extChartAt I α b) = b := by
    have hb_chart : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact (extChartAt I α).left_inv hb_extsrc
  have hV_eq : ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y)
        ((extChartAt I α).symm (extChartAt I α b))‖ = V := by
    rw [hsymm_b]
  have h_in_bound_pt : ∀ k : Fin r,
      ‖iteratedFDeriv ℝ 2 (Pi_in k) x‖ ≤ K_in k * (F2 + F1 + V) := fun k => by
    have h := hKin_bound k T hb
    rw [hV_eq] at h
    exact h
  have h_out_bound_pt : ∀ l : Fin s,
      ‖iteratedFDeriv ℝ 2 (Pi_out l) x‖ ≤ K_out l * (F2 + F1 + V) := fun l => by
    have h := hKout_bound l T hb
    rw [hV_eq] at h
    exact h
  -- Sum bounds.
  have h_in_sum_bound :
      (∑ k : Fin r, ‖iteratedFDeriv ℝ 2 (Pi_in k) x‖) ≤
        (∑ k : Fin r, K_in k) * (F2 + F1 + V) := by
    calc ∑ k : Fin r, _
        ≤ ∑ k : Fin r, K_in k * (F2 + F1 + V) :=
          Finset.sum_le_sum (fun k _ => h_in_bound_pt k)
      _ = (∑ k : Fin r, K_in k) * (F2 + F1 + V) := by rw [Finset.sum_mul]
  have h_out_sum_bound :
      (∑ l : Fin s, ‖iteratedFDeriv ℝ 2 (Pi_out l) x‖) ≤
        (∑ l : Fin s, K_out l) * (F2 + F1 + V) := by
    calc ∑ l : Fin s, _
        ≤ ∑ l : Fin s, K_out l * (F2 + F1 + V) :=
          Finset.sum_le_sum (fun l _ => h_out_bound_pt l)
      _ = (∑ l : Fin s, K_out l) * (F2 + F1 + V) := by rw [Finset.sum_mul]
  -- Each individual piece's argument bound (F3+F2+F1 ≤ F3+F2+F1+V, F2+F1+V ≤ F3+F2+F1+V).
  have h_sum_combined :
      ‖iteratedFDeriv ℝ 2 Pi_intr x‖ +
        (∑ k : Fin r, ‖iteratedFDeriv ℝ 2 (Pi_in k) x‖) +
        ∑ l : Fin s, ‖iteratedFDeriv ℝ 2 (Pi_out l) x‖ ≤
      K_I * (F3 + F2 + F1) +
        (∑ k : Fin r, K_in k) * (F2 + F1 + V) +
        (∑ l : Fin s, K_out l) * (F2 + F1 + V) := by
    linarith [h_intr_bound, h_in_sum_bound, h_out_sum_bound]
  -- The big bound: F3+F2+F1 ≤ F3+F2+F1+V and F2+F1+V ≤ F3+F2+F1+V.
  have h_intr_arg_le : F3 + F2 + F1 ≤ F3 + F2 + F1 + V := by linarith
  have h_slot_arg_le : F2 + F1 + V ≤ F3 + F2 + F1 + V := by linarith
  have h_KI_le : K_I * (F3 + F2 + F1) ≤ K_I * (F3 + F2 + F1 + V) :=
    mul_le_mul_of_nonneg_left h_intr_arg_le hKI_nn
  have h_Kin_le : (∑ k : Fin r, K_in k) * (F2 + F1 + V) ≤
      (∑ k : Fin r, K_in k) * (F3 + F2 + F1 + V) :=
    mul_le_mul_of_nonneg_left h_slot_arg_le hKin_sum_nn
  have h_Kout_le : (∑ l : Fin s, K_out l) * (F2 + F1 + V) ≤
      (∑ l : Fin s, K_out l) * (F3 + F2 + F1 + V) :=
    mul_le_mul_of_nonneg_left h_slot_arg_le hKout_sum_nn
  -- Combine into K' * (F3 + F2 + F1 + V).
  have h_combined_K' :
      K_I * (F3 + F2 + F1) +
        (∑ k : Fin r, K_in k) * (F2 + F1 + V) +
        (∑ l : Fin s, K_out l) * (F2 + F1 + V) ≤
      K' * (F3 + F2 + F1 + V) := by
    have h_eq : K' * (F3 + F2 + F1 + V) =
        K_I * (F3 + F2 + F1 + V) + (∑ k : Fin r, K_in k) * (F3 + F2 + F1 + V) +
          (∑ l : Fin s, K_out l) * (F3 + F2 + F1 + V) := by
      rw [hK'_def]; ring
    linarith [h_eq, h_KI_le, h_Kin_le, h_Kout_le]
  -- Step 9: linear bound on `‖iter 2 LHS_fn x‖`.
  have h_norm_bound : ‖iteratedFDeriv ℝ 2 LHS_fn x‖ ≤ K' * (F3 + F2 + F1 + V) := by
    refine le_trans h_triangle ?_
    linarith [h_sum_combined, h_combined_K']
  -- Step 10: square the bound.
  -- (K' * (F3+F2+F1+V))² = K'² * (F3+F2+F1+V)²
  -- (F3+F2+F1+V)² ≤ 4 (F3² + F2² + F1² + V²)
  have h_norm_lhs_nn : 0 ≤ ‖iteratedFDeriv ℝ 2 LHS_fn x‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ K' * (F3 + F2 + F1 + V) := by
    have : 0 ≤ F3 + F2 + F1 + V := by linarith
    exact mul_nonneg hK'_nn this
  -- Squaring monotone.
  have h_sq_le_sq :
      ‖iteratedFDeriv ℝ 2 LHS_fn x‖ ^ 2 ≤ (K' * (F3 + F2 + F1 + V)) ^ 2 := by
    exact pow_le_pow_left₀ h_norm_lhs_nn h_norm_bound 2
  -- (K' * S)² = K'² · S² where S = F3 + F2 + F1 + V.
  have h_sq_split : (K' * (F3 + F2 + F1 + V)) ^ 2 = K' ^ 2 * (F3 + F2 + F1 + V) ^ 2 := by
    ring
  -- (a + b + c + d)² ≤ 4(a² + b² + c² + d²) for a, b, c, d ≥ 0.
  -- Use the identity (a+b+c+d)² + (a-b)² + (a-c)² + (a-d)² + (b-c)² + (b-d)² + (c-d)²
  -- = 4(a² + b² + c² + d²).
  have h_four_sq : (F3 + F2 + F1 + V) ^ 2 ≤ 4 * (F3 ^ 2 + F2 ^ 2 + F1 ^ 2 + V ^ 2) := by
    have h_sq1 : 0 ≤ (F3 - F2) ^ 2 := sq_nonneg _
    have h_sq2 : 0 ≤ (F3 - F1) ^ 2 := sq_nonneg _
    have h_sq3 : 0 ≤ (F3 - V) ^ 2 := sq_nonneg _
    have h_sq4 : 0 ≤ (F2 - F1) ^ 2 := sq_nonneg _
    have h_sq5 : 0 ≤ (F2 - V) ^ 2 := sq_nonneg _
    have h_sq6 : 0 ≤ (F1 - V) ^ 2 := sq_nonneg _
    have h_id : 4 * (F3 ^ 2 + F2 ^ 2 + F1 ^ 2 + V ^ 2) - (F3 + F2 + F1 + V) ^ 2 =
        (F3 - F2) ^ 2 + (F3 - F1) ^ 2 + (F3 - V) ^ 2 +
        (F2 - F1) ^ 2 + (F2 - V) ^ 2 + (F1 - V) ^ 2 := by ring
    linarith [h_id]
  -- Express ‖iter 0 F‖ = ‖F (extChartAt I α b)‖ = V and ‖iter 1 F‖ = ‖fderiv F (extChartAt I α b)‖ = F1.
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def_local
  have h_iter0_F : ‖iteratedFDeriv ℝ 0 F x‖ = V := by
    rw [norm_iteratedFDeriv_zero]
    change ‖F x‖ = V
    rw [hV_def]
    have : F x = tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b := by
      rw [hF_def_local]
      change tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) ((extChartAt I α).symm x) = _
      rw [hx_def, hsymm_b]
    rw [this]
  have h_iter1_F : ‖iteratedFDeriv ℝ 1 F x‖ = F1 := by
    rw [norm_iteratedFDeriv_one]
  have h_iter2_F : ‖iteratedFDeriv ℝ 2 F x‖ = F2 := rfl
  have h_iter3_F : ‖iteratedFDeriv ℝ 3 F x‖ = F3 := rfl
  -- ∑ j : Fin 4, ‖iter j F‖² = V² + F1² + F2² + F3².
  have h_fin4_sum :
      (∑ j : Fin 4,
        ‖iteratedFDeriv ℝ j.val
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun z : M => T.toSection z)) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2) =
      V ^ 2 + F1 ^ 2 + F2 ^ 2 + F3 ^ 2 := by
    -- Unfold Fin 4 sum.
    simp only [Fin.sum_univ_four]
    -- j.val for j ∈ {0,1,2,3} is 0, 1, 2, 3.
    -- We need to identify the function inside the sum with F.
    change ‖iteratedFDeriv ℝ 0 F x‖ ^ 2 + ‖iteratedFDeriv ℝ 1 F x‖ ^ 2 +
         ‖iteratedFDeriv ℝ 2 F x‖ ^ 2 + ‖iteratedFDeriv ℝ 3 F x‖ ^ 2 =
         V ^ 2 + F1 ^ 2 + F2 ^ 2 + F3 ^ 2
    rw [h_iter0_F, h_iter1_F, h_iter2_F, h_iter3_F]
  -- The LHS of the goal: ‖iter 2 (covApply ∇ B T ∘ symm)‖² = ‖iter 2 LHS_fn x‖².
  -- Now combine: ‖iter 2 LHS_fn x‖² ≤ K'² · 4 · ∑.
  have h_final :
      ‖iteratedFDeriv ℝ 2 LHS_fn x‖ ^ 2 ≤
        4 * K' ^ 2 * (V ^ 2 + F1 ^ 2 + F2 ^ 2 + F3 ^ 2) := by
    calc ‖iteratedFDeriv ℝ 2 LHS_fn x‖ ^ 2
        ≤ (K' * (F3 + F2 + F1 + V)) ^ 2 := h_sq_le_sq
      _ = K' ^ 2 * (F3 + F2 + F1 + V) ^ 2 := h_sq_split
      _ ≤ K' ^ 2 * (4 * (F3 ^ 2 + F2 ^ 2 + F1 ^ 2 + V ^ 2)) := by
            have hK'sq_nn : 0 ≤ K' ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left h_four_sq hK'sq_nn
      _ = 4 * K' ^ 2 * (V ^ 2 + F1 ^ 2 + F2 ^ 2 + F3 ^ 2) := by ring
  -- Goal LHS = ‖iter 2 LHS_fn x‖². Substitute.
  -- The LHS of the goal references LHS_fn since the definition matches.
  rw [h_fin4_sum]
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_covApply_repr_iteratedFDeriv_two_bound
end Sanity
