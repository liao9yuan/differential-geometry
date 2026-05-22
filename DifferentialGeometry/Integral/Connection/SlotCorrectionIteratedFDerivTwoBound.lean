import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceIteratedFDerivTwoBound

/-!
# Order-2 iterated Fréchet derivative bound for the chart-pulled input/output
Christoffel slot corrections

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r s : ℕ`, a smooth tangent vector field `B`, a slot index `k : Fin r`
(input) or `l : Fin s` (output), and a smooth compactly supported
`(r, s)`-tensor section `T`, the chart-`α`-pulled slot correction has the
form

  `Ψ(y) := (kernel y) (F y)`,

where `F = tensorRSChartE_section_repr r s α T.toSection ∘ (extChartAt I α).symm`
and `kernel` is the chart-pulled input (resp. output) slot kernel.

This file ships the uniform bound

  `‖iteratedFDeriv ℝ 2 Ψ (extChartAt I α b)‖
      ≤ K * (‖iteratedFDeriv ℝ 2 F (extChartAt I α b)‖
             + ‖fderiv ℝ F (extChartAt I α b)‖
             + ‖F (extChartAt I α b)‖)`

for `b` in the intersection of the chart-`α` partition-of-unity tsupport
and the chart-`α` Levi-Civita good set. The constant `K` depends on
`g`, `α`, the locality hypothesis on the chart atlas, the ranks `r`, `s`,
the slot index, and `B`, but is independent of `T` and `b`.

## Strategy

Mirror the proof of `intrinsic_piece_iteratedFDeriv_two_bound`, but with
`c(y) := kernel y` and `u(y) := F y`. By
`norm_iteratedFDerivWithin_clm_apply` on the open chart-target image of the
chart-`α` Levi-Civita good set,

  `‖iteratedFDerivWithin 2 (c·u) U y‖
      ≤ ∑_{k=0,1,2} C(2,k) · ‖iteratedFDerivWithin k c U y‖
          · ‖iteratedFDerivWithin (2-k) u U y‖`.

Since `U` is open, `iteratedFDerivWithin = iteratedFDeriv` on `U`. The
factors `‖iteratedFDeriv k c‖` for `k = 0, 1, 2` are bounded uniformly on
the POU tsupport ∩ good set; the order-0 and order-1 bounds come from
`*_opNorm_uniform_on_pouTsupport` and
`*_fderiv_opNorm_uniform_on_pouTsupport`. The order-2 bound follows from
continuity of `iteratedFDeriv 2 (kernel ∘ symm)` on the open good-set
image and compactness of the POU tsupport.

## Main results

* `inputSlot_correction_iteratedFDeriv_two_bound` — uniform bound on the
  order-2 iterated Fréchet derivative of the chart-pulled input-slot
  Christoffel correction.
* `outputSlot_correction_iteratedFDeriv_two_bound` — analogous bound for
  the output slot. -/

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

/-! ## Step 1: pointwise equality on the good-set image

The chart-pulled slot correction equals `kernel · F` on a neighborhood of
`extChartAt I α b`, allowing us to swap the iterated Fréchet derivative
via `Filter.EventuallyEq.iteratedFDeriv_eq`. The same pointwise equality
that drives the order-1 bound also drives the order-2 bound. -/

/-- Pointwise equality between the chart-pulled input-slot correction and the
chart-kernel applied to `tensorRSChartE_section_repr`, on a neighbourhood of
`extChartAt I α b`. Repackages
`input_slot_pulled_eq_kernel_eventually` as an `EventuallyEq`. -/
private lemma input_slot_pulled_eq_kernel_repr_eventually
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
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
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have h_factor :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx_inv]; exact hx_src) k
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) k) =
    inputSlotChartKernel (I := I) g r s α B.toFun k
      ((extChartAt I α).symm y)
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
  exact h_factor

/-- Pointwise equality between the chart-pulled output-slot correction and
the chart-kernel applied to `tensorRSChartE_section_repr`, on a
neighbourhood of `extChartAt I α b`. -/
private lemma output_slot_pulled_eq_kernel_repr_eventually
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)
          ((tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y)) := by
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
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  have h_factor :=
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx_inv]; exact hx_src) l
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
      ((extChartAt I α).symm y)
      (chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun y' : M => T.toSection y') B.toFun
        ((extChartAt I α).symm y) l) =
    outputSlotChartKernel (I := I) g r s α B.toFun l
      ((extChartAt I α).symm y)
      (tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
  exact h_factor

/-! ## Step 2: uniform iteratedFDeriv-2 bound on the kernel over POU tsupport -/

/-- Continuity on the open chart-target image of the chart-`α` Levi-Civita
good set of `‖iteratedFDeriv ℝ 2 (kernel ∘ symm)‖`, where `kernel` is the
input-slot kernel. -/
private lemma inputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ 2
        (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hcd : ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B k
  have hk_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_2 : ContDiffOn ℝ 2
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y)) U :=
    hcd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) U) U :=
    hcd_2.continuousOn_iteratedFDerivWithin (m := 2) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) U)
      (iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))) U :=
    iteratedFDerivWithin_of_isOpen 2 hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y))) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

/-- Continuity on the open chart-target image of the chart-`α` Levi-Civita
good set of `‖iteratedFDeriv ℝ 2 (kernel ∘ symm)‖`, where `kernel` is the
output-slot kernel. -/
private lemma outputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ 2
        (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hcd : ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B l
  have hk_le : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_2 : ContDiffOn ℝ 2
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y)) U :=
    hcd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) U) U :=
    hcd_2.continuousOn_iteratedFDerivWithin (m := 2) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) U)
      (iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))) U :=
    iteratedFDerivWithin_of_isOpen 2 hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y))) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

/-- Under `[I.Boundaryless]`, the chart-α partition-of-unity tsupport lies in
the chart-α Levi-Civita good set. -/
private lemma pouTsupport_subset_goodSet (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have h_eq :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source
    (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M) α hb

/-- Uniform bound on `‖iteratedFDeriv ℝ 2 (inputSlotChartKernel ∘ symm)‖`
over the POU tsupport ∩ good set. -/
private lemma inputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
            (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := inputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (I := I) (M := M) g r s α B k
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

/-- Uniform bound on `‖iteratedFDeriv ℝ 2 (outputSlotChartKernel ∘ symm)‖`
over the POU tsupport ∩ good set. -/
private lemma outputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
            (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := outputSlotChartKernel_iteratedFDeriv_two_continuousOn
    (I := I) (M := M) g r s α B l
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps

  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

/-! ## Step 3: headline — input slot -/

/-- **Order-2 iteratedFDeriv bound for the chart-pulled input-slot
Christoffel correction.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
tangent vector field `B`, ranks `r, s : ℕ`, and an input-slot index
`k : Fin r`, there is a constant `K ≥ 0` (depending on the locality
hypothesis on the chart atlas, the metric `g`, the chart at `α`, the ranks,
the slot index, and `B`, but independent of `T` and `b`) such that for any
smooth compactly supported `(r, s)`-tensor section `T` and any `b` in the
intersection of the chart-`α` partition-of-unity tsupport and the chart-`α`
Levi-Civita good set,

  `‖iteratedFDeriv ℝ 2 (chart_pulled_input_slot_correction T B) (extChartAt I α b)‖
      ≤ K * (‖iteratedFDeriv ℝ 2 F (extChartAt I α b)‖
             + ‖fderiv ℝ F (extChartAt I α b)‖
             + ‖F (extChartAt I α b)‖)`

where `F = tensorRSChartE_section_repr r s α T.toSection ∘ (extChartAt I α).symm`. -/
theorem inputSlot_correction_iteratedFDeriv_two_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
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
                ((extChartAt I α).symm (extChartAt I α b))‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨K0, hK0_nn, hK0_bound⟩ :=
    inputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B k
  obtain ⟨K1, hK1_nn, hK1_bound⟩ :=
    inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B k
  obtain ⟨K2, hK2_nn, hK2_bound⟩ :=
    inputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B k
  -- The bound is by ‖iter 0 c‖·‖iter 2 F‖ + 2·‖iter 1 c‖·‖iter 1 F‖
  --              + ‖iter 2 c‖·‖iter 0 F‖ ≤ (K0+2K1+K2)·(N₂+N₁+N₀).
  -- Take K_total := max (max K0 K1) (max K2 2*K1).
  set K_total : ℝ := max (max K0 (2 * K1)) K2 with hKtotal_def
  have hK1_2_nn : 0 ≤ 2 * K1 := by positivity
  have hK_total_nn : 0 ≤ K_total :=
    le_trans hK0_nn (le_trans (le_max_left K0 _) (le_max_left _ K2))
  refine ⟨K_total, hK_total_nn, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def
  set c : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) :=
    fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
      ((extChartAt I α).symm y) with hc_def
  set x : E := extChartAt I α b with hx_def
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  -- Step 1: rewrite via `Filter.EventuallyEq.iteratedFDeriv`.
  have h_evt :
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) k)) =ᶠ[𝓝 x]
        (fun y : E => c y (F y)) :=
    input_slot_pulled_eq_kernel_repr_eventually (I := I) (M := M)
      g r s α T B k hb_good
  have h_iter_evt :=
    Filter.EventuallyEq.iteratedFDeriv ℝ h_evt 2
  have h_iter_at_x : iteratedFDeriv ℝ 2
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) k)) x =
      iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x :=
    h_iter_evt.eq_of_nhds
  rw [h_iter_at_x]
  -- Step 2: set up smoothness on U.
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hF_cd : ContDiffOn ℝ ∞ F U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hc_cd : ContDiffOn ℝ ∞ c U :=
    inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B k
  have hx_mem : x ∈ U := ⟨b, hb_good, rfl⟩
  have hUniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  -- Apply `norm_iteratedFDerivWithin_clm_apply` with `n = 2`.
  have h_two_le_top : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have h_leibniz_within :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDerivWithin ℝ i c U x‖ *
            ‖iteratedFDerivWithin ℝ (2 - i) F U x‖ :=
    norm_iteratedFDerivWithin_clm_apply hc_cd hF_cd hUniqueDiff hx_mem h_two_le_top
  -- Step 3: transfer iteratedFDerivWithin to iteratedFDeriv on the open set U at x.
  have h_iter_c : ∀ j : ℕ,
      iteratedFDerivWithin ℝ j c U x = iteratedFDeriv ℝ j c x := by
    intro j; exact iteratedFDerivWithin_of_isOpen j hU_open hx_mem
  have h_iter_F : ∀ j : ℕ,
      iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x := by
    intro j; exact iteratedFDerivWithin_of_isOpen j hU_open hx_mem
  have h_iter_clm :
      iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x =
        iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x :=
    iteratedFDerivWithin_of_isOpen 2 hU_open hx_mem
  have h_norm_clm :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x‖ =
        ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ := by
    rw [h_iter_clm]
  have h_norm_iter_c : ∀ j : ℕ,
      ‖iteratedFDerivWithin ℝ j c U x‖ = ‖iteratedFDeriv ℝ j c x‖ := by
    intro j; rw [h_iter_c j]
  have h_norm_iter_F : ∀ j : ℕ,
      ‖iteratedFDerivWithin ℝ j F U x‖ = ‖iteratedFDeriv ℝ j F x‖ := by
    intro j; rw [h_iter_F j]
  -- Rewrite the Leibniz bound in terms of global iteratedFDeriv.
  have h_leibniz_global :
      ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (2 - i) F x‖ := by
    rw [← h_norm_clm]
    refine le_trans h_leibniz_within ?_
    apply Finset.sum_le_sum
    intro i _
    rw [h_norm_iter_c i, h_norm_iter_F (2 - i)]
  -- Step 4: expand the sum explicitly (indices 0, 1, 2).
  have h_choose_0 : ((2 : ℕ).choose 0 : ℝ) = 1 := by norm_num
  have h_choose_1 : ((2 : ℕ).choose 1 : ℝ) = 2 := by norm_num
  have h_choose_2 : ((2 : ℕ).choose 2 : ℝ) = 1 := by norm_num
  have h_sum_eq :
      ∑ i ∈ Finset.range (2 + 1),
        ↑((2 : ℕ).choose i) *
          ‖iteratedFDeriv ℝ i c x‖ *
          ‖iteratedFDeriv ℝ (2 - i) F x‖ =
        ‖iteratedFDeriv ℝ 0 c x‖ * ‖iteratedFDeriv ℝ 2 F x‖ +
        (2 : ℝ) * ‖iteratedFDeriv ℝ 1 c x‖ * ‖iteratedFDeriv ℝ 1 F x‖ +
        ‖iteratedFDeriv ℝ 2 c x‖ * ‖iteratedFDeriv ℝ 0 F x‖ := by
    rw [show (2 + 1 : ℕ) = 3 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [zero_add, h_choose_0, h_choose_1, h_choose_2]
    have h_sub_0 : (2 - 0 : ℕ) = 2 := by norm_num
    have h_sub_1 : (2 - 1 : ℕ) = 1 := by norm_num
    have h_sub_2 : (2 - 2 : ℕ) = 0 := by norm_num
    rw [h_sub_0, h_sub_1, h_sub_2]
    ring
  rw [h_sum_eq] at h_leibniz_global
  -- Step 5: identify ‖iteratedFDeriv 0 c‖ = ‖c‖ and ‖iteratedFDeriv 1 c‖ = ‖fderiv c‖.
  have h_iter0_c : ‖iteratedFDeriv ℝ 0 c x‖ = ‖c x‖ :=
    norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := c) (x := x)
  have h_iter1_c : ‖iteratedFDeriv ℝ 1 c x‖ = ‖fderiv ℝ c x‖ :=
    norm_iteratedFDeriv_one (𝕜 := ℝ) c (x := x)
  have h_iter0_F : ‖iteratedFDeriv ℝ 0 F x‖ = ‖F x‖ :=
    norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := F) (x := x)
  have h_iter1_F : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ :=
    norm_iteratedFDeriv_one (𝕜 := ℝ) F (x := x)
  rw [h_iter0_c, h_iter1_c, h_iter0_F, h_iter1_F] at h_leibniz_global
  -- Step 6: apply the uniform bounds on ‖c‖, ‖fderiv c‖, ‖iter 2 c‖ over POU tsupport.
  -- Recall c x = inputSlotChartKernel ... ((symm) x) = inputSlotChartKernel ... b.
  have hsymm_x : (extChartAt I α).symm x = b := by
    rw [hx_def]
    have hb_chart : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact (extChartAt I α).left_inv hb_extsrc
  have hc_at_x :
      c x = inputSlotChartKernel (I := I) g r s α B.toFun k b := by
    change inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm x) =
      inputSlotChartKernel (I := I) g r s α B.toFun k b
    rw [hsymm_x]
  have h_c0_bound : ‖c x‖ ≤ K0 := by
    rw [hc_at_x]
    exact hK0_bound hb
  have h_c1_bound : ‖fderiv ℝ c x‖ ≤ K1 := by
    change ‖fderiv ℝ
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K1
    exact hK1_bound hb
  have h_c2_bound : ‖iteratedFDeriv ℝ 2 c x‖ ≤ K2 := by
    change ‖iteratedFDeriv ℝ 2
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K2
    exact hK2_bound hb
  -- Step 7: combine. Denote N₀ := ‖F x‖, N₁ := ‖fderiv F x‖, N₂ := ‖iter 2 F x‖.
  -- We have:
  --   ‖c x‖·N₂ + 2·‖fderiv c x‖·N₁ + ‖iter 2 c x‖·N₀
  --   ≤ K0·N₂ + 2K1·N₁ + K2·N₀
  --   ≤ K_total·(N₂+N₁+N₀).
  set N0 : ℝ := ‖F x‖ with hN0_def
  set N1 : ℝ := ‖fderiv ℝ F x‖ with hN1_def
  set N2 : ℝ := ‖iteratedFDeriv ℝ 2 F x‖ with hN2_def
  have hN0_nn : 0 ≤ N0 := norm_nonneg _
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have hN2_nn : 0 ≤ N2 := norm_nonneg _
  have h_cn_nn : 0 ≤ ‖c x‖ := norm_nonneg _
  have h_dcn_nn : 0 ≤ ‖fderiv ℝ c x‖ := norm_nonneg _
  have h_iter2cn_nn : 0 ≤ ‖iteratedFDeriv ℝ 2 c x‖ := norm_nonneg _
  -- Bound each summand.
  have h_b1 : ‖c x‖ * N2 ≤ K0 * N2 :=
    mul_le_mul_of_nonneg_right h_c0_bound hN2_nn
  have h_b2 : (2 : ℝ) * ‖fderiv ℝ c x‖ * N1 ≤ (2 * K1) * N1 := by
    have h_left : (2 : ℝ) * ‖fderiv ℝ c x‖ ≤ 2 * K1 := by
      have := mul_le_mul_of_nonneg_left h_c1_bound (by norm_num : (0:ℝ) ≤ 2)
      exact this
    exact mul_le_mul_of_nonneg_right h_left hN1_nn
  have h_b3 : ‖iteratedFDeriv ℝ 2 c x‖ * N0 ≤ K2 * N0 :=
    mul_le_mul_of_nonneg_right h_c2_bound hN0_nn
  -- Each K_i is bounded by K_total. Compute step by step.
  have hK0_le : K0 ≤ K_total := by
    have h1 : K0 ≤ max K0 (2 * K1) := le_max_left _ _
    have h2 : max K0 (2 * K1) ≤ max (max K0 (2 * K1)) K2 := le_max_left _ _
    exact le_trans h1 h2
  have h2K1_le : 2 * K1 ≤ K_total := by
    have h1 : 2 * K1 ≤ max K0 (2 * K1) := le_max_right _ _
    have h2 : max K0 (2 * K1) ≤ max (max K0 (2 * K1)) K2 := le_max_left _ _
    exact le_trans h1 h2
  have hK2_le : K2 ≤ K_total := le_max_right _ _
  have h_K0_N2 : K0 * N2 ≤ K_total * N2 :=
    mul_le_mul_of_nonneg_right hK0_le hN2_nn
  have h_2K1_N1 : (2 * K1) * N1 ≤ K_total * N1 :=
    mul_le_mul_of_nonneg_right h2K1_le hN1_nn
  have h_K2_N0 : K2 * N0 ≤ K_total * N0 :=
    mul_le_mul_of_nonneg_right hK2_le hN0_nn
  have h_sum_bound :
      ‖c x‖ * N2 + (2 : ℝ) * ‖fderiv ℝ c x‖ * N1 +
        ‖iteratedFDeriv ℝ 2 c x‖ * N0 ≤
      K_total * N2 + K_total * N1 + K_total * N0 := by
    linarith [h_b1, h_b2, h_b3, h_K0_N2, h_2K1_N1, h_K2_N0]
  have h_total_factor :
      K_total * N2 + K_total * N1 + K_total * N0 =
        K_total * (N2 + N1 + N0) := by ring
  -- Goal RHS: K_total · (‖iter 2 F (φ b)‖ + ‖fderiv F (φ b)‖ + ‖repr T ((symm) (φ b))‖).
  -- Note: ‖F (φ b)‖ = ‖repr T ((symm) (φ b))‖ by definition of F.
  have h_F_at_x : N0 =
      ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y)
        ((extChartAt I α).symm (extChartAt I α b))‖ := by
    rw [hN0_def, hF_def, hx_def]
    rfl
  -- Combine h_leibniz_global (in N0 form) with h_sum_bound (in N0 form) and
  -- finally express N0 as ‖repr T (symm (φ b))‖.
  have h_combined : ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
      K_total * (N2 + N1 +
        ‖tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y)
          ((extChartAt I α).symm (extChartAt I α b))‖) := by
    have h_chain : ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
        K_total * (N2 + N1 + N0) := by
      refine le_trans h_leibniz_global ?_
      linarith [h_sum_bound, h_total_factor]
    rw [h_F_at_x] at h_chain
    exact h_chain
  exact h_combined

/-! ## Step 4: headline — output slot -/

/-- **Order-2 iteratedFDeriv bound for the chart-pulled output-slot
Christoffel correction.**

Analogue of `inputSlot_correction_iteratedFDeriv_two_bound` with the
output-slot kernel. -/
theorem outputSlot_correction_iteratedFDeriv_two_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
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
                ((extChartAt I α).symm (extChartAt I α b))‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨K0, hK0_nn, hK0_bound⟩ :=
    outputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B l
  obtain ⟨K1, hK1_nn, hK1_bound⟩ :=
    outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B l
  obtain ⟨K2, hK2_nn, hK2_bound⟩ :=
    outputSlotChartKernel_iteratedFDeriv_two_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B l
  set K_total : ℝ := max (max K0 (2 * K1)) K2 with hKtotal_def
  have hK1_2_nn : 0 ≤ 2 * K1 := by positivity
  have hK_total_nn : 0 ≤ K_total :=
    le_trans hK0_nn (le_trans (le_max_left K0 _) (le_max_left _ K2))
  refine ⟨K_total, hK_total_nn, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def
  set c : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) :=
    fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
      ((extChartAt I α).symm y) with hc_def
  set x : E := extChartAt I α b with hx_def
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have h_evt :
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) l)) =ᶠ[𝓝 x]
        (fun y : E => c y (F y)) :=
    output_slot_pulled_eq_kernel_repr_eventually (I := I) (M := M)
      g r s α T B l hb_good
  have h_iter_evt :=
    Filter.EventuallyEq.iteratedFDeriv ℝ h_evt 2
  have h_iter_at_x : iteratedFDeriv ℝ 2
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) l)) x =
      iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x :=
    h_iter_evt.eq_of_nhds
  rw [h_iter_at_x]
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hF_cd : ContDiffOn ℝ ∞ F U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hc_cd : ContDiffOn ℝ ∞ c U :=
    outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M) g r s α B l
  have hx_mem : x ∈ U := ⟨b, hb_good, rfl⟩
  have hUniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  have h_two_le_top : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have h_leibniz_within :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDerivWithin ℝ i c U x‖ *
            ‖iteratedFDerivWithin ℝ (2 - i) F U x‖ :=
    norm_iteratedFDerivWithin_clm_apply hc_cd hF_cd hUniqueDiff hx_mem h_two_le_top
  have h_iter_c : ∀ j : ℕ,
      iteratedFDerivWithin ℝ j c U x = iteratedFDeriv ℝ j c x := by
    intro j; exact iteratedFDerivWithin_of_isOpen j hU_open hx_mem
  have h_iter_F : ∀ j : ℕ,
      iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x := by
    intro j; exact iteratedFDerivWithin_of_isOpen j hU_open hx_mem
  have h_iter_clm :
      iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x =
        iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x :=
    iteratedFDerivWithin_of_isOpen 2 hU_open hx_mem
  have h_norm_clm :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => c y (F y)) U x‖ =
        ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ := by
    rw [h_iter_clm]
  have h_norm_iter_c : ∀ j : ℕ,
      ‖iteratedFDerivWithin ℝ j c U x‖ = ‖iteratedFDeriv ℝ j c x‖ := by
    intro j; rw [h_iter_c j]
  have h_norm_iter_F : ∀ j : ℕ,
      ‖iteratedFDerivWithin ℝ j F U x‖ = ‖iteratedFDeriv ℝ j F x‖ := by
    intro j; rw [h_iter_F j]
  have h_leibniz_global :
      ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (2 - i) F x‖ := by
    rw [← h_norm_clm]
    refine le_trans h_leibniz_within ?_
    apply Finset.sum_le_sum
    intro i _
    rw [h_norm_iter_c i, h_norm_iter_F (2 - i)]
  have h_choose_0 : ((2 : ℕ).choose 0 : ℝ) = 1 := by norm_num
  have h_choose_1 : ((2 : ℕ).choose 1 : ℝ) = 2 := by norm_num
  have h_choose_2 : ((2 : ℕ).choose 2 : ℝ) = 1 := by norm_num
  have h_sum_eq :
      ∑ i ∈ Finset.range (2 + 1),
        ↑((2 : ℕ).choose i) *
          ‖iteratedFDeriv ℝ i c x‖ *
          ‖iteratedFDeriv ℝ (2 - i) F x‖ =
        ‖iteratedFDeriv ℝ 0 c x‖ * ‖iteratedFDeriv ℝ 2 F x‖ +
        (2 : ℝ) * ‖iteratedFDeriv ℝ 1 c x‖ * ‖iteratedFDeriv ℝ 1 F x‖ +
        ‖iteratedFDeriv ℝ 2 c x‖ * ‖iteratedFDeriv ℝ 0 F x‖ := by
    rw [show (2 + 1 : ℕ) = 3 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [zero_add, h_choose_0, h_choose_1, h_choose_2]
    have h_sub_0 : (2 - 0 : ℕ) = 2 := by norm_num
    have h_sub_1 : (2 - 1 : ℕ) = 1 := by norm_num
    have h_sub_2 : (2 - 2 : ℕ) = 0 := by norm_num
    rw [h_sub_0, h_sub_1, h_sub_2]
    ring
  rw [h_sum_eq] at h_leibniz_global
  have h_iter0_c : ‖iteratedFDeriv ℝ 0 c x‖ = ‖c x‖ :=
    norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := c) (x := x)
  have h_iter1_c : ‖iteratedFDeriv ℝ 1 c x‖ = ‖fderiv ℝ c x‖ :=
    norm_iteratedFDeriv_one (𝕜 := ℝ) c (x := x)
  have h_iter0_F : ‖iteratedFDeriv ℝ 0 F x‖ = ‖F x‖ :=
    norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := F) (x := x)
  have h_iter1_F : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ :=
    norm_iteratedFDeriv_one (𝕜 := ℝ) F (x := x)
  rw [h_iter0_c, h_iter1_c, h_iter0_F, h_iter1_F] at h_leibniz_global
  have hsymm_x : (extChartAt I α).symm x = b := by
    rw [hx_def]
    have hb_chart : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact (extChartAt I α).left_inv hb_extsrc
  have hc_at_x :
      c x = outputSlotChartKernel (I := I) g r s α B.toFun l b := by
    change outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm x) =
      outputSlotChartKernel (I := I) g r s α B.toFun l b
    rw [hsymm_x]
  have h_c0_bound : ‖c x‖ ≤ K0 := by
    rw [hc_at_x]
    exact hK0_bound hb
  have h_c1_bound : ‖fderiv ℝ c x‖ ≤ K1 := by
    change ‖fderiv ℝ
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K1
    exact hK1_bound hb
  have h_c2_bound : ‖iteratedFDeriv ℝ 2 c x‖ ≤ K2 := by
    change ‖iteratedFDeriv ℝ 2
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K2
    exact hK2_bound hb
  set N0 : ℝ := ‖F x‖ with hN0_def
  set N1 : ℝ := ‖fderiv ℝ F x‖ with hN1_def
  set N2 : ℝ := ‖iteratedFDeriv ℝ 2 F x‖ with hN2_def
  have hN0_nn : 0 ≤ N0 := norm_nonneg _
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have hN2_nn : 0 ≤ N2 := norm_nonneg _
  have h_cn_nn : 0 ≤ ‖c x‖ := norm_nonneg _
  have h_dcn_nn : 0 ≤ ‖fderiv ℝ c x‖ := norm_nonneg _
  have h_iter2cn_nn : 0 ≤ ‖iteratedFDeriv ℝ 2 c x‖ := norm_nonneg _
  have h_b1 : ‖c x‖ * N2 ≤ K0 * N2 :=
    mul_le_mul_of_nonneg_right h_c0_bound hN2_nn
  have h_b2 : (2 : ℝ) * ‖fderiv ℝ c x‖ * N1 ≤ (2 * K1) * N1 := by
    have h_left : (2 : ℝ) * ‖fderiv ℝ c x‖ ≤ 2 * K1 := by
      have := mul_le_mul_of_nonneg_left h_c1_bound (by norm_num : (0:ℝ) ≤ 2)
      exact this
    exact mul_le_mul_of_nonneg_right h_left hN1_nn
  have h_b3 : ‖iteratedFDeriv ℝ 2 c x‖ * N0 ≤ K2 * N0 :=
    mul_le_mul_of_nonneg_right h_c2_bound hN0_nn
  have hK0_le : K0 ≤ K_total := by
    have h1 : K0 ≤ max K0 (2 * K1) := le_max_left _ _
    have h2 : max K0 (2 * K1) ≤ max (max K0 (2 * K1)) K2 := le_max_left _ _
    exact le_trans h1 h2
  have h2K1_le : 2 * K1 ≤ K_total := by
    have h1 : 2 * K1 ≤ max K0 (2 * K1) := le_max_right _ _
    have h2 : max K0 (2 * K1) ≤ max (max K0 (2 * K1)) K2 := le_max_left _ _
    exact le_trans h1 h2
  have hK2_le : K2 ≤ K_total := le_max_right _ _
  have h_K0_N2 : K0 * N2 ≤ K_total * N2 :=
    mul_le_mul_of_nonneg_right hK0_le hN2_nn
  have h_2K1_N1 : (2 * K1) * N1 ≤ K_total * N1 :=
    mul_le_mul_of_nonneg_right h2K1_le hN1_nn
  have h_K2_N0 : K2 * N0 ≤ K_total * N0 :=
    mul_le_mul_of_nonneg_right hK2_le hN0_nn
  have h_sum_bound :
      ‖c x‖ * N2 + (2 : ℝ) * ‖fderiv ℝ c x‖ * N1 +
        ‖iteratedFDeriv ℝ 2 c x‖ * N0 ≤
      K_total * N2 + K_total * N1 + K_total * N0 := by
    linarith [h_b1, h_b2, h_b3, h_K0_N2, h_2K1_N1, h_K2_N0]
  have h_F_at_x : N0 =
      ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y)
        ((extChartAt I α).symm (extChartAt I α b))‖ := by
    rw [hN0_def, hF_def, hx_def]
    rfl
  have h_total_factor :
      K_total * N2 + K_total * N1 + K_total * N0 =
        K_total * (N2 + N1 + N0) := by ring
  have h_combined : ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
      K_total * (N2 + N1 +
        ‖tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y)
          ((extChartAt I α).symm (extChartAt I α b))‖) := by
    have h_chain : ‖iteratedFDeriv ℝ 2 (fun y : E => c y (F y)) x‖ ≤
        K_total * (N2 + N1 + N0) := by
      refine le_trans h_leibniz_global ?_
      linarith [h_sum_bound, h_total_factor]
    rw [h_F_at_x] at h_chain
    exact h_chain
  exact h_combined

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.inputSlot_correction_iteratedFDeriv_two_bound
#print axioms
  DifferentialGeometry.Integral.Connection.outputSlot_correction_iteratedFDeriv_two_bound
end Sanity
