import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula

/-!
# Bound on the Fréchet derivative of the chart-pulled representation of
`covApply ∇ B T`

Combining the intrinsic-piece Fréchet-derivative bound with the input/output
Christoffel slot-correction Fréchet-derivative bounds, we obtain a uniform
bound on the operator norm of the Fréchet derivative of the chart-pulled
representation of `covApply ∇ B T` at chart-coordinate points whose preimage
lies in the partition-of-unity tsupport intersected with the chart-`α`
Levi-Civita good set.

Concretely, for a smooth Riemannian manifold `(M, g)`, a chart-centre
`α : M`, ranks `r, s : ℕ`, a smooth tangent vector field `B`, and a smooth
compactly supported `(r, s)`-tensor section `T`, there is a constant
`K ≥ 0` (depending on `g`, the chart at `α`, the locality hypothesis on the
chart atlas, the ranks `r`, `s`, and `B`, but independent of `T` and `b`)
such that for any `b ∈ tsupport (POU α) ∩ chartLeviCivitaGoodSet α` and any
hypothesis `hF2_diff` that the chart-pulled representation `repr T ∘ symm`
is differentiable in its Fréchet derivative at `extChartAt I α b`, the
operator norm of the Fréchet derivative of the chart-pulled representation
of `covApply ∇ B T` at `extChartAt I α b` is bounded by

```
K * (‖repr T b‖
     + ‖fderiv ℝ (repr T ∘ symm) (extChartAt I α b)‖
     + ‖iteratedFDeriv ℝ 2 (repr T ∘ symm) (extChartAt I α b)‖)
```

## Strategy

1. The chart-pulled formula
   `chart_pulled_covApply_explicit_formula_target_smoothCc` expresses
   `repr (covApply ∇ B T) ∘ symm y` as the sum of an intrinsic
   Fréchet-derivative piece, a finite sum of input-slot Christoffel
   corrections, minus a finite sum of output-slot Christoffel corrections,
   at every point `y` of the chart target image of the Levi-Civita good set.

2. This holds on an open neighbourhood of `extChartAt I α b` whenever
   `b ∈ chartLeviCivitaGoodSet α`. We use `Filter.EventuallyEq.fderiv_eq` to
   rewrite the LHS's Fréchet derivative as the Fréchet derivative of the
   three-piece sum.

3. We distribute the Fréchet derivative across `+`, `-`, and finite sums via
   `fderiv_add`, `fderiv_sub`, `fderiv_fun_sum`. This requires each piece to
   be differentiable at the chart point.

4. The intrinsic piece's differentiability follows from
   `DifferentiableAt.clm_apply` applied to `fderiv (repr T ∘ symm)` (whose
   differentiability is `hF2_diff`) and the chart-pulled `B` representation
   (smooth on the chart-target image of the good set).

5. Each slot-correction piece's differentiability follows from
   `Filter.EventuallyEq.differentiableAt_iff` against the kernel-form
   factorisation, then `DifferentiableAt.clm_apply` for the kernel form.

6. The bounds on each summand come from `intrinsic_piece_fderiv_bound`,
   `chart_pulled_input_slot_correction_fderiv_bound`,
   `chart_pulled_output_slot_correction_fderiv_bound`. Summing and absorbing
   the constants into `K := K_I + ∑ K_in + ∑ K_out` gives the headline.
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

/-! ## Smoothness of the chart-pulled tensor representation
on the chart-target image of the good set -/

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled tensor representation. Re-derived here to avoid relying on
a private helper. -/
private lemma reprT_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (T.toSection x)) :=
    T.toSection.contMDiff
  have hbase :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  have hcm_on_source :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        ((chartAt H α).source) := by
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x
        (T.toSection x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hcm_on_good :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)
        (chartLeviCivitaGoodSet (I := I) α) := by
    rw [h_good_eq_source]; exact hcm_on_source
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hx_good, rfl⟩
  set F : M → TensorRSModel r s ℝ E :=
    fun b : M => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => T.toSection y') b with hF_def
  have hF_at : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞ F x :=
    hcm_on_good.contMDiffAt (hgood_open.mem_nhds hx_good)
  set φ := extChartAt I α
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hxφ_src : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_on :
      ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_tgt
  have hF_at' : ContMDiffAt I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

/-- Smoothness of the chart-pulled `B`-representation on the chart-target
image of the good set. -/
private lemma uB_contDiffOn_goodSet
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  exact chartE_pullback_contDiffOn_goodSet (I := I) α hB_on

/-! ## Differentiability of each piece at `x = extChartAt I α b` -/

/-- Differentiability of the intrinsic Fréchet-derivative piece at the chart
point. -/
private lemma intrinsicPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hF2_diff : DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b)) :
    DifferentiableAt ℝ
      (fun y : E =>
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    uB_contDiffOn_goodSet (I := I) α B
  have hu_diff : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hu_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  exact hF2_diff.clm_apply hu_diff

/-- Differentiability of the chart-pulled input-slot Christoffel correction at
the chart point. -/
private lemma inputSlotPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ
      (fun y : E => tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    inputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B k hb_good
  have hK_diff : DifferentiableAt ℝ
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm y)) (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  have h_clm_diff : DifferentiableAt ℝ
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm y)
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y)))
      (extChartAt I α b) := hK_diff.clm_apply hR_diff
  have h_evt :
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
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    have h_factor :=
      chartTensorRSInputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := (extChartAt I α).symm y)
        (by rw [hx'_inv]; exact hx'_src) k
    exact h_factor
  exact (h_evt.differentiableAt_iff).mpr h_clm_diff

/-- Differentiability of the chart-pulled output-slot Christoffel correction
at the chart point. -/
private lemma outputSlotPiece_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ
      (fun y : E => tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) (extChartAt I α b) hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    outputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B l hb_good
  have hK_diff : DifferentiableAt ℝ
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm y)) (extChartAt I α b) := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h; exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  have h_clm_diff : DifferentiableAt ℝ
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm y)
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y)))
      (extChartAt I α b) := hK_diff.clm_apply hR_diff
  have h_evt :
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
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
    refine Filter.eventually_of_mem (hU_open.mem_nhds hx_mem) ?_
    intro y hy
    rcases hy with ⟨x', hx'_good, hx'y⟩
    have hx'_src : x' ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hx'_extsrc : x' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hx'_src
    have hx'_inv : (extChartAt I α).symm y = x' := by
      rw [← hx'y]; exact (extChartAt I α).left_inv hx'_extsrc
    have h_factor :=
      chartTensorRSOutputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := (extChartAt I α).symm y)
        (by rw [hx'_inv]; exact hx'_src) l
    exact h_factor
  exact (h_evt.differentiableAt_iff).mpr h_clm_diff

/-! ## Pointwise eventual equality from the chart-pulled explicit formula -/

/-- The chart-pulled representation of `covApply ∇ B T` is, on an open
neighbourhood of `extChartAt I α b`, equal to the intrinsic piece plus
input-slot Christoffel corrections minus output-slot Christoffel
corrections. -/
private lemma chart_pulled_covApply_repr_eventuallyEq
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

/-- **Bound on the Fréchet derivative of the chart-pulled representation of
the first covariant derivative applied to a tangent vector field.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a smooth tangent vector field `B`, a smooth compactly supported
`(r, s)`-tensor section `T`, and a chart-`α` partition-of-unity tsupport
point `b` lying in the chart-`α` Levi-Civita good set, the operator norm of
the Fréchet derivative of the chart-pulled representation
`tensorRSChartE_section_repr r s α (covApply ∇ B T) ∘ (extChartAt I α).symm`
at `extChartAt I α b` is bounded by

```
K * (‖tensorRSChartE_section_repr r s α T.toSection b‖
     + ‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
            (extChartAt I α b)‖
     + ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
            (extChartAt I α b)‖)
```

The constant `K` depends only on `h_atlas`, `g`, `α`, `r`, `s`, and `B`. The
differentiability hypothesis on the Fréchet derivative of the chart-pulled
representation is genuine — it expresses that
`tensorRSChartE_section_repr r s α T.toSection ∘ (extChartAt I α).symm` is
twice Fréchet-differentiable at the chart point, which the caller discharges
from smoothness of `T`. -/
theorem chart_pulled_covApply_repr_fderiv_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        DifferentiableAt ℝ
          (fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
              (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
          (extChartAt I α b) →
        ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) B.toFun
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤
        K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
             ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                  (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
               (extChartAt I α b)‖ +
             ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
                  (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
               (extChartAt I α b)‖) := by
  classical
  obtain ⟨K_I, hKI_nn, hKI_bound⟩ :=
    intrinsic_piece_fderiv_bound (I := I) (M := M) g r s α B
  have h_in_choose : ∀ k : Fin r, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
          (fun y : E =>
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm y)
              (chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) k))
          (extChartAt I α b)‖ ≤
        K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') b‖ +
             ‖fderiv ℝ
               (tensorRSChartE_section_repr (I := I) r s α
                  (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
               (extChartAt I α b)‖) := fun k =>
    chart_pulled_input_slot_correction_fderiv_bound
      (I := I) (M := M) h_atlas g r s α B k
  choose K_in hKin_nn hKin_bound using h_in_choose
  have h_out_choose : ∀ l : Fin s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
          (fun y : E =>
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm y)
              (chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun y' : M => T.toSection y') B.toFun
                ((extChartAt I α).symm y) l))
          (extChartAt I α b)‖ ≤
        K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') b‖ +
             ‖fderiv ℝ
               (tensorRSChartE_section_repr (I := I) r s α
                  (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
               (extChartAt I α b)‖) := fun l =>
    chart_pulled_output_slot_correction_fderiv_bound
      (I := I) (M := M) h_atlas g r s α B l
  choose K_out hKout_nn hKout_bound using h_out_choose
  refine ⟨K_I + (∑ k : Fin r, K_in k) + (∑ l : Fin s, K_out l), ?_, ?_⟩
  · have h2 : 0 ≤ ∑ k : Fin r, K_in k :=
      Finset.sum_nonneg (fun k _ => hKin_nn k)
    have h3 : 0 ≤ ∑ l : Fin s, K_out l :=
      Finset.sum_nonneg (fun l _ => hKout_nn l)
    linarith
  intro T b hb hF2_diff
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Eventually equal to the 3-piece sum.
  have h_evt :=
    chart_pulled_covApply_repr_eventuallyEq
      (I := I) (M := M) g r s α T B hb_good
  rw [Filter.EventuallyEq.fderiv_eq h_evt]
  -- Differentiability of each piece at `x`.
  have h_intr_diff :=
    intrinsicPiece_differentiableAt (I := I) (M := M) g r s α T B hb_good hF2_diff
  have h_in_diff : ∀ k : Fin r, DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) (extChartAt I α b) := fun k =>
    inputSlotPiece_differentiableAt (I := I) (M := M) g r s α T B k hb_good
  have h_out_diff : ∀ l : Fin s, DifferentiableAt ℝ
      (fun y : E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) (extChartAt I α b) := fun l =>
    outputSlotPiece_differentiableAt (I := I) (M := M) g r s α T B l hb_good
  have h_in_sum_diff : DifferentiableAt ℝ
      (fun y : E => ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k)) (extChartAt I α b) :=
    DifferentiableAt.fun_sum (fun k _ => h_in_diff k)
  have h_out_sum_diff : DifferentiableAt ℝ
      (fun y : E => ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) (extChartAt I α b) :=
    DifferentiableAt.fun_sum (fun l _ => h_out_diff l)
  -- Use HasFDerivAt to compute the fderiv of the 3-piece sum.
  have h_in_sum_at :=
    HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin r)))
      (fun k _ => (h_in_diff k).hasFDerivAt)
  have h_out_sum_at :=
    HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin s)))
      (fun l _ => (h_out_diff l).hasFDerivAt)
  have h_total :=
    (h_intr_diff.hasFDerivAt.add h_in_sum_at).sub h_out_sum_at
  -- `h_total.fderiv` has form `fderiv ℝ ((f + g) - h) x = ...` with function-level
  -- arithmetic. Convert the goal's pointwise form to function form via `Pi`.
  have h_pi : (fun y : E =>
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y))) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l)) =
      (((fun y : E => fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))) +
      (fun y : E => ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) k))) -
      (fun y : E => ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y)
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y' : M => T.toSection y') B.toFun
            ((extChartAt I α).symm y) l))) := rfl
  rw [h_pi, h_total.fderiv]
  -- Bounds from sub-lemmas.
  have h_intr_bound := hKI_bound T hb hF2_diff
  have h_in_bound_pt : ∀ k : Fin r, _ ≤ K_in k * _ := fun k =>
    hKin_bound k T hb
  have h_out_bound_pt : ∀ l : Fin s, _ ≤ K_out l * _ := fun l =>
    hKout_bound l T hb
  -- Abbreviations.
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ with hV_def
  set F : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hF_def
  set I2 : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ F := norm_nonneg _
  have hI2_nn : 0 ≤ I2 := norm_nonneg _
  -- Triangle inequalities.
  have h_norm_sub :
      ‖fderiv ℝ (fun y : E =>
            fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)
        + ∑ k : Fin r,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b)
        - ∑ l : Fin s,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b)‖
      ≤ ‖fderiv ℝ (fun y : E =>
            fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)‖
        + ∑ k : Fin r,
            ‖fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b)‖
        + ∑ l : Fin s,
            ‖fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b)‖ := by
    have h1 := norm_sub_le
      (fderiv ℝ (fun y : E =>
            fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)
        + ∑ k : Fin r,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b))
      (∑ l : Fin s,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b))
    have h2 := norm_add_le
      (fderiv ℝ (fun y : E =>
            fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b))
      (∑ k : Fin r,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b))
    have h3 := norm_sum_le
      (Finset.univ : Finset (Fin r))
      (fun k => fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b))
    have h4 := norm_sum_le
      (Finset.univ : Finset (Fin s))
      (fun l => fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b))
    linarith
  -- Combine norm-by-piece bounds.
  have h_in_sum_bound :
      (∑ k : Fin r, ‖fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b)‖)
        ≤ (∑ k : Fin r, K_in k) * (V + F) := by
    calc ∑ k : Fin r, _
        ≤ ∑ k : Fin r, K_in k * (V + F) :=
          Finset.sum_le_sum (fun k _ => h_in_bound_pt k)
      _ = (∑ k : Fin r, K_in k) * (V + F) := by rw [Finset.sum_mul]
  have h_out_sum_bound :
      (∑ l : Fin s, ‖fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b)‖)
        ≤ (∑ l : Fin s, K_out l) * (V + F) := by
    calc ∑ l : Fin s, _
        ≤ ∑ l : Fin s, K_out l * (V + F) :=
          Finset.sum_le_sum (fun l _ => h_out_bound_pt l)
      _ = (∑ l : Fin s, K_out l) * (V + F) := by rw [Finset.sum_mul]
  have hKin_sum_nn : 0 ≤ ∑ k : Fin r, K_in k :=
    Finset.sum_nonneg (fun k _ => hKin_nn k)
  have hKout_sum_nn : 0 ≤ ∑ l : Fin s, K_out l :=
    Finset.sum_nonneg (fun l _ => hKout_nn l)
  have h_VF_le_VFI2 : V + F ≤ V + F + I2 := by linarith
  have h_I2F_le_VFI2 : I2 + F ≤ V + F + I2 := by linarith
  have h_intr_final : K_I * (I2 + F) ≤ K_I * (V + F + I2) :=
    mul_le_mul_of_nonneg_left h_I2F_le_VFI2 hKI_nn
  have h_in_final : (∑ k : Fin r, K_in k) * (V + F) ≤
      (∑ k : Fin r, K_in k) * (V + F + I2) :=
    mul_le_mul_of_nonneg_left h_VF_le_VFI2 hKin_sum_nn
  have h_out_final : (∑ l : Fin s, K_out l) * (V + F) ≤
      (∑ l : Fin s, K_out l) * (V + F + I2) :=
    mul_le_mul_of_nonneg_left h_VF_le_VFI2 hKout_sum_nn
  -- Putting it all together.
  -- `‖A + ∑I - ∑O‖ ≤ ‖A‖ + ∑‖I‖ + ∑‖O‖
  --              ≤ K_I·(I2+F) + (∑K_in)·(V+F) + (∑K_out)·(V+F)
  --              ≤ (K_I + ∑K_in + ∑K_out)·(V+F+I2)`.
  calc ‖fderiv ℝ (fun y : E =>
            fderiv ℝ
              (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)
        + ∑ k : Fin r,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) k)) (extChartAt I α b)
        - ∑ l : Fin s,
            fderiv ℝ (fun y : E =>
              (trivializationAt (TensorRSModel r s ℝ E)
                  (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y)
                (chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun y' : M => T.toSection y') B.toFun
                  ((extChartAt I α).symm y) l)) (extChartAt I α b)‖
      ≤ _ := h_norm_sub
    _ ≤ K_I * (I2 + F) +
        (∑ k : Fin r, K_in k) * (V + F) +
        (∑ l : Fin s, K_out l) * (V + F) := by
          have h_in_sum_bound' := h_in_sum_bound
          have h_out_sum_bound' := h_out_sum_bound
          have h_intr_bound' := h_intr_bound
          linarith
    _ ≤ K_I * (V + F + I2) +
        (∑ k : Fin r, K_in k) * (V + F + I2) +
        (∑ l : Fin s, K_out l) * (V + F + I2) := by linarith
    _ = (K_I + (∑ k : Fin r, K_in k) + (∑ l : Fin s, K_out l)) *
          (V + F + I2) := by ring

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_covApply_repr_fderiv_bound
end Sanity
