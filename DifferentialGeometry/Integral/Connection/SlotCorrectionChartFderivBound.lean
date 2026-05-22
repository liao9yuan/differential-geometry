import DifferentialGeometry.Integral.Connection.SlotCorrectionChartKernel
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound

/-!
# Bound on the Fréchet derivative of the chart-pulled input/output Christoffel
slot corrections

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r s : ℕ`, a smooth tangent vector field `B`, an input slot `k : Fin r`
(resp. output slot `l : Fin s`), and a smooth compactly supported
`(r, s)`-tensor section `T`, the chart-`α`-trivialised input-slot
Christoffel correction factors through a `T`-linear chart kernel:

```
(triv α).cLMA b (chartTensorRSInputSlotCorrection r s g α T B b k)
    = inputSlotChartKernel g r s α B k b
        (tensorRSChartE_section_repr r s α T b)
```

(and the analogous identity for the output slot). Differentiating in the
chart variable `y` and applying `fderiv_clm_apply` to the kernel-CLM action
gives

```
fderiv (y ↦ (kernel y) (R y)) x
    = (kernel x).comp (fderiv R x) + (fderiv kernel x).flip (R x)
```

whose operator norm is bounded by

```
‖kernel x‖ · ‖fderiv R x‖ + ‖fderiv kernel x‖ · ‖R x‖
```

Both `‖kernel x‖` and `‖fderiv kernel x‖` admit uniform bounds on the
intersection of the partition-of-unity tsupport with the chart-`α`
Levi-Civita good set, supplied by the kernel infrastructure. Choosing the
maximum gives the headline.

## Main results

* `chart_pulled_input_slot_correction_fderiv_bound` — uniform bound on the
  Fréchet derivative of the chart-pulled input-slot Christoffel correction.
* `chart_pulled_output_slot_correction_fderiv_bound` — analogous uniform
  bound for the output slot. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

/-! ## Step 1: smoothness of `R(y) = (tensorRSChartE_section_repr r s α T ∘ symm) y`
on the chart-target image of the chart-`α` Levi-Civita good set -/

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled tensor representation
`tensorRSChartE_section_repr r s α T ∘ (extChartAt I α).symm`. -/
lemma R_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  -- `tensorRSChartE_section_repr r s α T.toSection` is smooth on the chart
  -- source as a function `M → TensorRSModel r s ℝ E`, by
  -- `Trivialization.contMDiffOn_section_baseSet_iff` applied to the smoothness
  -- of `T.toSection` (which is `(T.toSection).contMDiff`).
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
  -- Transfer to chart-target image via composition with `extChartAt I α .symm`.
  -- This is the standard `chartE_pullback`-style pattern.
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
  -- Now compose with `extChartAt I α .symm`.
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

/-! ## Step 2: chart-pulled equality of the slot correction and the kernel
factorisation, transferred to an `fderiv` equality through
`Filter.EventuallyEq.fderiv_eq`. -/

/-- Pointwise equality between the chart-pulled input-slot correction and the
chart-kernel applied to `tensorRSChartE_section_repr`, on a neighbourhood of
the chart target image of a point `b ∈ chartLeviCivitaGoodSet α`. -/
private lemma input_slot_pulled_eq_kernel_eventually
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
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
  classical
  -- It suffices to check pointwise equality on the open neighbourhood
  -- `(extChartAt I α) '' chartLeviCivitaGoodSet α` of `extChartAt I α b`.
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
  -- `(extChartAt I α).symm y = x` since y = (extChartAt I α) x and x ∈ source.
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx_good
  have hx_extsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hx_inv : (extChartAt I α).symm y = x := by
    rw [← hxy]; exact (extChartAt I α).left_inv hx_extsrc
  -- Apply the kernel factorisation at `(symm y) = x ∈ chartSource`.
  have h_factor :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun b' : M => T.toSection b') B.toFun
      (b := (extChartAt I α).symm y)
      (by rw [hx_inv]; exact hx_src) k
  -- LHS = (triv).cLMA (symm y) (slot correction)
  --     = kernel(symm y) (triv (T (symm y)))
  --     = kernel(symm y) (repr T (symm y)).
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

/-- Pointwise equality between the chart-pulled output-slot correction and the
chart-kernel applied to `tensorRSChartE_section_repr`, on a neighbourhood of
the chart target image of a point `b ∈ chartLeviCivitaGoodSet α`. -/
private lemma output_slot_pulled_eq_kernel_eventually
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
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ((extChartAt I α).symm y))) := by
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

/-! ## Headline: input slot bound -/

/-- **Bound on the Fréchet derivative of the chart-pulled input-slot
Christoffel correction.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, a smooth
tangent vector field `B`, ranks `r, s : ℕ`, and an input-slot index
`k : Fin r`, there is a constant `K ≥ 0` (depending on the locality
hypothesis on the chart atlas, the metric `g`, the chart-`α`, the ranks
`r`, `s`, the slot index `k`, and `B`, but independent of `T` and `b`)
such that for any smooth compactly supported `(r, s)`-tensor section
`T` and any `b` in the intersection of the chart-`α` partition-of-unity
tsupport and the chart-`α` Levi-Civita good set, the operator norm of the
Fréchet derivative of the chart-pulled input-slot Christoffel correction is
bounded by

```
K * (‖tensorRSChartE_section_repr r s α T.toSection b‖
     + ‖fderiv (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
            (extChartAt I α b)‖)
```
-/
theorem chart_pulled_input_slot_correction_fderiv_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
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
               (extChartAt I α b)‖) := by
  classical
  -- Uniform op-norm and fderiv bounds for the kernel.
  obtain ⟨K_op, hKop_nn, hKop_bound⟩ :=
    inputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B k
  obtain ⟨K_d, hKd_nn, hKd_bound⟩ :=
    inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B k
  refine ⟨max K_op K_d, le_trans hKop_nn (le_max_left _ _), ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Abbreviations.
  set R : E → TensorRSModel r s ℝ E :=
    fun y : E => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => T.toSection y') ((extChartAt I α).symm y) with hR_def
  set K_chart : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) :=
    fun y : E =>
      inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm y) with hKchart_def
  set x : E := extChartAt I α b with hx_def
  -- Step 1: rewrite via `EventuallyEq.fderiv_eq`.
  have h_evt :
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) k)) =ᶠ[𝓝 x]
        (fun y : E => K_chart y (R y)) :=
    input_slot_pulled_eq_kernel_eventually (I := I) (M := M)
      g r s α T B k hb_good
  rw [Filter.EventuallyEq.fderiv_eq h_evt]
  -- Step 2: differentiability of `K_chart` and `R` at `x`.
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      x ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞ R
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ R x := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h
      exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) x hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    inputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B k hb_good
  have hK_diff : DifferentiableAt ℝ K_chart x := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h
      exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  -- Step 3: apply `fderiv_clm_apply`.
  have h_clm :
      fderiv ℝ (fun y : E => K_chart y (R y)) x =
        (K_chart x).comp (fderiv ℝ R x) + (fderiv ℝ K_chart x).flip (R x) :=
    fderiv_clm_apply hK_diff hR_diff
  -- Step 4: norm bound from `fderiv_clm_apply` formula.
  have h_norm_le :
      ‖fderiv ℝ (fun y : E => K_chart y (R y)) x‖ ≤
        ‖K_chart x‖ * ‖fderiv ℝ R x‖ +
          ‖fderiv ℝ K_chart x‖ * ‖R x‖ := by
    rw [h_clm]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(K_chart x).comp (fderiv ℝ R x)‖ ≤
        ‖K_chart x‖ * ‖fderiv ℝ R x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖(fderiv ℝ K_chart x).flip (R x)‖ ≤
        ‖fderiv ℝ K_chart x‖ * ‖R x‖ := by
      have h2a : ‖(fderiv ℝ K_chart x).flip (R x)‖ ≤
          ‖(fderiv ℝ K_chart x).flip‖ * ‖R x‖ :=
        ContinuousLinearMap.le_opNorm _ (R x)
      rw [ContinuousLinearMap.opNorm_flip] at h2a
      exact h2a
    linarith
  -- Step 5: uniform constants. Note `K_chart x` corresponds to the kernel at
  -- `(extChartAt I α).symm x = b`.
  have hsymm_x : (extChartAt I α).symm x = b := by
    rw [hx_def]
    have hb_chart : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact (extChartAt I α).left_inv hb_extsrc
  have hK_chart_at_x :
      K_chart x =
        inputSlotChartKernel (I := I) g r s α B.toFun k b := by
    change inputSlotChartKernel (I := I) g r s α B.toFun k
        ((extChartAt I α).symm x) =
      inputSlotChartKernel (I := I) g r s α B.toFun k b
    rw [hsymm_x]
  have hKop_x : ‖K_chart x‖ ≤ K_op := by
    rw [hK_chart_at_x]
    exact hKop_bound hb
  have hKd_x :
      ‖fderiv ℝ K_chart x‖ ≤ K_d := by
    change ‖fderiv ℝ
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K_d
    exact hKd_bound hb
  -- Identify `R x = repr T b`.
  have hR_at_x :
      R x = tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b := by
    change tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm x) =
      tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b
    rw [hsymm_x]
  -- Step 6: combine. Let K := max K_op K_d.
  set K_total : ℝ := max K_op K_d with hKtotal_def
  have hKop_le : K_op ≤ K_total := le_max_left _ _
  have hKd_le : K_d ≤ K_total := le_max_right _ _
  have hKtotal_nn : 0 ≤ K_total := le_trans hKop_nn hKop_le
  -- We have:
  --   ‖K_chart x‖ * ‖fderiv R x‖ ≤ K_op * ‖fderiv R x‖ ≤ K_total * ‖fderiv R x‖
  --   ‖fderiv K_chart x‖ * ‖R x‖ ≤ K_d * ‖R x‖ ≤ K_total * ‖R x‖
  -- Sum is `≤ K_total * (‖R x‖ + ‖fderiv R x‖)`.
  set N_R : ℝ := ‖R x‖ with hN_R_def
  set N_dR : ℝ := ‖fderiv ℝ R x‖ with hN_dR_def
  have hN_R_nn : 0 ≤ N_R := norm_nonneg _
  have hN_dR_nn : 0 ≤ N_dR := norm_nonneg _
  have h_bound1 : ‖K_chart x‖ * N_dR ≤ K_total * N_dR := by
    refine mul_le_mul_of_nonneg_right ?_ hN_dR_nn
    exact le_trans hKop_x hKop_le
  have h_bound2 : ‖fderiv ℝ K_chart x‖ * N_R ≤ K_total * N_R := by
    refine mul_le_mul_of_nonneg_right ?_ hN_R_nn
    exact le_trans hKd_x hKd_le
  have h_combine :
      ‖K_chart x‖ * N_dR + ‖fderiv ℝ K_chart x‖ * N_R ≤
        K_total * N_dR + K_total * N_R := by
    linarith
  have h_factor : K_total * N_dR + K_total * N_R =
      K_total * (N_R + N_dR) := by ring
  have h_final :
      ‖fderiv ℝ (fun y : E => K_chart y (R y)) x‖ ≤
        K_total * (N_R + N_dR) := by
    refine le_trans h_norm_le ?_
    rw [show ‖K_chart x‖ * ‖fderiv ℝ R x‖ +
        ‖fderiv ℝ K_chart x‖ * ‖R x‖ =
        ‖K_chart x‖ * N_dR + ‖fderiv ℝ K_chart x‖ * N_R from rfl]
    rw [← h_factor]; exact h_combine
  -- Rewrite `N_R` and `N_dR` into the headline RHS shape via `hR_at_x`.
  have hN_R_rw : N_R = ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b‖ := by
    rw [hN_R_def, hR_at_x]
  have hN_dR_rw : N_dR =
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
    change ‖fderiv ℝ
        (fun y : E => tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
        (extChartAt I α b)‖ =
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖
    rfl
  rw [hN_R_rw, hN_dR_rw] at h_final
  exact h_final

/-! ## Headline: output slot bound -/

/-- **Bound on the Fréchet derivative of the chart-pulled output-slot
Christoffel correction.**

Analogue of `chart_pulled_input_slot_correction_fderiv_bound` with the
output-slot kernel. -/
theorem chart_pulled_output_slot_correction_fderiv_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
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
               (extChartAt I α b)‖) := by
  classical
  obtain ⟨K_op, hKop_nn, hKop_bound⟩ :=
    outputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B l
  obtain ⟨K_d, hKd_nn, hKd_bound⟩ :=
    outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) g r s α B l
  refine ⟨max K_op K_d, le_trans hKop_nn (le_max_left _ _), ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  set R : E → TensorRSModel r s ℝ E :=
    fun y : E => tensorRSChartE_section_repr (I := I) r s α
      (fun y' : M => T.toSection y') ((extChartAt I α).symm y) with hR_def
  set K_chart : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) :=
    fun y : E =>
      outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm y) with hKchart_def
  set x : E := extChartAt I α b with hx_def
  -- Step 1: `EventuallyEq.fderiv_eq`.
  have h_evt :
      (fun y : E =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun y' : M => T.toSection y') B.toFun
              ((extChartAt I α).symm y) l)) =ᶠ[𝓝 x]
        (fun y : E => K_chart y (R y)) :=
    output_slot_pulled_eq_kernel_eventually (I := I) (M := M)
      g r s α T B l hb_good
  rw [Filter.EventuallyEq.fderiv_eq h_evt]
  -- Step 2: differentiability of `K_chart` and `R` at `x`.
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      x ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hR_cd : ContDiffOn ℝ ∞ R
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hR_diff : DifferentiableAt ℝ R x := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h
      exact absurd h (by simp)
    exact ((hR_cd.differentiableOn hne) x hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have hK_at :=
    outputSlotChartKernel_contDiffAt_chart_pulled
      (I := I) (M := M) g r s α B l hb_good
  have hK_diff : DifferentiableAt ℝ K_chart x := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h
      exact absurd h (by simp)
    exact hK_at.differentiableAt hne
  -- Step 3: apply `fderiv_clm_apply`.
  have h_clm :
      fderiv ℝ (fun y : E => K_chart y (R y)) x =
        (K_chart x).comp (fderiv ℝ R x) + (fderiv ℝ K_chart x).flip (R x) :=
    fderiv_clm_apply hK_diff hR_diff
  -- Step 4: norm bound.
  have h_norm_le :
      ‖fderiv ℝ (fun y : E => K_chart y (R y)) x‖ ≤
        ‖K_chart x‖ * ‖fderiv ℝ R x‖ +
          ‖fderiv ℝ K_chart x‖ * ‖R x‖ := by
    rw [h_clm]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(K_chart x).comp (fderiv ℝ R x)‖ ≤
        ‖K_chart x‖ * ‖fderiv ℝ R x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖(fderiv ℝ K_chart x).flip (R x)‖ ≤
        ‖fderiv ℝ K_chart x‖ * ‖R x‖ := by
      have h2a : ‖(fderiv ℝ K_chart x).flip (R x)‖ ≤
          ‖(fderiv ℝ K_chart x).flip‖ * ‖R x‖ :=
        ContinuousLinearMap.le_opNorm _ (R x)
      rw [ContinuousLinearMap.opNorm_flip] at h2a
      exact h2a
    linarith
  -- Step 5: uniform constants.
  have hsymm_x : (extChartAt I α).symm x = b := by
    rw [hx_def]
    have hb_chart : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hb_chart
    exact (extChartAt I α).left_inv hb_extsrc
  have hK_chart_at_x :
      K_chart x =
        outputSlotChartKernel (I := I) g r s α B.toFun l b := by
    change outputSlotChartKernel (I := I) g r s α B.toFun l
        ((extChartAt I α).symm x) =
      outputSlotChartKernel (I := I) g r s α B.toFun l b
    rw [hsymm_x]
  have hKop_x : ‖K_chart x‖ ≤ K_op := by
    rw [hK_chart_at_x]
    exact hKop_bound hb
  have hKd_x :
      ‖fderiv ℝ K_chart x‖ ≤ K_d := by
    change ‖fderiv ℝ
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
          ((extChartAt I α).symm y)) (extChartAt I α b)‖ ≤ K_d
    exact hKd_bound hb
  have hR_at_x :
      R x = tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b := by
    change tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') ((extChartAt I α).symm x) =
      tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b
    rw [hsymm_x]
  -- Step 6: combine.
  set K_total : ℝ := max K_op K_d with hKtotal_def
  have hKop_le : K_op ≤ K_total := le_max_left _ _
  have hKd_le : K_d ≤ K_total := le_max_right _ _
  have hKtotal_nn : 0 ≤ K_total := le_trans hKop_nn hKop_le
  set N_R : ℝ := ‖R x‖ with hN_R_def
  set N_dR : ℝ := ‖fderiv ℝ R x‖ with hN_dR_def
  have hN_R_nn : 0 ≤ N_R := norm_nonneg _
  have hN_dR_nn : 0 ≤ N_dR := norm_nonneg _
  have h_bound1 : ‖K_chart x‖ * N_dR ≤ K_total * N_dR := by
    refine mul_le_mul_of_nonneg_right ?_ hN_dR_nn
    exact le_trans hKop_x hKop_le
  have h_bound2 : ‖fderiv ℝ K_chart x‖ * N_R ≤ K_total * N_R := by
    refine mul_le_mul_of_nonneg_right ?_ hN_R_nn
    exact le_trans hKd_x hKd_le
  have h_combine :
      ‖K_chart x‖ * N_dR + ‖fderiv ℝ K_chart x‖ * N_R ≤
        K_total * N_dR + K_total * N_R := by
    linarith
  have h_factor : K_total * N_dR + K_total * N_R =
      K_total * (N_R + N_dR) := by ring
  have h_final :
      ‖fderiv ℝ (fun y : E => K_chart y (R y)) x‖ ≤
        K_total * (N_R + N_dR) := by
    refine le_trans h_norm_le ?_
    rw [show ‖K_chart x‖ * ‖fderiv ℝ R x‖ +
        ‖fderiv ℝ K_chart x‖ * ‖R x‖ =
        ‖K_chart x‖ * N_dR + ‖fderiv ℝ K_chart x‖ * N_R from rfl]
    rw [← h_factor]; exact h_combine
  have hN_R_rw : N_R = ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y' : M => T.toSection y') b‖ := by
    rw [hN_R_def, hR_at_x]
  have hN_dR_rw : N_dR =
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
    change ‖fderiv ℝ
        (fun y : E => tensorRSChartE_section_repr (I := I) r s α
          (fun y' : M => T.toSection y') ((extChartAt I α).symm y))
        (extChartAt I α b)‖ =
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖
    rfl
  rw [hN_R_rw, hN_dR_rw] at h_final
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_input_slot_correction_fderiv_bound
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_output_slot_correction_fderiv_bound
end Sanity
