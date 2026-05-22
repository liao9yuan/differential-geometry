import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartKernel
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.ChartPulledRawTensorReprFactorization

/-!
# Pointwise norm bound on the chart-pulled value of the nested chart-frame
covariant derivative of a smooth compactly supported tensor section

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a chart-frame index `i : Fin (Module.finrank ℝ E)`, and a smooth
compactly supported `(r, s)`-tensor section `T`, the value of the chart-`α`
trivialised representation of the *nested* chart-frame covariant derivative

  `b ↦ tensorRSChartE_section_repr r s α (covApply ∇ B (covApply ∇ B T)) b`,

where `B := chartFrameNormGlobalSmooth g α i` is the globally smooth
chart-`α` chart-frame Gram-Schmidt section, is bounded pointwise on the
intersection of the chart-`α` partition-of-unity tsupport with the chart-`α`
Levi-Civita good set by the chart-pulled iterated-Fréchet-derivative data of
`T` up to order `2`.

The pointwise bound, in squared form, reads

```
‖tensorRSChartE_section_repr r s α
    (fun y => (covApply ∇ B (covApply ∇ B T)) y) b‖ ^ 2 ≤
  K *
    (∑ j : Fin 3,
      ‖iteratedFDeriv ℝ j.val
          (tensorRSChartE_section_repr r s α (fun y => T.toSection y) ∘
            (extChartAt I α).symm)
          (extChartAt I α b)‖ ^ 2)
```

with `K ≥ 0` depending only on `h_atlas`, `g`, the chart
at `α`, the ranks `r`, `s`, and the chart-frame index `i`. The constant is
*independent* of `T` and `b`.

This headline is the order-0 (i.e., value, not Fréchet derivative) analogue
of the chart-pulled-nested-covApply Fréchet-derivative bound that follows
from iterating the order-1 covApply Fréchet-derivative bound (Sub-E,
`chart_pulled_covApply_repr_fderiv_bound`). The Fréchet-derivative variant
also requires an order-2 iterated-Fréchet-derivative bound on the
chart-pulled `repr (covApply ∇ B T) ∘ symm`, which is not yet developed in
this codebase; that order-2 bound will be needed downstream and is left as a
separate obligation.

## Strategy

The chart-pulled explicit formula
`chart_pulled_covApply_explicit_formula` applied to the smooth section
`σ := covApply ∇ B T` gives, at every chart-`α` Levi-Civita good-set
point `b`,

```
repr (covApply ∇ B σ) (b) =
  fderiv ℝ (repr σ ∘ symm) (extChartAt I α b) (trivToE α b (B b))
  + ∑ k : Fin r, triv.cLMA b (inputSlotCorrection r s g α σ B b k)
  - ∑ l : Fin s, triv.cLMA b (outputSlotCorrection r s g α σ B b l)
```

We pass to norms via the triangle inequality. The intrinsic Fréchet-derivative
piece's norm is bounded by

```
‖fderiv ℝ (repr σ ∘ symm) (extChartAt I α b)‖ · ‖trivToE α b (B b)‖
```

The first factor is bounded by `chart_pulled_covApply_repr_fderiv_bound`
(Sub-E) in terms of orders `0, 1, 2` of `repr T ∘ symm`. The second is
bounded by smoothness of `B`. The slot-correction pieces' norms are bounded
by op-norm uniform bounds on the slot kernels and norm bounds on
`repr σ` (the value of `covApply ∇ B T` at `b`), which itself is bounded by
orders `0, 1` of `repr T ∘ symm` via the chart-pulled explicit formula at `b`
applied to `T` together with uniform op-norm bounds. Adding the bounds and
squaring yields the squared headline.

The differentiability witness required by Sub-E (the differentiability of
`fderiv ℝ (repr T ∘ symm)` at `extChartAt I α b`) is discharged from
`ContDiffOn ℝ ∞` regularity of `repr T ∘ symm` on the chart-target image of
the good set, via `ContDiffWithinAt → ContDiffAt → DifferentiableAt`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Step 1: smoothness regularity of `repr T ∘ symm` and the
discharge of the `fderiv (repr T ∘ symm)` differentiability hypothesis -/

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled representation of a `SmoothCcTensor`. -/
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

/-- For any chart-`α` Levi-Civita good-set point `b`, the chart-pulled
representation `repr T ∘ symm` of `T : SmoothCcTensor g r s` is twice
Fréchet-differentiable at `extChartAt I α b`; in particular, the Fréchet
derivative `fderiv ℝ (repr T ∘ symm)` is itself differentiable there. -/
private lemma fderiv_reprT_differentiableAt_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
  classical
  have hU_open :
      IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem :
      extChartAt I α b ∈
        (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hcd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    reprT_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    hcd.fderiv_of_isOpen hU_open h_le
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by intro h; exact absurd h (by simp)
  have hwithin : DifferentiableWithinAt ℝ
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α)
      (extChartAt I α b) :=
    (hfd_cd.differentiableOn hne) (extChartAt I α b) hx_mem
  exact hwithin.differentiableAt (hU_open.mem_nhds hx_mem)

/-! ## Step 2: uniform bound on `‖B b‖` over the partition-of-unity tsupport
for `B := chartFrameNormGlobalSmooth g α i` -/

/-- For a globally smooth tangent vector section `B`, the chart-pulled
trivialised vector `trivToE α b (B b) = chartE_section_repr α B.toFun b` has
a uniform norm bound over the chart-`α` partition-of-unity tsupport. -/
private lemma trivToE_B_norm_bound
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖trivToE (I := I) α b (B.toFun b)‖ ≤ C := by
  classical
  -- Smoothness of B on the chart-α good set.
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  -- Smoothness of `b ↦ chartE_section_repr α B.toFun b` on the good set,
  -- which equals `b ↦ trivToE α b (B.toFun b)` by definition.
  have hu_cd_good : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => chartE_section_repr (I := I) α B.toFun b)
      (chartLeviCivitaGoodSet (I := I) α) :=
    chartE_section_repr_contMDiffOn_goodSet (I := I) (M := M) α hB_on
  -- The function is continuous on the good set.
  have hu_cont : ContinuousOn
      (fun b : M => trivToE (I := I) α b (B.toFun b))
      (chartLeviCivitaGoodSet (I := I) α) :=
    hu_cd_good.continuousOn
  -- POU tsupport is contained in the chart source = good set.
  have hPOU_subset_src : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hPOU_subset_good : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
    rw [h_good_eq_source]; exact hPOU_subset_src
  -- Compact POU tsupport.
  have hKcompact : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (isClosed_tsupport _).isCompact
  -- Apply bdd_above on a compact set with a continuous function (restricted
  -- to the POU tsupport via the inclusion).
  have hu_cont_K : ContinuousOn
      (fun b : M => trivToE (I := I) α b (B.toFun b))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    hu_cont.mono hPOU_subset_good
  obtain ⟨C, hC_bdd⟩ :=
    hKcompact.bddAbove_image (hu_cont_K.norm)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have h_in : ‖trivToE (I := I) α b (B.toFun b)‖ ∈
      (fun b => ‖trivToE (I := I) α b (B.toFun b)‖) '' tsupport _ :=
    ⟨b, hb, rfl⟩
  exact (hC_bdd h_in).trans (le_max_left _ _)

/-! ## Step 3: uniform bound on `‖repr (covApply ∇ B T) b‖` by orders 0, 1 of T

The chart-pulled value `repr (covApply ∇ B T)(b)` decomposes via the explicit
formula into an intrinsic piece (involving the fderiv of `repr T ∘ symm`) and
slot kernel pieces (involving `repr T(b)`). The intrinsic piece is bounded by
`‖fderiv (repr T ∘ symm) (extChartAt I α b)‖ * ‖trivToE α b (B b)‖`, and the
slot kernels are bounded by op-norm uniform bounds times `‖repr T(b)‖`.
-/

/-- Pointwise norm bound on the chart-pulled value of `covApply ∇ B T` at a
chart-`α` POU-tsupport + Levi-Civita good-set point. -/
private theorem chart_pulled_covApply_repr_value_bound_local
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) B.toFun
              (fun y : M => T.toSection y)) b‖ ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun y : M => T.toSection y) b‖ +
               ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := by
  classical
  -- General quantifier over input slots.
  have h_in_choose : ∀ k : Fin r, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K := fun k =>
    inputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B k
  choose K_in hK_in_nn hK_in_bound using h_in_choose
  have h_out_choose : ∀ l : Fin s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K := fun l =>
    outputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B l
  choose K_out hK_out_nn hK_out_bound using h_out_choose
  -- Constant for the trivToE B norm.
  obtain ⟨Cb, hCb_nn, hCb_bound⟩ := trivToE_B_norm_bound (I := I) (M := M) α B
  -- Choose `K := Cb + (∑ K_in) + (∑ K_out)` (independent of T and b).
  set Kin_sum : ℝ := ∑ k : Fin r, K_in k with hKin_sum_def
  set Kout_sum : ℝ := ∑ l : Fin s, K_out l with hKout_sum_def
  have hKin_sum_nn : 0 ≤ Kin_sum := Finset.sum_nonneg (fun k _ => hK_in_nn k)
  have hKout_sum_nn : 0 ≤ Kout_sum := Finset.sum_nonneg (fun l _ => hK_out_nn l)
  refine ⟨Cb + Kin_sum + Kout_sum, by linarith, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Apply the chart-pulled explicit formula at `b`.
  have h_formula :=
    chart_pulled_covApply_explicit_formula (I := I) (M := M)
      g r s α T.toSection B (b := b) hb_good
  -- Slot correction factorisation through the kernel.
  have h_in_factor : ∀ k : Fin r,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun y : M => T.toSection y) B.toFun b k) =
      inputSlotChartKernel (I := I) g r s α B.toFun k b
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b) := fun k =>
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun y : M => T.toSection y) B.toFun
      (b := b) (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good) k
  have h_out_factor : ∀ l : Fin s,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun y : M => T.toSection y) B.toFun b l) =
      outputSlotChartKernel (I := I) g r s α B.toFun l b
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b) := fun l =>
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α
      (fun y : M => T.toSection y) B.toFun
      (b := b) (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good) l
  -- Rewrite the formula's slot sums via the factorisations.
  -- Abbreviations.
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ with hV_def
  set F : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hF_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ F := norm_nonneg _
  -- Norm of the intrinsic Fréchet-derivative piece.
  have h_intr_norm :
      ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ ≤
        F * Cb := by
    have h1 : ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ ≤
        F * ‖trivToE (I := I) α b (B.toFun b)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖trivToE (I := I) α b (B.toFun b)‖ ≤ Cb := hCb_bound hb.1
    have h3 : F * ‖trivToE (I := I) α b (B.toFun b)‖ ≤ F * Cb :=
      mul_le_mul_of_nonneg_left h2 hF_nn
    exact le_trans h1 h3
  -- Norm of the input-slot correction pieces.
  have h_in_norm : ∀ k : Fin r,
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k)‖ ≤ K_in k * V := by
    intro k
    rw [h_in_factor k]
    have h1 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)‖ ≤
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * V :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K_in k :=
      hK_in_bound k hb
    have h3 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * V ≤
        K_in k * V :=
      mul_le_mul_of_nonneg_right h2 hV_nn
    linarith
  have h_out_norm : ∀ l : Fin s,
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l)‖ ≤ K_out l * V := by
    intro l
    rw [h_out_factor l]
    have h1 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) b)‖ ≤
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * V :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K_out l :=
      hK_out_bound l hb
    have h3 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * V ≤
        K_out l * V :=
      mul_le_mul_of_nonneg_right h2 hV_nn
    linarith
  -- Combine via the explicit-formula equality and the triangle inequality.
  -- Rewrite the LHS to align with `h_formula`. Both `T.toSection.toFun` and
  -- `fun y : M => T.toSection y` are the same map, but the `change` step is
  -- needed to canonicalise the form.
  change ‖tensorRSChartE_section_repr (I := I) r s α
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) B.toFun T.toSection.toFun) b‖ ≤ _
  rw [h_formula]
  have h_tri : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l)‖ ≤
      ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ +
      ∑ k : Fin r,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k)‖ +
      ∑ l : Fin s,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l)‖ := by
    have h1 := norm_sub_le
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
        ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun y : M => T.toSection y) B.toFun b k))
      (∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun y : M => T.toSection y) B.toFun b l))
    have h2 := norm_add_le
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)))
      (∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun y : M => T.toSection y) B.toFun b k))
    have h3 := norm_sum_le
      (Finset.univ : Finset (Fin r))
      (fun k => (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k))
    have h4 := norm_sum_le
      (Finset.univ : Finset (Fin s))
      (fun l => (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l))
    linarith
  -- Bound the sums via per-summand norm bounds.
  have h_in_sum : ∑ k : Fin r,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k)‖ ≤ Kin_sum * V := by
    calc ∑ k : Fin r, _
        ≤ ∑ k : Fin r, K_in k * V :=
          Finset.sum_le_sum (fun k _ => h_in_norm k)
      _ = (∑ k : Fin r, K_in k) * V := by rw [Finset.sum_mul]
      _ = Kin_sum * V := by rw [hKin_sum_def]
  have h_out_sum : ∑ l : Fin s,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l)‖ ≤ Kout_sum * V := by
    calc ∑ l : Fin s, _
        ≤ ∑ l : Fin s, K_out l * V :=
          Finset.sum_le_sum (fun l _ => h_out_norm l)
      _ = (∑ l : Fin s, K_out l) * V := by rw [Finset.sum_mul]
      _ = Kout_sum * V := by rw [hKout_sum_def]
  -- Final assembly.
  have h_VleVF : V ≤ V + F := by linarith
  have h_FCb_le : F * Cb ≤ Cb * (V + F) := by
    have hCb_VF_nn : 0 ≤ V + F := by linarith
    have hF_le_VF : F ≤ V + F := by linarith
    have h_FCb_le_VFCb : F * Cb ≤ (V + F) * Cb :=
      mul_le_mul_of_nonneg_right hF_le_VF hCb_nn
    have hcomm : (V + F) * Cb = Cb * (V + F) := by ring
    linarith
  have h_KinV_le : Kin_sum * V ≤ Kin_sum * (V + F) :=
    mul_le_mul_of_nonneg_left h_VleVF hKin_sum_nn
  have h_KoutV_le : Kout_sum * V ≤ Kout_sum * (V + F) :=
    mul_le_mul_of_nonneg_left h_VleVF hKout_sum_nn
  calc ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun y : M => T.toSection y) B.toFun b l)‖
      ≤ _ := h_tri
    _ ≤ F * Cb + Kin_sum * V + Kout_sum * V := by linarith
    _ ≤ Cb * (V + F) + Kin_sum * (V + F) + Kout_sum * (V + F) := by linarith
    _ = (Cb + Kin_sum + Kout_sum) * (V + F) := by ring

/-! ## Headline: pointwise squared-norm bound on the chart-pulled value of
the nested chart-frame covariant derivative -/

set_option linter.unusedVariables false in
/-- **Pointwise squared-norm bound on the chart-pulled value of the nested
chart-frame covariant derivative `covApply ∇ B (covApply ∇ B T)` at a
chart-`α` partition-of-unity tsupport + Levi-Civita good-set point**, where
`B := chartFrameNormGlobalSmooth g α i`.

The bound is in terms of orders `0, 1, 2` of the chart-pulled representation
`(repr T) ∘ symm` of `T`. The constant `K ≥ 0` depends only on the
chart-atlas locality hypotheses, the metric `g`, the chart at `α`, the ranks
`r, s`, and the chart-frame index `i`; in particular, `K` is independent of
`T` and `b`. -/
theorem rawTensorRepr_intrinsic_chartPulled_value_norm_sq_le_repr_data
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖tensorRSChartE_section_repr (I := I) r s α
            (fun y : M =>
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M =>
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z' : M => T.toSection z')) z)) y) b‖ ^ 2 ≤
          K *
            (∑ j : Fin 3,
              ‖iteratedFDeriv ℝ j.val
                  ((tensorRSChartE_section_repr (I := I) r s α
                      (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
                  (extChartAt I α b)‖ ^ 2) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hB_def
  -- Inner-step constants from `chart_pulled_covApply_repr_value_bound_local`:
  -- bounds `‖repr (covApply ∇ B T) b‖` and `‖repr (covApply ∇ B (covApply ∇ B T)) b‖`
  -- in terms of orders 0, 1 of the inner argument.
  obtain ⟨K_inner, hK_inner_nn, hK_inner_bound⟩ :=
    chart_pulled_covApply_repr_value_bound_local
      (I := I) (M := M) h_atlas g r s α B
  -- The outer step is a NESTED application: we need to bound
  -- `‖repr (covApply ∇ B (covApply ∇ B T)) b‖` by orders 0, 1, 2 of T,
  -- but our `chart_pulled_covApply_repr_value_bound_local` only handles a smooth
  -- *bundled* tensor input. For the nested case, we instead apply the explicit
  -- formula directly with `σ := covApply ∇ B T` (smooth section) and bound
  -- each piece in terms of orders 0, 1, 2 of T.
  --
  -- Pieces of the outer formula:
  --   * intrinsic: `‖fderiv (repr σ ∘ symm) (extChartAt I α b)‖ * ‖trivToE α b (B b)‖`,
  --     where `σ = covApply ∇ B T`. The `fderiv (repr (covApply ∇ B T) ∘ symm)` term
  --     is bounded by `chart_pulled_covApply_repr_fderiv_bound` (Sub-E) by
  --     orders 0, 1, 2 of T.
  --   * slot kernels: bounded by `‖σ(b)‖ = ‖repr (covApply ∇ B T)(b)‖`,
  --     itself bounded by orders 0, 1 of T (via `chart_pulled_covApply_repr_value_bound_local`).
  --
  -- Sub-E:
  obtain ⟨K_E, hK_E_nn, hK_E_bound⟩ :=
    chart_pulled_covApply_repr_fderiv_bound
      (I := I) (M := M) h_atlas g r s α B
  -- Slot kernel op-norm bounds (for σ via covApply).
  have h_in_choose : ∀ k : Fin r, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K := fun k =>
    inputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B k
  choose K_in hK_in_nn hK_in_bound using h_in_choose
  have h_out_choose : ∀ l : Fin s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K := fun l =>
    outputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B l
  choose K_out hK_out_nn hK_out_bound using h_out_choose
  -- Constant for trivToE B norm.
  obtain ⟨Cb, hCb_nn, hCb_bound⟩ := trivToE_B_norm_bound (I := I) (M := M) α B
  set Kin_sum : ℝ := ∑ k : Fin r, K_in k with hKin_sum_def
  set Kout_sum : ℝ := ∑ l : Fin s, K_out l with hKout_sum_def
  have hKin_sum_nn : 0 ≤ Kin_sum := Finset.sum_nonneg (fun k _ => hK_in_nn k)
  have hKout_sum_nn : 0 ≤ Kout_sum := Finset.sum_nonneg (fun l _ => hK_out_nn l)
  -- Combine into the un-squared constant `K_lin` and squared constant.
  -- The combined unsquared bound for `‖repr (covApply ∇ B σ) (b)‖` is
  --   `Cb · ‖fderiv (repr σ ∘ symm) (extChartAt I α b)‖
  --      + (Kin_sum + Kout_sum) · ‖σ(b)‖`
  -- with `σ = covApply ∇ B T`. Using Sub-E and the inner value bound:
  --   ≤ Cb · K_E · (V + F + I²) + (Kin_sum + Kout_sum) · K_inner · (V + F)
  --   ≤ K_lin · (V + F + I²)
  -- where V = ‖iteratedFDeriv 0 (repr T ∘ symm)‖,
  --       F = ‖iteratedFDeriv 1 (repr T ∘ symm)‖,
  --      I² = ‖iteratedFDeriv 2 (repr T ∘ symm)‖.
  -- Set K_lin and squared constant.
  set K_lin : ℝ := Cb * K_E + (Kin_sum + Kout_sum) * K_inner with hKlin_def
  have hKlin_nn : 0 ≤ K_lin := by
    have h1 : 0 ≤ Cb * K_E := mul_nonneg hCb_nn hK_E_nn
    have h2 : 0 ≤ (Kin_sum + Kout_sum) * K_inner :=
      mul_nonneg (by linarith) hK_inner_nn
    linarith
  -- Squared constant: `3 * K_lin^2` (using `(a + b + c)^2 ≤ 3(a^2 + b^2 + c^2)`).
  refine ⟨3 * K_lin ^ 2, by positivity, ?_⟩
  intro T b hb
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Discharge the differentiability hypothesis required by Sub-E.
  have hF2_diff :=
    fderiv_reprT_differentiableAt_goodSet
      (I := I) (M := M) g r s α T hb_good
  -- Sub-E applied to T: bound `‖fderiv (repr (covApply ∇ B T) ∘ symm) (extChartAt I α b)‖`.
  have h_fd_BT :=
    hK_E_bound T hb hF2_diff
  -- Inner value bound: bound `‖repr (covApply ∇ B T) b‖`.
  have h_val_BT := hK_inner_bound T hb
  -- Set abbreviations for the unsquared `T`-data.
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
  -- The outer explicit formula applied to `σ = covApply ∇ B T`.
  -- First, build the smooth section σ.
  have hCovApply_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) B.toFun
              (fun z : M => T.toSection z) y)) := by
    have hT_total :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
      T.toSection.contMDiff
    have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
    -- Bump T's smoothness to ∞ + 1 (which equals ∞).
    have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        ((∞ : WithTop ℕ∞) + 1)
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
      exact hT_total
    have hOn :
        ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) B.toFun
                (fun z : M => T.toSection z) y)) Set.univ :=
      covApply_contMDiffOn
        (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) hB_total hT_plus
    intro b
    exact hOn.contMDiffAt (Filter.univ_mem)
  set σ : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b' : M => TensorRSSpace r s I b'⟯ :=
    { toFun := fun y : M =>
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun z : M => T.toSection z) y
      contMDiff_toFun := hCovApply_smooth } with hσ_def
  -- Apply the outer explicit formula at `b` with `T := σ`.
  have h_outer_formula :=
    chart_pulled_covApply_explicit_formula (I := I) (M := M)
      g r s α σ B (b := b) hb_good
  -- We want to identify:
  --   `tensorRSChartE_section_repr r s α σ.toFun = repr (covApply ∇ B T)`
  -- (definitionally), and similarly for the slot corrections inside `h_outer_formula`.
  -- These rewrites hold by `rfl` because `σ.toFun` IS `fun y => covApply ∇ B T y`.
  -- Slot factorisation at `b`.
  have h_in_factor_σ : ∀ k : Fin r,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSInputSlotCorrection (I := I) r s g α
          σ.toFun B.toFun b k) =
      inputSlotChartKernel (I := I) g r s α B.toFun k b
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun b) := fun k =>
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α σ.toFun B.toFun
      (b := b) (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good) k
  have h_out_factor_σ : ∀ l : Fin s,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSOutputSlotCorrection (I := I) r s g α
          σ.toFun B.toFun b l) =
      outputSlotChartKernel (I := I) g r s α B.toFun l b
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun b) := fun l =>
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α σ.toFun B.toFun
      (b := b) (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good) l
  -- Abbreviation for ‖σ(b) repr‖ = ‖repr (covApply ∇ B T)(b)‖.
  set Vσ : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α σ.toFun b‖
    with hVσ_def
  have hVσ_nn : 0 ≤ Vσ := norm_nonneg _
  -- The inner value bound applies to `T` (the bundled `SmoothCcTensor`), giving
  -- `Vσ ≤ K_inner · (V + F)`.
  have h_Vσ_le : Vσ ≤ K_inner * (V + F) := by
    have h := h_val_BT
    -- `h` bounds `‖repr (covApply ∇ B T)(b)‖` (= Vσ since σ.toFun = covApply ∇ B T).
    -- We need to relate Vσ to the LHS of `h`.
    have heq : tensorRSChartE_section_repr (I := I) r s α σ.toFun b =
        tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun
            (fun y : M => T.toSection y)) b := rfl
    rw [hVσ_def, heq]
    exact h
  -- Sub-E `h_fd_BT` directly applies to `repr T ∘ symm`, giving the fderiv bound
  -- on `repr (covApply ∇ B T) ∘ symm`.
  -- Abbreviation for the fderiv quantity.
  set Fσ : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M =>
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) B.toFun
              (fun z : M => T.toSection z)) y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFσ_def
  have hFσ_nn : 0 ≤ Fσ := norm_nonneg _
  have hFσ_le : Fσ ≤ K_E * (V + F + I2) := h_fd_BT
  -- Now bound `‖repr (covApply ∇ B σ)(b)‖` (which is the headline LHS, unsquared).
  -- Step 1: triangle inequality for the outer formula.
  have h_tri_outer :
      ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
        ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k) -
        ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b l)‖ ≤
        ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ +
        ∑ k : Fin r,
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k)‖ +
        ∑ l : Fin s,
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b l)‖ := by
    have h1 := norm_sub_le
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
        ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k))
      (∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b l))
    have h2 := norm_add_le
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)))
      (∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k))
    have h3 := norm_sum_le
      (Finset.univ : Finset (Fin r))
      (fun k => (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k))
    have h4 := norm_sum_le
      (Finset.univ : Finset (Fin s))
      (fun l => (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l))
    linarith
  -- Step 2: intrinsic-piece bound.
  have h_intr_norm :
      ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ ≤
        Fσ * Cb := by
    have h1 : ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))‖ ≤
        Fσ * ‖trivToE (I := I) α b (B.toFun b)‖ := by
      rw [hFσ_def]
      have hF : ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ =
          ‖fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M =>
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)) B.toFun
                    (fun z : M => T.toSection z)) y) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ := rfl
      rw [← hF]
      exact ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖trivToE (I := I) α b (B.toFun b)‖ ≤ Cb := hCb_bound hb.1
    have h3 : Fσ * ‖trivToE (I := I) α b (B.toFun b)‖ ≤ Fσ * Cb :=
      mul_le_mul_of_nonneg_left h2 hFσ_nn
    exact le_trans h1 h3
  -- Step 3: slot-correction bounds in terms of `Vσ`.
  have h_in_norm_σ : ∀ k : Fin r,
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k)‖ ≤ K_in k * Vσ := by
    intro k
    rw [h_in_factor_σ k]
    have h1 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun b)‖ ≤
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * Vσ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K_in k :=
      hK_in_bound k hb
    have h3 : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * Vσ ≤
        K_in k * Vσ :=
      mul_le_mul_of_nonneg_right h2 hVσ_nn
    linarith
  have h_out_norm_σ : ∀ l : Fin s,
      ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l)‖ ≤ K_out l * Vσ := by
    intro l
    rw [h_out_factor_σ l]
    have h1 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun b)‖ ≤
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * Vσ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K_out l :=
      hK_out_bound l hb
    have h3 : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * Vσ ≤
        K_out l * Vσ :=
      mul_le_mul_of_nonneg_right h2 hVσ_nn
    linarith
  have h_in_sum_σ : ∑ k : Fin r,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k)‖ ≤ Kin_sum * Vσ := by
    calc ∑ k : Fin r, _
        ≤ ∑ k : Fin r, K_in k * Vσ :=
          Finset.sum_le_sum (fun k _ => h_in_norm_σ k)
      _ = (∑ k : Fin r, K_in k) * Vσ := by rw [Finset.sum_mul]
      _ = Kin_sum * Vσ := by rw [hKin_sum_def]
  have h_out_sum_σ : ∑ l : Fin s,
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l)‖ ≤ Kout_sum * Vσ := by
    calc ∑ l : Fin s, _
        ≤ ∑ l : Fin s, K_out l * Vσ :=
          Finset.sum_le_sum (fun l _ => h_out_norm_σ l)
      _ = (∑ l : Fin s, K_out l) * Vσ := by rw [Finset.sum_mul]
      _ = Kout_sum * Vσ := by rw [hKout_sum_def]
  -- Rewrite the LHS of the headline via the outer formula and unsquared bound.
  -- Goal target: `‖repr (covApply ∇ B σ)(b)‖^2 ≤ 3 K_lin^2 · (V^2 + F^2 + I2^2)`.
  -- First: identify the headline LHS with the outer formula RHS via `h_outer_formula`.
  set Y : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M =>
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun z : M =>
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun z' : M => T.toSection z')) z)) y) b‖ with hY_def
  have hY_nn : 0 ≤ Y := norm_nonneg _
  -- Identify Y with the outer formula at b.
  have hY_eq : Y = ‖tensorRSChartE_section_repr (I := I) r s α
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) B.toFun σ.toFun) b‖ := by
    rw [hY_def]
  rw [hY_eq, h_outer_formula]
  -- Now we have: LHS = ‖intrinsic + Σ input - Σ output‖.
  -- Bound it unsquared, then square.
  have h_unsquared :
      ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
        ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k) -
        ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b l)‖
      ≤ K_lin * (V + F + I2) := by
    have h_step1 : ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
            (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
        ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b k) -
        ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              σ.toFun B.toFun b l)‖ ≤
        Fσ * Cb + Kin_sum * Vσ + Kout_sum * Vσ := by
      have := h_tri_outer
      linarith
    -- Now bound `Fσ * Cb + (Kin_sum + Kout_sum) * Vσ ≤ K_lin * (V + F + I2)`.
    have h_FσCb_le : Fσ * Cb ≤ Cb * K_E * (V + F + I2) := by
      have h1 : Cb * Fσ ≤ Cb * (K_E * (V + F + I2)) :=
        mul_le_mul_of_nonneg_left hFσ_le hCb_nn
      have h2 : Fσ * Cb = Cb * Fσ := by ring
      have h3 : Cb * (K_E * (V + F + I2)) = Cb * K_E * (V + F + I2) := by ring
      linarith
    have h_Vσ_VFI2_le : Vσ ≤ K_inner * (V + F + I2) := by
      have hVF_le : V + F ≤ V + F + I2 := by linarith
      have h := h_Vσ_le
      have h2 : K_inner * (V + F) ≤ K_inner * (V + F + I2) :=
        mul_le_mul_of_nonneg_left hVF_le hK_inner_nn
      linarith
    have h_KinV_le : Kin_sum * Vσ ≤ Kin_sum * K_inner * (V + F + I2) := by
      have h := mul_le_mul_of_nonneg_left h_Vσ_VFI2_le hKin_sum_nn
      have hcomm : Kin_sum * (K_inner * (V + F + I2)) =
          Kin_sum * K_inner * (V + F + I2) := by ring
      linarith
    have h_KoutV_le : Kout_sum * Vσ ≤ Kout_sum * K_inner * (V + F + I2) := by
      have h := mul_le_mul_of_nonneg_left h_Vσ_VFI2_le hKout_sum_nn
      have hcomm : Kout_sum * (K_inner * (V + F + I2)) =
          Kout_sum * K_inner * (V + F + I2) := by ring
      linarith
    have hKlin_expand :
        K_lin * (V + F + I2) =
          (Cb * K_E) * (V + F + I2) +
          ((Kin_sum + Kout_sum) * K_inner) * (V + F + I2) := by
      rw [hKlin_def]; ring
    have h_KinKout : (Kin_sum + Kout_sum) * K_inner * (V + F + I2) =
        Kin_sum * K_inner * (V + F + I2) +
        Kout_sum * K_inner * (V + F + I2) := by ring
    have hFinal : Fσ * Cb + Kin_sum * Vσ + Kout_sum * Vσ ≤
        K_lin * (V + F + I2) := by
      rw [hKlin_expand]
      have h1 : Fσ * Cb ≤ Cb * K_E * (V + F + I2) := h_FσCb_le
      have h2 : Kin_sum * Vσ ≤ Kin_sum * K_inner * (V + F + I2) := h_KinV_le
      have h3 : Kout_sum * Vσ ≤ Kout_sum * K_inner * (V + F + I2) := h_KoutV_le
      have hexpand : (Kin_sum + Kout_sum) * K_inner * (V + F + I2) =
          Kin_sum * K_inner * (V + F + I2) +
          Kout_sum * K_inner * (V + F + I2) := by ring
      linarith
    linarith
  -- Square the unsquared bound. Use `(K_lin (V + F + I2))^2 ≤ 3 K_lin^2 (V^2 + F^2 + I2^2)`.
  -- First, replace `iteratedFDeriv 0` with V, etc.
  -- Identify the sum `∑ j : Fin 3, ‖iteratedFDeriv j ...‖^2` with `V^2 + F^2 + I2^2`.
  have h_sum_eq : ∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 = V ^ 2 + F ^ 2 + I2 ^ 2 := by
    -- For j = 0: ‖iteratedFDeriv 0 F (extChartAt I α b)‖ = ‖F (extChartAt I α b)‖
    --   = ‖repr T ((extChartAt I α).symm (extChartAt I α b))‖ = ‖repr T b‖ = V
    -- (since b ∈ good set ⊆ chart source, so (symm ∘ extChartAt) b = b).
    have h0 : ‖iteratedFDeriv ℝ 0
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ = V := by
      rw [norm_iteratedFDeriv_zero, hV_def]
      have hb_src : b ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
      have hb_extsrc : b ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact hb_src
      have hround : (extChartAt I α).symm ((extChartAt I α) b) = b :=
        (extChartAt I α).left_inv hb_extsrc
      change ‖((tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm) (extChartAt I α b)‖ = _
      rw [Function.comp_apply, hround]
    have h1 : ‖iteratedFDeriv ℝ 1
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ = F := by
      rw [norm_iteratedFDeriv_one, hF_def]
    have h2 : ‖iteratedFDeriv ℝ 2
            ((tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ = I2 := by
      rw [hI2_def]
    -- Expand the sum.
    rw [Fin.sum_univ_three]
    -- The summand at j ∈ {0, 1, 2} (as a Fin 3) has `.val` reducing to 0, 1, 2.
    -- We rewrite to the named abbreviations.
    change ‖iteratedFDeriv ℝ ((0 : Fin 3).val) _ _‖ ^ 2 +
        ‖iteratedFDeriv ℝ ((1 : Fin 3).val) _ _‖ ^ 2 +
        ‖iteratedFDeriv ℝ ((2 : Fin 3).val) _ _‖ ^ 2 = _
    have e0 : (0 : Fin 3).val = 0 := rfl
    have e1 : (1 : Fin 3).val = 1 := rfl
    have e2 : (2 : Fin 3).val = 2 := rfl
    rw [e0, e1, e2, h0, h1, h2]
  rw [h_sum_eq]
  -- Now: target is `‖outer formula‖^2 ≤ 3 K_lin^2 (V^2 + F^2 + I2^2)`.
  have h_pre_sq : (K_lin * (V + F + I2)) ^ 2 = K_lin ^ 2 * (V + F + I2) ^ 2 := by ring
  have h_sum_sq_le : (V + F + I2) ^ 2 ≤ 3 * (V ^ 2 + F ^ 2 + I2 ^ 2) := by
    have h_expand : (V + F + I2) ^ 2 =
        V^2 + F^2 + I2^2 + 2 * (V * F) + 2 * (V * I2) + 2 * (F * I2) := by ring
    have h_2VF : 2 * (V * F) ≤ V^2 + F^2 := by
      have := sq_nonneg (V - F); nlinarith
    have h_2VI2 : 2 * (V * I2) ≤ V^2 + I2^2 := by
      have := sq_nonneg (V - I2); nlinarith
    have h_2FI2 : 2 * (F * I2) ≤ F^2 + I2^2 := by
      have := sq_nonneg (F - I2); nlinarith
    linarith
  -- Square the unsquared bound to get the goal.
  have h_unsq_le_Klin : ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l)‖ ≤ K_lin * (V + F + I2) := h_unsquared
  -- LHS of the goal IS the unsquared norm above, by `h_outer_formula`.
  -- After `rw [h_outer_formula]`, the LHS becomes the explicit-formula RHS norm.
  have h_lhs_sq : (‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l)‖) ^ 2 ≤
      (K_lin * (V + F + I2)) ^ 2 := by
    have hnn : 0 ≤ K_lin * (V + F + I2) :=
      mul_nonneg hKlin_nn (by linarith)
    exact sq_le_sq' (by linarith [norm_nonneg (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α σ.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b)) +
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b k) -
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            σ.toFun B.toFun b l))]) h_unsq_le_Klin
  calc _ ≤ (K_lin * (V + F + I2)) ^ 2 := h_lhs_sq
    _ = K_lin ^ 2 * (V + F + I2) ^ 2 := h_pre_sq
    _ ≤ K_lin ^ 2 * (3 * (V^2 + F^2 + I2^2)) := by
        have hKlin2_nn : 0 ≤ K_lin ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left h_sum_sq_le hKlin2_nn
    _ = 3 * K_lin ^ 2 * (V^2 + F^2 + I2^2) := by ring

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorRepr_intrinsic_chartPulled_value_norm_sq_le_repr_data
end Sanity
