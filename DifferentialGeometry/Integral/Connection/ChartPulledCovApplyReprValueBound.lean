import DifferentialGeometry.Integral.Connection.SlotCorrectionChartFderivBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyExplicitFormula

/-!
# Pointwise value bound for the chart-pulled representation of `covApply ∇ B T`

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a smooth tangent vector field `B`, and a smooth compactly supported
`(r, s)`-tensor section `T`, the value of the chart-`α`-trivialised
representation of `covApply ∇ B T` at a partition-of-unity tsupport point `b`
inside the chart-`α` Levi-Civita good set is bounded by

```
K * (‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
                (extChartAt I α b)‖
     + ‖tensorRSChartE_section_repr r s α T.toSection b‖)
```

for a constant `K ≥ 0` depending only on `g`, `α`, the chart-atlas locality
hypothesis `h_atlas`, the ranks `r`, `s`, and `B` — in particular independent
of `T` and `b`.

## Strategy

The chart-pulled explicit formula

```
tensorRSChartE_section_repr r s α (covApply ∇ B T) b
    = fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
        (extChartAt I α b) (trivToE α b (B b))
      + ∑ k, (triv α).cLMA b (chartTensorRSInputSlotCorrection ... k)
      - ∑ l, (triv α).cLMA b (chartTensorRSOutputSlotCorrection ... l)
```

valid for `b` in the chart-`α` Levi-Civita good set. Taking norms via the
triangle inequality reduces the problem to three uniform value bounds:

* the intrinsic piece's CLM-application bound: `‖fderiv F (trivToE α b (B b))‖
  ≤ ‖fderiv F‖ · ‖trivToE α b (B b)‖`, with `‖trivToE α b (B b)‖` uniformly
  bounded over the POU tsupport;
* each input-slot piece's kernel factorisation
  `(triv α).cLMA b (slot k) = kernel_k(b) (repr T b)`, giving
  `‖slot k‖ ≤ ‖kernel_k(b)‖ · ‖repr T b‖`, with `‖kernel_k(b)‖` uniformly
  bounded on `tsupport ∩ goodSet`;
* the analogous output-slot bound.

Summing and absorbing the constants into a single `K_total` yields the
headline. -/

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

/-! ## Uniform value bound for `trivToE α b (B b)` on the POU tsupport

The function `b ↦ trivToE α b (B b)` is just the chart-trivialised
representation `chartE_section_repr α B.toFun b` (both are
`(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b (B.toFun b)`).
This is smooth on the chart source, hence continuous on the compact POU
tsupport, and therefore uniformly bounded above. -/

/-- Uniform value bound for `‖trivToE α b (B b)‖` on the chart-`α`
partition-of-unity tsupport. -/
private lemma trivToE_B_value_bound_on_pouTsupport
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖trivToE (I := I) α b (B.toFun b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  -- Smoothness of `u(y) := chartE_section_repr α B.toFun ∘ symm` on the chart
  -- target image of the good set.
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  -- Continuity of `‖u‖` on the open image.
  have hcont_u : ContinuousOn (fun y : E =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    continuous_norm.comp_continuousOn hu_cd.continuousOn
  -- Map K_set into the good-set image via extChartAt.
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_u_M : ContinuousOn (fun b : M =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖) K_set :=
    hcont_u.comp hφ_cont hmaps
  obtain ⟨Cu, hCu_mem⟩ := hK_compact.bddAbove_image hcont_u_M
  refine ⟨max Cu 0, le_max_right _ _, ?_⟩
  intro b hb
  -- `‖trivToE α b (B b)‖ = ‖chartE_section_repr α B.toFun b‖`
  --                     = ‖(chartE_section_repr α B.toFun ∘ symm)
  --                          (extChartAt I α b)‖` on the chart source.
  have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart
  have hsymm_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_extsrc
  have h_eq : ‖trivToE (I := I) α b (B.toFun b)‖ =
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ := by
    -- Unfold Function.comp; `chartE_section_repr α B.toFun b = trivToE α b (B b)`
    -- by definition (both are `triv.continuousLinearMapAt ℝ b (B b)`).
    change ‖trivToE (I := I) α b (B.toFun b)‖ =
      ‖chartE_section_repr (I := I) α B.toFun
        ((extChartAt I α).symm (extChartAt I α b))‖
    rw [hsymm_inv]
    rfl
  rw [h_eq]
  have h1 := hCu_mem ⟨b, hb, rfl⟩
  exact le_trans h1 (le_max_left _ _)

/-! ## Headline -/

/-- **Pointwise value bound on the chart-pulled representation of the first
covariant derivative applied to a tangent vector field.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, a smooth tangent vector field `B`, a smooth compactly supported
`(r, s)`-tensor section `T`, and a chart-`α` partition-of-unity tsupport
point `b` lying in the chart-`α` Levi-Civita good set, the norm of the
chart-`α`-trivialised representation of `covApply ∇ B T` at `b` is bounded by

```
K * (‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘ symm)
                (extChartAt I α b)‖
     + ‖tensorRSChartE_section_repr r s α T.toSection b‖)
```

The constant `K` depends only on `h_atlas`, `g`, `α`, `r`, `s`, and `B`. -/
theorem chart_pulled_covApply_repr_value_bound
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
            (fun z : M =>
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) B.toFun
                (fun w : M => T.toSection w)) z) b‖ ≤
          K *
            (‖fderiv ℝ
                ((tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
              ‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z) b‖) := by
  classical
  -- Uniform `‖B(b)‖` bound on POU tsupport.
  obtain ⟨C_B, hCB_nn, hCB_bound⟩ :=
    trivToE_B_value_bound_on_pouTsupport (I := I) (M := M) α B
  -- Uniform kernel op-norm bounds.
  have h_in_choose : ∀ k : Fin r, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K := fun k =>
    inputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B k
  choose K_in hKin_nn hKin_bound using h_in_choose
  have h_out_choose : ∀ l : Fin s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K := fun l =>
    outputSlotChartKernel_opNorm_uniform_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α B l
  choose K_out hKout_nn hKout_bound using h_out_choose
  refine ⟨C_B + (∑ k : Fin r, K_in k) + (∑ l : Fin s, K_out l), ?_, ?_⟩
  · have h2 : 0 ≤ ∑ k : Fin r, K_in k :=
      Finset.sum_nonneg (fun k _ => hKin_nn k)
    have h3 : 0 ≤ ∑ l : Fin s, K_out l :=
      Finset.sum_nonneg (fun l _ => hKout_nn l)
    linarith
  intro T b hb
  have hb_pou : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb.1
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  -- Step 1: apply the chart-pulled explicit formula at `b`.
  have h_formula :=
    chart_pulled_covApply_explicit_formula (I := I) (M := M)
      g r s α T.toSection B (b := b) hb_good
  -- The formula's `T.toFun` is `T.toSection.toFun`, which is definitionally
  -- equal to `fun w => T.toSection w` by η-expansion of `DFunLike.coe`. Use
  -- a `change` to align.
  have h_formula' :
      tensorRSChartE_section_repr (I := I) r s α
          (fun z : M =>
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) B.toFun
              (fun w : M => T.toSection w)) z) b =
        fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) ∘
              (extChartAt I α).symm) (extChartAt I α b)
              (trivToE (I := I) α b (B.toFun b))
        + ∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun z : M => T.toSection z) B.toFun b k)
        - ∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun z : M => T.toSection z) B.toFun b l) := h_formula
  rw [h_formula']
  -- Step 2: triangle inequality.
  -- Abbreviations.
  set F_val : TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b with hF_val_def
  set FD : E →L[ℝ] TensorRSModel r s ℝ E :=
    fderiv ℝ
      ((tensorRSChartE_section_repr (I := I) r s α
          (fun z : M => T.toSection z)) ∘ (extChartAt I α).symm)
      (extChartAt I α b) with hFD_def
  -- Intrinsic piece value.
  set P_intr : TensorRSModel r s ℝ E :=
    FD (trivToE (I := I) α b (B.toFun b)) with hP_intr_def
  -- Slot piece values.
  set P_in : Fin r → TensorRSModel r s ℝ E := fun k =>
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun z : M => T.toSection z) B.toFun b k) with hP_in_def
  set P_out : Fin s → TensorRSModel r s ℝ E := fun l =>
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun z : M => T.toSection z) B.toFun b l) with hP_out_def
  -- Show LHS norm with explicit shape.
  change ‖P_intr + ∑ k : Fin r, P_in k - ∑ l : Fin s, P_out l‖ ≤ _
  -- Norm triangle inequality.
  have h_norm_le :
      ‖P_intr + ∑ k : Fin r, P_in k - ∑ l : Fin s, P_out l‖ ≤
        ‖P_intr‖ + (∑ k : Fin r, ‖P_in k‖) + (∑ l : Fin s, ‖P_out l‖) := by
    have h1 := norm_sub_le (P_intr + ∑ k : Fin r, P_in k)
      (∑ l : Fin s, P_out l)
    have h2 := norm_add_le P_intr (∑ k : Fin r, P_in k)
    have h3 := norm_sum_le (Finset.univ : Finset (Fin r)) P_in
    have h4 := norm_sum_le (Finset.univ : Finset (Fin s)) P_out
    linarith
  -- Bound `‖P_intr‖`.
  have h_intr_bound : ‖P_intr‖ ≤ ‖FD‖ * C_B := by
    have hop : ‖FD (trivToE (I := I) α b (B.toFun b))‖
        ≤ ‖FD‖ * ‖trivToE (I := I) α b (B.toFun b)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hB := hCB_bound hb_pou
    have hFD_nn : 0 ≤ ‖FD‖ := norm_nonneg _
    calc ‖P_intr‖
        = ‖FD (trivToE (I := I) α b (B.toFun b))‖ := rfl
      _ ≤ ‖FD‖ * ‖trivToE (I := I) α b (B.toFun b)‖ := hop
      _ ≤ ‖FD‖ * C_B := mul_le_mul_of_nonneg_left hB hFD_nn
  -- Bound each `‖P_in k‖` via the kernel factorisation.
  have h_in_bound : ∀ k : Fin r, ‖P_in k‖ ≤ K_in k * ‖F_val‖ := by
    intro k
    have hb_src : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    -- Kernel factorisation at `b`.
    have h_factor :=
      chartTensorRSInputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := b) hb_src k
    -- `P_in k = kernel(b) (F_val)` after the factorisation.
    have hP_in_factored : P_in k =
        inputSlotChartKernel (I := I) g r s α B.toFun k b F_val := by
      change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun z : M => T.toSection z) B.toFun b k) =
        inputSlotChartKernel (I := I) g r s α B.toFun k b
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T.toSection b))
      exact h_factor
    rw [hP_in_factored]
    have hop : ‖inputSlotChartKernel (I := I) g r s α B.toFun k b F_val‖
        ≤ ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * ‖F_val‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hker := hKin_bound k hb
    have hFval_nn : 0 ≤ ‖F_val‖ := norm_nonneg _
    calc ‖inputSlotChartKernel (I := I) g r s α B.toFun k b F_val‖
        ≤ ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ * ‖F_val‖ := hop
      _ ≤ K_in k * ‖F_val‖ := mul_le_mul_of_nonneg_right hker hFval_nn
  -- Bound each `‖P_out l‖` analogously.
  have h_out_bound : ∀ l : Fin s, ‖P_out l‖ ≤ K_out l * ‖F_val‖ := by
    intro l
    have hb_src : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have h_factor :=
      chartTensorRSOutputSlotCorrection_chart_kernel_factorization
        (I := I) (M := M) g r s α
        (fun b' : M => T.toSection b') B.toFun
        (b := b) hb_src l
    have hP_out_factored : P_out l =
        outputSlotChartKernel (I := I) g r s α B.toFun l b F_val := by
      change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun z : M => T.toSection z) B.toFun b l) =
        outputSlotChartKernel (I := I) g r s α B.toFun l b
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T.toSection b))
      exact h_factor
    rw [hP_out_factored]
    have hop : ‖outputSlotChartKernel (I := I) g r s α B.toFun l b F_val‖
        ≤ ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * ‖F_val‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hker := hKout_bound l hb
    have hFval_nn : 0 ≤ ‖F_val‖ := norm_nonneg _
    calc ‖outputSlotChartKernel (I := I) g r s α B.toFun l b F_val‖
        ≤ ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ * ‖F_val‖ := hop
      _ ≤ K_out l * ‖F_val‖ := mul_le_mul_of_nonneg_right hker hFval_nn
  -- Sum the slot bounds.
  have h_in_sum_bound :
      (∑ k : Fin r, ‖P_in k‖) ≤ (∑ k : Fin r, K_in k) * ‖F_val‖ := by
    calc ∑ k : Fin r, ‖P_in k‖
        ≤ ∑ k : Fin r, K_in k * ‖F_val‖ :=
          Finset.sum_le_sum (fun k _ => h_in_bound k)
      _ = (∑ k : Fin r, K_in k) * ‖F_val‖ := by rw [Finset.sum_mul]
  have h_out_sum_bound :
      (∑ l : Fin s, ‖P_out l‖) ≤ (∑ l : Fin s, K_out l) * ‖F_val‖ := by
    calc ∑ l : Fin s, ‖P_out l‖
        ≤ ∑ l : Fin s, K_out l * ‖F_val‖ :=
          Finset.sum_le_sum (fun l _ => h_out_bound l)
      _ = (∑ l : Fin s, K_out l) * ‖F_val‖ := by rw [Finset.sum_mul]
  -- Combine.
  -- We want:
  --   ‖P_intr‖ + ∑‖P_in k‖ + ∑‖P_out l‖
  --     ≤ ‖FD‖·C_B + (∑K_in)·‖F_val‖ + (∑K_out)·‖F_val‖
  --     ≤ C_B·‖FD‖ + (∑K_in)·(‖FD‖+‖F_val‖) + (∑K_out)·(‖FD‖+‖F_val‖)
  --        — wait, we want ‖FD‖ + ‖F_val‖, not just ‖F_val‖.
  -- Rearrange: target RHS is K_total · (‖FD‖ + ‖F_val‖)
  -- where K_total = C_B + ∑K_in + ∑K_out.
  -- ‖FD‖·C_B ≤ C_B·(‖FD‖+‖F_val‖) since C_B ≥ 0 and ‖F_val‖ ≥ 0.
  -- (∑K_in)·‖F_val‖ ≤ (∑K_in)·(‖FD‖+‖F_val‖).
  -- (∑K_out)·‖F_val‖ ≤ (∑K_out)·(‖FD‖+‖F_val‖).
  set FN : ℝ := ‖FD‖ with hFN_def
  set VN : ℝ := ‖F_val‖ with hVN_def
  have hFN_nn : 0 ≤ FN := norm_nonneg _
  have hVN_nn : 0 ≤ VN := norm_nonneg _
  have hKin_sum_nn : 0 ≤ ∑ k : Fin r, K_in k :=
    Finset.sum_nonneg (fun k _ => hKin_nn k)
  have hKout_sum_nn : 0 ≤ ∑ l : Fin s, K_out l :=
    Finset.sum_nonneg (fun l _ => hKout_nn l)
  -- C_B * FN ≤ C_B * (FN + VN)
  have h_intr_final : FN * C_B ≤ C_B * (FN + VN) := by
    have hFN_le : FN ≤ FN + VN := by linarith
    have h_mul : C_B * FN ≤ C_B * (FN + VN) :=
      mul_le_mul_of_nonneg_left hFN_le hCB_nn
    have hcomm : FN * C_B = C_B * FN := by ring
    linarith
  have h_VN_le : VN ≤ FN + VN := by linarith
  have h_in_final : (∑ k : Fin r, K_in k) * VN ≤
      (∑ k : Fin r, K_in k) * (FN + VN) :=
    mul_le_mul_of_nonneg_left h_VN_le hKin_sum_nn
  have h_out_final : (∑ l : Fin s, K_out l) * VN ≤
      (∑ l : Fin s, K_out l) * (FN + VN) :=
    mul_le_mul_of_nonneg_left h_VN_le hKout_sum_nn
  -- Assemble.
  calc ‖P_intr + ∑ k : Fin r, P_in k - ∑ l : Fin s, P_out l‖
      ≤ ‖P_intr‖ + (∑ k : Fin r, ‖P_in k‖) + (∑ l : Fin s, ‖P_out l‖) :=
        h_norm_le
    _ ≤ FN * C_B + (∑ k : Fin r, K_in k) * VN +
        (∑ l : Fin s, K_out l) * VN := by
          have hb1 := h_intr_bound
          -- ‖P_intr‖ ≤ FN · C_B because FD = FN by definition.
          have hb1' : ‖P_intr‖ ≤ FN * C_B := by
            have heq : ‖FD‖ * C_B = FN * C_B := by rw [hFN_def]
            rw [← heq]; exact hb1
          have hb2 := h_in_sum_bound
          have hb2' : (∑ k : Fin r, ‖P_in k‖) ≤
              (∑ k : Fin r, K_in k) * VN := by
            have heq : (∑ k : Fin r, K_in k) * ‖F_val‖ =
                (∑ k : Fin r, K_in k) * VN := by rw [hVN_def]
            rw [← heq]; exact hb2
          have hb3 := h_out_sum_bound
          have hb3' : (∑ l : Fin s, ‖P_out l‖) ≤
              (∑ l : Fin s, K_out l) * VN := by
            have heq : (∑ l : Fin s, K_out l) * ‖F_val‖ =
                (∑ l : Fin s, K_out l) * VN := by rw [hVN_def]
            rw [← heq]; exact hb3
          linarith
    _ ≤ C_B * (FN + VN) + (∑ k : Fin r, K_in k) * (FN + VN) +
        (∑ l : Fin s, K_out l) * (FN + VN) := by linarith
    _ = (C_B + (∑ k : Fin r, K_in k) + (∑ l : Fin s, K_out l)) *
          (FN + VN) := by ring

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.chart_pulled_covApply_repr_value_bound
end Sanity
