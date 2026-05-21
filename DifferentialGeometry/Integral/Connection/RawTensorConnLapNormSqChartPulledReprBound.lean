import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.Connection.RawTensorConnLapPointwiseBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.LocalChartConsistency
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivIntrinsicComponent
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# Pointwise squared op-norm bound for `rawTensorConnLap` by the chart-pulled
representation data

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, and a smooth compactly supported `(r, s)`-tensor section `T`, this
file ships the pointwise squared op-norm bound

```
‖rawTensorConnLap g r s T.toSection b‖^2
    ≤ K * (‖tensorRSChartE_section_repr r s α T.toSection b‖^2
           + ‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘
                (extChartAt I α).symm) (extChartAt I α b)‖^2
           + ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α
                T.toSection ∘ (extChartAt I α).symm) (extChartAt I α b)‖^2)
```

valid for all `b` in the intersection of the chart-α partition-of-unity
tsupport and the chart-α Levi-Civita good set. The constant `K` depends on
`g`, the chart at `α`, the chart-atlas locality hypotheses, and the ranks
`r`, `s`; it is independent of `T` and `b`.

## Strategy

1. The chart-data-only pointwise bound
   `rawTensorConnLap_pointwise_bound_chart_data` decomposes `‖raw‖` into a
   constant times the sum of `chartFrameData T b i` and `secondAppChartData T
   b i` over the frame index `i`.

2. For each `i`, each piece of `chartFrameData` and `secondAppChartData` is
   bounded by a uniform constant times `V + F + I2`, where `V`, `F`, `I2`
   denote the three chart-pulled representation norms.

3. The chart-source-consistency predicate `HasChartSourceConsistentChartAt`
   discharges the chart-equation hypothesis `chartAt H b = chartAt H α` of
   `chartFrameNormGlobalSmooth_eventuallyEq_smoothOrthoFrame`, since the
   chart-α Levi-Civita good set is contained in the chart-α source.

4. Summing the per-`i` bounds gives `‖raw‖ ≤ K_lin * (V + F + I2)`. Squaring
   via `(a + b + c)^2 ≤ 3 * (a^2 + b^2 + c^2)` yields the headline.
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

/-! ## Arithmetic squared bound -/

private lemma sq_add_three_le_three_mul_sum_sq (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-! ## Smoothness of `repr T ∘ symm` on the chart-target image of the good set -/

/-- Smoothness on the chart-target image of the chart-`α` Levi-Civita good set
of the chart-pulled tensor representation. -/
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

/-- Differentiability of `fderiv ℝ (repr T ∘ symm)` at the chart point. -/
private lemma fderiv_reprT_differentiableAt_chart_point
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) := by
  classical
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α b ∈
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

/-! ## Pointwise transfer from `smoothOrthoFrame g b i` to
`chartFrameNormGlobalSmooth g α i` via the chart-source-consistency predicate -/

/-- The smooth orthonormal frame `smoothOrthoFrame g b i` and the global
smooth section `chartFrameNormGlobalSmooth g α i` are eventually equal near
any `b` in the POU tsupport ∩ chart-α good set, under the strong predicate. -/
private lemma smoothOrthoFrame_eventuallyEq_at_b
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    (smoothOrthoFrame (I := I) g b i :
        Π y : M, TangentSpace I y) =ᶠ[𝓝 b]
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun := by
  classical
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb.2
  have hb_chart : chartAt H b = chartAt H α :=
    h_atlas_strong α b hb_chart_src
  exact chartFrameNormGlobalSmooth_eventuallyEq_smoothOrthoFrame
    (I := I) (M := M) h_atlas g α i hb hb_chart

/-- Pointwise equality at `b`. -/
private lemma smoothOrthoFrame_eq_chartFrameNormGlobalSmooth_at_b
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α) :
    smoothOrthoFrame (I := I) g b i b =
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b :=
  (smoothOrthoFrame_eventuallyEq_at_b (I := I) (M := M)
    h_atlas h_atlas_strong g α i hb).self_of_nhds

/-! ## Uniform fibre-norm bound on `chartFrameNormGlobalSmooth g α i` -/

/-- Uniform bound on `‖chartFrameNormGlobalSmooth g α i.toFun b‖` over the
chart-`α` POU tsupport. -/
private lemma chartFrameNormGlobalSmooth_norm_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖(chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  have hsec_total :
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun y : M => TangentSpace I y) x
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x)) :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have hrepr_cm : ContMDiffOn I (𝓘(ℝ, E)) ∞
      (chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun))
      (chartAt H α).source := by
    have hbase : (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
      TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
    have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (e := trivializationAt E (TangentSpace I) α)).mp hsec_total.contMDiffOn
    rw [hbase] at hrewrite
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt E (TangentSpace I) α).linearMapAt ℝ x
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have hcont_on : ContinuousOn
      (fun b : M => ‖chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖)
      K_set := by
    have hcont := hrepr_cm.continuousOn
    exact (continuous_norm.comp_continuousOn hcont).mono hK_sub
  obtain ⟨MB, hMB⟩ :
      BddAbove ((fun b : M => ‖chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖) ''
          K_set) := hK_compact.bddAbove_image hcont_on
  refine ⟨C_Jinv * (max MB 0), mul_nonneg hCJinv_nn (le_max_right _ _), ?_⟩
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hK_sub hb
  have h_inv : (trivFromE (I := I) α b)
      (chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b) =
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b :=
    trivFromE_trivToE (I := I) α (x := b) hb_base _
  have h_op : ‖(chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b‖ ≤
      ‖trivFromE (I := I) α b‖ *
        ‖chartE_section_repr (I := I) α
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖ := by
    have h := (trivFromE (I := I) α b).le_opNorm
      (chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b)
    rw [h_inv] at h
    exact h
  have h_repr_le :
      ‖chartE_section_repr (I := I) α
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖ ≤
        max MB 0 := by
    have h_in := hMB ⟨b, hb, rfl⟩
    exact le_trans h_in (le_max_left _ _)
  have hJinv_b : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_repr_nn : 0 ≤ ‖chartE_section_repr (I := I) α
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖ :=
    norm_nonneg _
  have h_chain :
      ‖trivFromE (I := I) α b‖ *
          ‖chartE_section_repr (I := I) α
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b‖ ≤
        C_Jinv * (max MB 0) := by
    have h_a := mul_le_mul_of_nonneg_right hJinv_b h_repr_nn
    have h_b := mul_le_mul_of_nonneg_left h_repr_le hCJinv_nn
    linarith
  linarith

/-! ## Uniform fibre-norm bound on `smoothOrthoFrame g b i b` over the POU
tsupport ∩ goodSet -/

/-- Uniform bound on `‖smoothOrthoFrame g b i b‖` over `K_set ∩ goodSet`, per
frame index, using both predicates and the global smooth section bound. -/
private lemma smoothOrthoFrame_norm_uniform_bound
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖smoothOrthoFrame (I := I) g b i b‖ ≤ C := by
  classical
  obtain ⟨C_glob, hC_glob_nn, hC_glob_bound⟩ :=
    chartFrameNormGlobalSmooth_norm_bound (I := I) (M := M)
      h_atlas g α i
  refine ⟨C_glob, hC_glob_nn, ?_⟩
  intro b hb
  rw [smoothOrthoFrame_eq_chartFrameNormGlobalSmooth_at_b
        (I := I) (M := M) h_atlas h_atlas_strong g α i hb]
  exact hC_glob_bound b hb.1

/-! ## Bound on `chartFrameData_i` -/

/-- Per-frame-index bound for `chartFrameData T b i` by `K · (V + F + I2)`. -/
private lemma chartFrameData_le_VFI2
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        chartFrameData (I := I) g r s α
            (fun y : M => T.toSection y) b i ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨C_X, hCX_nn, hCX_bound⟩ :=
    smoothOrthoFrame_norm_uniform_bound (I := I) (M := M)
      h_atlas h_atlas_strong g α i
  set const_Mb : ℝ := (max (1 + C_X) 1) ^ (max r s) with hconst_Mb_def
  have hconst_Mb_nn : 0 ≤ const_Mb := by
    have : 0 ≤ max (1 + C_X) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  -- Sub-E with B := chartFrameNormGlobalSmooth.
  obtain ⟨K_E, hKE_nn, hKE_bound⟩ :=
    chart_pulled_covApply_repr_fderiv_bound
      (I := I) (M := M) h_atlas g r s α
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i)
  -- chartTensorRSCovariantDerivative op-norm bound.
  obtain ⟨C_cov, hCcov_nn, hCcov_bound⟩ :=
    chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
      (I := I) (M := M) h_atlas g r s α
  -- Reverse fiber norm.
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  obtain ⟨C_rev, hCrev_pos, hCrev_bound⟩ :=
    tensorRSSpace_norm_le_chartRepr_norm_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK_compact) (hKsub := hK_sub)
  have hCrev_nn : 0 ≤ C_rev := le_of_lt hCrev_pos
  -- Headline constant: K_lin = const_Mb · (K_E · C_X + C_cov · const_Mb · (C_X + C_rev)).
  set K_lin : ℝ :=
    const_Mb * (K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := by
    have h1 : 0 ≤ K_E * C_X := mul_nonneg hKE_nn hCX_nn
    have h2 : 0 ≤ C_cov * const_Mb := mul_nonneg hCcov_nn hconst_Mb_nn
    have h3 : 0 ≤ C_X + C_rev := by linarith
    have h4 : 0 ≤ C_cov * const_Mb * (C_X + C_rev) := mul_nonneg h2 h3
    have h5 : 0 ≤ K_E * C_X + C_cov * const_Mb * (C_X + C_rev) := by linarith
    exact mul_nonneg hconst_Mb_nn h5
  refine ⟨K_lin, hK_lin_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  set X_i : Π b' : M, TangentSpace I b' :=
    fun b' => smoothOrthoFrame (I := I) g b i b' with hX_i_def
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ with hV_def
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFnorm_def
  set I2norm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2norm_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ Fnorm := norm_nonneg _
  have hI2_nn : 0 ≤ I2norm := norm_nonneg _
  have hVFI2_nn : 0 ≤ V + Fnorm + I2norm := by linarith
  -- Eventually-equal: X_i =ᶠ[𝓝 b] Bg.toFun.
  have h_evt_X : X_i =ᶠ[𝓝 b] Bg.toFun :=
    smoothOrthoFrame_eventuallyEq_at_b (I := I) (M := M)
      h_atlas h_atlas_strong g α i ⟨hb_pou, hb_good⟩
  -- Eventually-equal (function-level via trivialisation): the chart-pulled repr
  -- of covApply ∇ X_i T and covApply ∇ Bg.toFun T agree near b.
  -- This avoids Pi-type EventuallyEq issues.
  have h_evt_cov_repr_M :
      (fun y : M => tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X_i
          (fun y' : M => T.toSection y')) y) =ᶠ[𝓝 b]
      (fun y : M => tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) Bg.toFun
          (fun y' : M => T.toSection y')) y) := by
    filter_upwards [h_evt_X] with y hy
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ y
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) X_i
              (fun y' : M => T.toSection y') y) =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ y
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) Bg.toFun
              (fun y' : M => T.toSection y') y)
    have h_cov_eq : covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X_i
            (fun y' : M => T.toSection y') y =
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) Bg.toFun
            (fun y' : M => T.toSection y') y := by
      simp only [covApply, hy]
    rw [h_cov_eq]
  -- repr ∘ symm versions agree eventually near extChartAt α b.
  have h_evt_repr_symm :
      (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) X_i
            (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
        (tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) Bg.toFun
              (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm) := by
    have hb_extsrc : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
    have hb_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv hb_extsrc
    have h_open : IsOpen (extChartAt I α).target :=
      isOpen_extChartAt_target (I := I) α
    have hb_tgt : extChartAt I α b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_extsrc
    have hsymm_cont : ContinuousAt (extChartAt I α).symm
        (extChartAt I α b) :=
      (continuousOn_extChartAt_symm (I := I) α).continuousAt
        (h_open.mem_nhds hb_tgt)
    -- We pull h_evt_cov_repr_M through symm via continuity.
    have hpull_set : (extChartAt I α).symm ⁻¹'
        {z : M | tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) X_i
              (fun y' : M => T.toSection y')) z =
          tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) Bg.toFun
              (fun y' : M => T.toSection y')) z} ∈ 𝓝 (extChartAt I α b) := by
      have h_in_nhds_b : {z : M | tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) X_i
              (fun y' : M => T.toSection y')) z =
          tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) Bg.toFun
              (fun y' : M => T.toSection y')) z} ∈ 𝓝 b := h_evt_cov_repr_M
      exact hsymm_cont.preimage_mem_nhds (by rw [hb_inv]; exact h_in_nhds_b)
    filter_upwards [hpull_set] with y hy
    change tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X_i
          (fun y' : M => T.toSection y')) ((extChartAt I α).symm y) =
      tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) Bg.toFun
          (fun y' : M => T.toSection y')) ((extChartAt I α).symm y)
    exact hy
  -- fderiv at chart point is equal.
  have h_fderiv_eq :
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) X_i
              (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
        (extChartAt I α b) =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) Bg.toFun
              (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
        (extChartAt I α b) := Filter.EventuallyEq.fderiv_eq h_evt_repr_symm
  have hF2_diff : DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) :=
    fderiv_reprT_differentiableAt_chart_point (I := I) (M := M) g r s α T hb_good
  have hKE := hKE_bound T ⟨hb_pou, hb_good⟩ hF2_diff
  have hKE_X_i :
      ‖fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)) X_i
                (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤
        K_E * (V + Fnorm + I2norm) := by
    rw [h_fderiv_eq]
    exact hKE
  -- ‖X_i b‖ ≤ C_X.
  have h_X_i_b_le : ‖X_i b‖ ≤ C_X := by
    change ‖smoothOrthoFrame (I := I) g b i b‖ ≤ C_X
    exact hCX_bound ⟨hb_pou, hb_good⟩
  -- ‖covApply ∇ X_i T b‖ bound via chartCD.
  have h_covApply_bound :
      ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X_i (fun y : M => T.toSection y) b‖ ≤
        C_cov * const_Mb * (Fnorm * C_X + C_rev * V) := by
    set Tsec : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b' : M => TensorRSSpace r s I b'⟯ := T.toSection with hTsec_def
    have hcov_apply :
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X_i (fun y : M => T.toSection y) b =
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun (fun y : M => T.toSection y) b
            (X_i b) := rfl
    rw [hcov_apply]
    obtain ⟨Xext, hXext_at_b⟩ :=
      ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
        (n := ⊤) b (X_i b)
    have hXext_toFun_b : Xext.toFun b = X_i b := hXext_at_b
    have h_agree :
        chartTensorRSCovariantDerivative (I := I) r s g α
            (fun y : M => Tsec.toFun y) Xext.toFun b =
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun y : M => Tsec.toFun y) b (Xext.toFun b) :=
      chartTensorRSCovariantDerivative_eq_abstract (I := I) (M := M)
        g r s α Tsec Xext (b := b) hb_good
    rw [hXext_toFun_b] at h_agree
    have hTsec_toFun_eq :
        (fun y : M => Tsec.toFun y) = (fun y : M => T.toSection y) := rfl
    rw [hTsec_toFun_eq] at h_agree
    rw [← h_agree]
    have h_chartCD_bound :=
      hCcov_bound (b := b) hb_pou (fun y : M => Tsec.toFun y) Xext.toFun
    rw [hXext_toFun_b, hTsec_toFun_eq] at h_chartCD_bound
    -- h_chartCD_bound: ‖chartCD T X_i b‖ ≤ C_cov · M(X_i,b)^(max r s) · (F · ‖X_i b‖ + ‖T b‖).
    have h_max_le : max (1 + ‖X_i b‖) 1 ≤ max (1 + C_X) 1 :=
      max_le_max (by linarith) (le_refl _)
    have h_max_nn : (0 : ℝ) ≤ max (1 + ‖X_i b‖) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    have h_pow_le :
        (max (1 + ‖X_i b‖) 1) ^ (max r s) ≤ const_Mb := by
      rw [hconst_Mb_def]
      exact pow_le_pow_left₀ h_max_nn h_max_le _
    have h_pow_nn : 0 ≤ (max (1 + ‖X_i b‖) 1) ^ (max r s) := pow_nonneg h_max_nn _
    -- ‖T b‖ ≤ C_rev · V.
    have h_T_b_le : ‖T.toSection b‖ ≤ C_rev * V := by
      have h := hCrev_bound b hb_pou (T.toSection b)
      change ‖T.toSection b‖ ≤ _ at h
      change ‖T.toSection b‖ ≤ C_rev * V
      exact h
    -- F · ‖X_i b‖ + ‖T b‖ ≤ F · C_X + C_rev · V.
    have h_inner_le :
        Fnorm * ‖X_i b‖ + ‖T.toSection b‖ ≤ Fnorm * C_X + C_rev * V := by
      have h_a : Fnorm * ‖X_i b‖ ≤ Fnorm * C_X :=
        mul_le_mul_of_nonneg_left h_X_i_b_le hF_nn
      linarith
    have h_inner_nn : 0 ≤ Fnorm * ‖X_i b‖ + ‖T.toSection b‖ := by
      have h_a : 0 ≤ Fnorm * ‖X_i b‖ := mul_nonneg hF_nn (norm_nonneg _)
      have h_b : 0 ≤ ‖T.toSection b‖ := norm_nonneg _
      linarith
    have h_step1 :
        C_cov * (max (1 + ‖X_i b‖) 1) ^ (max r s) *
            (Fnorm * ‖X_i b‖ + ‖T.toSection b‖) ≤
          C_cov * const_Mb * (Fnorm * C_X + C_rev * V) := by
      have h_a1 :
          C_cov * (max (1 + ‖X_i b‖) 1) ^ (max r s) ≤ C_cov * const_Mb :=
        mul_le_mul_of_nonneg_left h_pow_le hCcov_nn
      have h_a1_nn : 0 ≤ C_cov * (max (1 + ‖X_i b‖) 1) ^ (max r s) :=
        mul_nonneg hCcov_nn h_pow_nn
      have h_a2 :
          C_cov * (max (1 + ‖X_i b‖) 1) ^ (max r s) *
              (Fnorm * ‖X_i b‖ + ‖T.toSection b‖) ≤
            C_cov * const_Mb *
              (Fnorm * ‖X_i b‖ + ‖T.toSection b‖) :=
        mul_le_mul_of_nonneg_right h_a1 h_inner_nn
      have h_a3_nn : 0 ≤ C_cov * const_Mb := mul_nonneg hCcov_nn hconst_Mb_nn
      have h_a4 :
          C_cov * const_Mb *
              (Fnorm * ‖X_i b‖ + ‖T.toSection b‖) ≤
            C_cov * const_Mb *
              (Fnorm * C_X + C_rev * V) :=
        mul_le_mul_of_nonneg_left h_inner_le h_a3_nn
      linarith
    exact le_trans h_chartCD_bound h_step1
  -- Now derive chartFrameData ≤ K_lin · (V + F + I2).
  unfold chartFrameData
  set Mb_term : ℝ := (max (1 + ‖X_i b‖) 1) ^ (max r s) with hMb_term_def
  have hMb_term_nn : 0 ≤ Mb_term := by
    have : 0 ≤ max (1 + ‖X_i b‖) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  have hMb_term_le : Mb_term ≤ const_Mb := by
    rw [hconst_Mb_def, hMb_term_def]
    have h_max_le : max (1 + ‖X_i b‖) 1 ≤ max (1 + C_X) 1 :=
      max_le_max (by linarith [h_X_i_b_le]) (le_refl _)
    have h_max_nn : (0 : ℝ) ≤ max (1 + ‖X_i b‖) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    exact pow_le_pow_left₀ h_max_nn h_max_le _
  set FderivStuff : ℝ :=
    ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g b i) (fun y : M => T.toSection y)) ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ with hFderivStuff_def
  set CovValStuff : ℝ :=
    ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g b i) (fun y : M => T.toSection y) b‖
    with hCovValStuff_def
  have hFderivStuff_nn : 0 ≤ FderivStuff := norm_nonneg _
  have hCovValStuff_nn : 0 ≤ CovValStuff := norm_nonneg _
  have hFderivStuff_le : FderivStuff ≤ K_E * (V + Fnorm + I2norm) := hKE_X_i
  have hCovValStuff_le :
      CovValStuff ≤ C_cov * const_Mb * (Fnorm * C_X + C_rev * V) :=
    h_covApply_bound
  -- The goal: Mb_term · (FderivStuff · ‖X_i b‖ + CovValStuff) ≤ K_lin · (V+F+I2).
  -- Inner sum bound.
  have hF_X_le : FderivStuff * ‖X_i b‖ ≤ (K_E * C_X) * (V + Fnorm + I2norm) := by
    have h_a : FderivStuff * ‖X_i b‖ ≤ (K_E * (V + Fnorm + I2norm)) * ‖X_i b‖ :=
      mul_le_mul_of_nonneg_right hFderivStuff_le (norm_nonneg _)
    have h_b : (K_E * (V + Fnorm + I2norm)) * ‖X_i b‖ ≤
        (K_E * (V + Fnorm + I2norm)) * C_X :=
      mul_le_mul_of_nonneg_left h_X_i_b_le
        (mul_nonneg hKE_nn hVFI2_nn)
    have h_c : (K_E * (V + Fnorm + I2norm)) * C_X = (K_E * C_X) * (V + Fnorm + I2norm) := by ring
    linarith
  -- (F · C_X + C_rev · V) ≤ (C_X + C_rev) · (V+F+I2).
  have h_FX_CrevV_le_VFI2 :
      Fnorm * C_X + C_rev * V ≤ (C_X + C_rev) * (V + Fnorm + I2norm) := by
    have h_a : Fnorm * C_X ≤ C_X * (V + Fnorm + I2norm) := by
      have h_aa : Fnorm * C_X = C_X * Fnorm := by ring
      have h_ab : C_X * Fnorm ≤ C_X * (V + Fnorm + I2norm) :=
        mul_le_mul_of_nonneg_left (by linarith) hCX_nn
      linarith
    have h_b : C_rev * V ≤ C_rev * (V + Fnorm + I2norm) :=
      mul_le_mul_of_nonneg_left (by linarith) hCrev_nn
    have h_c : C_X * (V + Fnorm + I2norm) + C_rev * (V + Fnorm + I2norm) =
        (C_X + C_rev) * (V + Fnorm + I2norm) := by ring
    linarith
  -- CovValStuff ≤ C_cov · const_Mb · (C_X + C_rev) · (V+F+I2).
  have hCcov_constMb_nn : 0 ≤ C_cov * const_Mb := mul_nonneg hCcov_nn hconst_Mb_nn
  have hCovValStuff_VFI2_le :
      CovValStuff ≤ C_cov * const_Mb * (C_X + C_rev) * (V + Fnorm + I2norm) := by
    refine le_trans hCovValStuff_le ?_
    have h_step :
        C_cov * const_Mb * (Fnorm * C_X + C_rev * V) ≤
          C_cov * const_Mb * ((C_X + C_rev) * (V + Fnorm + I2norm)) :=
      mul_le_mul_of_nonneg_left h_FX_CrevV_le_VFI2 hCcov_constMb_nn
    have h_eq : C_cov * const_Mb * ((C_X + C_rev) * (V + Fnorm + I2norm)) =
        C_cov * const_Mb * (C_X + C_rev) * (V + Fnorm + I2norm) := by ring
    linarith
  -- FderivStuff · ‖X b‖ + CovValStuff ≤
  --   K_E · C_X · (V+F+I2) + C_cov · const_Mb · (C_X + C_rev) · (V+F+I2).
  have h_inner_VFI2 :
      FderivStuff * ‖X_i b‖ + CovValStuff ≤
        (K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm) := by
    have h_distrib :
        (K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm) =
          (K_E * C_X) * (V + Fnorm + I2norm) +
            C_cov * const_Mb * (C_X + C_rev) * (V + Fnorm + I2norm) := by ring
    linarith
  have h_inner_VFI2_nn :
      0 ≤ (K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm) := by
    have h_a : 0 ≤ K_E * C_X := mul_nonneg hKE_nn hCX_nn
    have h_b : 0 ≤ C_cov * const_Mb * (C_X + C_rev) := by
      have h_c : 0 ≤ C_X + C_rev := by linarith
      exact mul_nonneg hCcov_constMb_nn h_c
    have h_sum_nn : 0 ≤ K_E * C_X + C_cov * const_Mb * (C_X + C_rev) := by linarith
    exact mul_nonneg h_sum_nn hVFI2_nn
  have h_inner_nn : 0 ≤ FderivStuff * ‖X_i b‖ + CovValStuff := by
    have h_a : 0 ≤ FderivStuff * ‖X_i b‖ := mul_nonneg hFderivStuff_nn (norm_nonneg _)
    linarith
  -- Mb_term · (...) ≤ const_Mb · (...) ≤ const_Mb · ((K_E·C_X + C_cov·const_Mb·(C_X+C_rev)) · (V+F+I2))
  --              = K_lin · (V+F+I2).
  have h_step1 :
      Mb_term * (FderivStuff * ‖X_i b‖ + CovValStuff) ≤
        const_Mb * (FderivStuff * ‖X_i b‖ + CovValStuff) :=
    mul_le_mul_of_nonneg_right hMb_term_le h_inner_nn
  have h_step2 :
      const_Mb * (FderivStuff * ‖X_i b‖ + CovValStuff) ≤
        const_Mb *
          ((K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm)) :=
    mul_le_mul_of_nonneg_left h_inner_VFI2 hconst_Mb_nn
  have h_step3 :
      const_Mb *
          ((K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm)) =
        K_lin * (V + Fnorm + I2norm) := by
    rw [hK_lin_def]; ring
  have h_chain :
      Mb_term * (FderivStuff * ‖X_i b‖ + CovValStuff) ≤
        K_lin * (V + Fnorm + I2norm) := by
    calc Mb_term * (FderivStuff * ‖X_i b‖ + CovValStuff)
        ≤ const_Mb * (FderivStuff * ‖X_i b‖ + CovValStuff) := h_step1
      _ ≤ const_Mb *
            ((K_E * C_X + C_cov * const_Mb * (C_X + C_rev)) * (V + Fnorm + I2norm)) := h_step2
      _ = K_lin * (V + Fnorm + I2norm) := h_step3
  exact h_chain

/-! ## Bound on `secondAppChartData_i` -/

/-- Per-frame-index bound for `secondAppChartData T b i` by `K · (V + F + I2)`. -/
private lemma secondAppChartData_le_VFI2
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        secondAppChartData (I := I) g r s α
            (fun y : M => T.toSection y) b i ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Uniform bound on ‖smoothOrthoFrame g b i b‖.
  obtain ⟨C_X, hCX_nn, hCX_bound⟩ :=
    smoothOrthoFrame_norm_uniform_bound (I := I) (M := M)
      h_atlas h_atlas_strong g α i
  -- Uniform bound on ‖(LeviCivita g) X_i b (X_i b)‖ via leviCivita_X_X.
  obtain ⟨C_LX, hCLX_nn, hCLX_bound⟩ :=
    leviCivita_X_X_norm_bound_on_pouTsupport (I := I) (M := M) h_atlas g α
  -- Sub-E (with B := chartFrameNormGlobalSmooth, used to bound the
  -- chartE_section_repr derivative of X_i since X_i =ᶠ Bg).
  -- We don't actually need Sub-E for secondAppChartData — only the value
  -- ‖v_i‖ matters, not the section derivative.
  -- chartE_section_repr derivative of chartFrameNormGlobalSmooth is a fixed
  -- smooth function, so its fderiv-norm is bounded over the POU tsupport.
  -- Combined with ‖X_i b‖ ≤ C_X via the eventually-equal lemma, we get
  -- ‖v_i‖ ≤ uniform constant.
  -- We'll extract a single uniform C_v.
  -- Use leviCivita_X_X_norm_bound_on_pouTsupport with X := chartFrameNormGlobalSmooth g α i;
  -- the bound is in terms of ‖fderiv (chartE_section_repr α X.toFun ∘ symm)‖ and ‖X b‖,
  -- both uniformly bounded over the POU tsupport (X is a fixed smooth section).
  -- The transfer X_i =ᶠ Bg gives:
  -- ‖(LeviCivita g) X_i b (X_i b)‖ = ‖(LeviCivita g) Bg.toFun b (Bg.toFun b)‖ (CovariantDerivative locality).
  -- For X := Bg, the leviCivita_X_X bound gives ‖v_i‖ ≤ C_LX · (uniform stuff).
  -- We compute uniform bounds on (uniform stuff) below.
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
  -- Uniform bound on `‖Bg.toFun b‖`.
  obtain ⟨C_Bg, hCBg_nn, hCBg_bound⟩ :=
    chartFrameNormGlobalSmooth_norm_bound (I := I) (M := M) h_atlas g α i
  -- Uniform bound on `‖fderiv (chartE_section_repr α Bg.toFun ∘ symm) (extChartAt α b)‖`
  -- over the POU tsupport.
  -- Since Bg is a fixed smooth section, chartE_section_repr α Bg.toFun is
  -- C^∞ on the chart source. Its composition with symm is C^∞ on chart-target image
  -- of chart source. Hence its fderiv has bounded op-norm there.
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  -- Build the uniform bound on ‖fderiv (chartE_section_repr α Bg.toFun ∘ symm)‖.
  -- Use the same pattern as IntrinsicPieceFderivBound's u_and_fderiv_u_bound.
  obtain ⟨C_dBg, hCdBg_nn, hCdBg_bound⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K_set,
        ‖fderiv ℝ
          (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C := by
    have hU_open : IsOpen
        ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
      chartLeviCivitaGoodSet_image_isOpen (I := I) α
    have hBg_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun y : M => TangentSpace I y) x (Bg.toFun x)) := Bg.contMDiff
    have hBg_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (Bg.toFun : Π x : M, TangentSpace I x))
        (chartLeviCivitaGoodSet (I := I) α) := hBg_total.contMDiffOn
    have hu_cd : ContDiffOn ℝ ∞
        (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm)
        ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
      chartE_pullback_contDiffOn_goodSet (I := I) α hBg_on
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    have hfd_cd : ContDiffOn ℝ ∞
        (fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm))
        ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
      hu_cd.fderiv_of_isOpen hU_open h_le
    have hcont_fd : ContinuousOn (fun y : E =>
        ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm) y‖)
        ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
      continuous_norm.comp_continuousOn hfd_cd.continuousOn
    -- Map K_set into the chart-target image via extChartAt.
    have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
    have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
      have h_eq := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
      intro y hy
      rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
      exact hK_sub hy
    have hmaps : Set.MapsTo (extChartAt I α) K_set
        ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
      fun b hb => ⟨b, hK_sub_good hb, rfl⟩
    have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
      (hφ_cm.continuousOn).mono hK_sub
    have hcont_fd_M : ContinuousOn (fun b : M =>
        ‖fderiv ℝ
          (chartE_section_repr (I := I) α Bg.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖) K_set :=
      hcont_fd.comp hφ_cont hmaps
    obtain ⟨Cfd, hCfd_mem⟩ := hK_compact.bddAbove_image hcont_fd_M
    refine ⟨max Cfd 0, le_max_right _ _, ?_⟩
    intro b hb
    have h := hCfd_mem ⟨b, hb, rfl⟩
    exact le_trans h (le_max_left _ _)
  -- Uniform bound on ‖v_i‖ where v_i = (LeviCivita g) X_i b (X_i b).
  -- By the eventually-equal X_i =ᶠ Bg.toFun and CovariantDerivative locality,
  -- (LeviCivita g) X_i b = (LeviCivita g) Bg.toFun b as CLMs at b.
  -- Then (LeviCivita g) X_i b (X_i b) = (LeviCivita g) Bg.toFun b (X_i b)
  --                                    = (LeviCivita g) Bg.toFun b (Bg.toFun b)
  --                                       (since X_i b = Bg.toFun b).
  -- Apply leviCivita_X_X_norm_bound_on_pouTsupport:
  --   ‖(LeviCivita g) Bg.toFun b (Bg.toFun b)‖ ≤ C_LX · (‖fderiv ...‖ · ‖Bg b‖ + ‖Bg b‖²).
  -- The RHS is uniformly bounded by C_LX · (C_dBg · C_Bg + C_Bg²) =: C_v.
  set C_v : ℝ := C_LX * (C_dBg * C_Bg + C_Bg ^ 2) with hC_v_def
  have hC_v_nn : 0 ≤ C_v := by
    have h_a : 0 ≤ C_dBg * C_Bg := mul_nonneg hCdBg_nn hCBg_nn
    have h_b : 0 ≤ C_Bg ^ 2 := sq_nonneg _
    have h_c : 0 ≤ C_dBg * C_Bg + C_Bg ^ 2 := by linarith
    exact mul_nonneg hCLX_nn h_c
  set const_Mv : ℝ := (max (1 + C_v) 1) ^ (max r s) with hconst_Mv_def
  have hconst_Mv_nn : 0 ≤ const_Mv := by
    have : 0 ≤ max (1 + C_v) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  -- Reverse fiber norm: ‖T b‖ ≤ C_rev · V.
  obtain ⟨C_rev, hCrev_pos, hCrev_bound⟩ :=
    tensorRSSpace_norm_le_chartRepr_norm_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK_compact) (hKsub := hK_sub)
  have hCrev_nn : 0 ≤ C_rev := le_of_lt hCrev_pos
  -- Headline constant: K = const_Mv · (C_v + C_rev).
  set K_lin : ℝ := const_Mv * (C_v + C_rev) with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := by
    have h_a : 0 ≤ C_v + C_rev := by linarith
    exact mul_nonneg hconst_Mv_nn h_a
  refine ⟨K_lin, hK_lin_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  set X_i : Π b' : M, TangentSpace I b' :=
    fun b' => smoothOrthoFrame (I := I) g b i b' with hX_i_def
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ with hV_def
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFnorm_def
  set I2norm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2norm_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ Fnorm := norm_nonneg _
  have hI2_nn : 0 ≤ I2norm := norm_nonneg _
  have hVFI2_nn : 0 ≤ V + Fnorm + I2norm := by linarith
  -- v_i = (LeviCivita g) X_i b (X_i b).
  set v_i : TangentSpace I b :=
    (LeviCivita (I := I) g).toFun X_i b (X_i b) with hv_i_def
  -- Bound ‖v_i‖ ≤ C_v.
  -- Step 1: X_i b = Bg.toFun b.
  have hX_i_eq_Bg : X_i b = Bg.toFun b := by
    change smoothOrthoFrame (I := I) g b i b = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
    exact smoothOrthoFrame_eq_chartFrameNormGlobalSmooth_at_b (I := I) (M := M)
      h_atlas h_atlas_strong g α i ⟨hb_pou, hb_good⟩
  -- Step 2: X_i =ᶠ Bg.toFun near b.
  have h_evt_X : X_i =ᶠ[𝓝 b] Bg.toFun :=
    smoothOrthoFrame_eventuallyEq_at_b (I := I) (M := M)
      h_atlas h_atlas_strong g α i ⟨hb_pou, hb_good⟩
  -- Step 3: (LeviCivita g).toFun X_i b = (LeviCivita g).toFun Bg.toFun b
  --         (using CovariantDerivative locality in the section argument).
  have hX_i_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (X_i y)) b := by
    have h_cm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (smoothOrthoFrame (I := I) g b i)) :=
      smoothOrthoFrame_smooth (I := I) g b i
    exact (h_cm.contMDiffAt).mdifferentiableAt (by simp)
  have hBg_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (Bg.toFun y)) b :=
    (Bg.contMDiff b).mdifferentiableAt (by simp)
  have h_LC_eq : (LeviCivita (I := I) g).toFun X_i b =
      (LeviCivita (I := I) g).toFun Bg.toFun b :=
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hX_i_diff hBg_diff (by simp) h_evt_X
  -- Step 4: v_i = (LeviCivita g) Bg.toFun b (Bg.toFun b).
  have hv_i_eq : v_i = (LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b) := by
    rw [hv_i_def, h_LC_eq, hX_i_eq_Bg]
  -- Step 5: apply leviCivita_X_X_norm_bound.
  have h_v_bound :
      ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖ ≤
        C_LX *
          (‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
            + ‖Bg.toFun b‖ ^ 2) := hCLX_bound hb_pou Bg
  -- Step 6: bound ‖Bg b‖ ≤ C_Bg and ‖fderiv ...‖ ≤ C_dBg, square.
  have h_Bg_b_le : ‖Bg.toFun b‖ ≤ C_Bg := hCBg_bound b hb_pou
  have h_dBg_le :
      ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ ≤ C_dBg :=
    hCdBg_bound b hb_pou
  have h_Bg_nn : 0 ≤ ‖Bg.toFun b‖ := norm_nonneg _
  have h_dBg_nn : 0 ≤ ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
      (extChartAt I α).symm) (extChartAt I α b)‖ := norm_nonneg _
  have h_v_bound_C :
      ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖ ≤ C_v := by
    refine le_trans h_v_bound ?_
    rw [hC_v_def]
    have h_a : ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖ ≤
          C_dBg * C_Bg := by
      have h_aa := mul_le_mul_of_nonneg_right h_dBg_le h_Bg_nn
      have h_ab := mul_le_mul_of_nonneg_left h_Bg_b_le hCdBg_nn
      linarith
    have h_b : ‖Bg.toFun b‖ ^ 2 ≤ C_Bg ^ 2 := by
      exact sq_le_sq' (by linarith [h_Bg_nn]) h_Bg_b_le
    have h_sum_le :
        ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
            (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
          + ‖Bg.toFun b‖ ^ 2 ≤ C_dBg * C_Bg + C_Bg ^ 2 := by linarith
    have h_sum_nn :
        0 ≤ ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
            (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
          + ‖Bg.toFun b‖ ^ 2 := by
      have h_a := mul_nonneg h_dBg_nn h_Bg_nn
      have h_b := sq_nonneg ‖Bg.toFun b‖
      linarith
    exact mul_le_mul_of_nonneg_left h_sum_le hCLX_nn
  have h_v_i_norm_bound : ‖v_i‖ ≤ C_v := by
    rw [hv_i_eq]
    exact h_v_bound_C
  -- Bound ‖T b‖ ≤ C_rev · V.
  have h_T_b_le : ‖T.toSection b‖ ≤ C_rev * V := by
    have h := hCrev_bound b hb_pou (T.toSection b)
    change ‖T.toSection b‖ ≤ _ at h
    change ‖T.toSection b‖ ≤ C_rev * V
    exact h
  -- Now bound secondAppChartData.
  unfold secondAppChartData
  -- secondAppChartData = M_v^(max r s) · (F · ‖v_i‖ + ‖T b‖)
  -- where M_v = max (1 + ‖v_i‖) 1.
  set Mv_term : ℝ := (max (1 + ‖v_i‖) 1) ^ (max r s) with hMv_term_def
  set Inner : ℝ :=
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ * ‖v_i‖ + ‖T.toSection b‖ with hInner_def
  -- Mv_term ≤ const_Mv.
  have h_Mv_le : Mv_term ≤ const_Mv := by
    rw [hMv_term_def, hconst_Mv_def]
    have h_a : max (1 + ‖v_i‖) 1 ≤ max (1 + C_v) 1 :=
      max_le_max (by linarith [h_v_i_norm_bound]) (le_refl _)
    have h_b : (0 : ℝ) ≤ max (1 + ‖v_i‖) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    exact pow_le_pow_left₀ h_b h_a _
  have hMv_term_nn : 0 ≤ Mv_term := by
    have : 0 ≤ max (1 + ‖v_i‖) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  -- Inner ≤ (C_v + C_rev) · (V + F + I2).
  have h_Inner_le : Inner ≤ (C_v + C_rev) * (V + Fnorm + I2norm) := by
    rw [hInner_def]
    have h_a : Fnorm * ‖v_i‖ ≤ Fnorm * C_v :=
      mul_le_mul_of_nonneg_left h_v_i_norm_bound hF_nn
    have h_b : Fnorm * C_v ≤ C_v * (V + Fnorm + I2norm) := by
      have h_ba : Fnorm * C_v = C_v * Fnorm := by ring
      have h_bb : C_v * Fnorm ≤ C_v * (V + Fnorm + I2norm) :=
        mul_le_mul_of_nonneg_left (by linarith) hC_v_nn
      linarith
    have h_c : ‖T.toSection b‖ ≤ C_rev * (V + Fnorm + I2norm) := by
      have h_cc : C_rev * V ≤ C_rev * (V + Fnorm + I2norm) :=
        mul_le_mul_of_nonneg_left (by linarith) hCrev_nn
      linarith
    have h_d : C_v * (V + Fnorm + I2norm) + C_rev * (V + Fnorm + I2norm) =
        (C_v + C_rev) * (V + Fnorm + I2norm) := by ring
    linarith
  have hInner_nn : 0 ≤ Inner := by
    rw [hInner_def]
    have h_a : 0 ≤ Fnorm * ‖v_i‖ := mul_nonneg hF_nn (norm_nonneg _)
    have h_b : 0 ≤ ‖T.toSection b‖ := norm_nonneg _
    linarith
  -- Chain: Mv_term · Inner ≤ const_Mv · Inner ≤ const_Mv · (C_v + C_rev) · (V+F+I2) = K_lin · (V+F+I2).
  have h_step1 : Mv_term * Inner ≤ const_Mv * Inner :=
    mul_le_mul_of_nonneg_right h_Mv_le hInner_nn
  have h_step2 : const_Mv * Inner ≤
      const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) :=
    mul_le_mul_of_nonneg_left h_Inner_le hconst_Mv_nn
  have h_step3 :
      const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) = K_lin * (V + Fnorm + I2norm) := by
    rw [hK_lin_def]; ring
  calc Mv_term * Inner
      ≤ const_Mv * Inner := h_step1
    _ ≤ const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) := h_step2
    _ = K_lin * (V + Fnorm + I2norm) := h_step3

/-! ## Universal chart-data bound (constant independent of T) -/

/-- `rawTensorConnLap_pointwise_bound_chart_data` with the constant `C` chosen
universally in `T`. The argument structure is restructured so the existential
binds before the universal `T`. -/
private lemma rawTensorConnLap_pointwise_bound_chart_data_uniform_in_T
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        chartLeviCivitaGoodSet (I := I) α →
          ‖rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b‖ ≤
            C * ((∑ i : Fin (Module.finrank ℝ E),
                chartFrameData (I := I) g r s α
                  (fun y : M => T.toSection y) b i) +
              ∑ i : Fin (Module.finrank ℝ E),
                secondAppChartData (I := I) g r s α
                  (fun y : M => T.toSection y) b i) := by
  classical
  obtain ⟨C_cov, hCcov_nn, hCcov_bound⟩ :=
    chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport
      (I := I) (M := M) h_atlas g r s α
  obtain ⟨C_2nd, hC2nd_nn, hC2nd_bound⟩ :=
    rawTensorConnLap_2ndApplication_opNorm_bound
      (I := I) (M := M) h_atlas g r s α
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  refine ⟨max C_cov C_2nd, le_max_of_le_left hCcov_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  set N : ℕ := Module.finrank ℝ E with hN_def
  -- Chart expansion (Step 1).
  have h_chart_expand :=
    rawTensorConnLap_eq_chart (I := I) (M := M) g r s α T.toSection hb_good
  -- Each chartCD piece bounded by C_cov · chartFrameData_i.
  have h_chartPiece_le : ∀ i : Fin N,
      ‖chartTensorRSCovariantDerivative (I := I) r s g α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y))
          (smoothOrthoFrame (I := I) g b i) b‖ ≤
        C_cov * chartFrameData (I := I) g r s α
          (fun y : M => T.toSection y) b i := by
    intro i
    have h_bound := hCcov_bound (b := b) hb_pou
      (T := covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y))
      (X := smoothOrthoFrame (I := I) g b i)
    unfold chartFrameData
    have h_rew :
        C_cov * (max (1 + ‖smoothOrthoFrame (I := I) g b i b‖) 1) ^ (max r s) *
            (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i)
                  (fun y : M => T.toSection y)) ∘
                (extChartAt I α).symm) (extChartAt I α b)‖ *
              ‖smoothOrthoFrame (I := I) g b i b‖
              + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i)
                  (fun y : M => T.toSection y) b‖) =
          C_cov * ((max (1 + ‖smoothOrthoFrame (I := I) g b i b‖) 1) ^ (max r s) *
            (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i)
                  (fun y : M => T.toSection y)) ∘
                (extChartAt I α).symm) (extChartAt I α b)‖ *
              ‖smoothOrthoFrame (I := I) g b i b‖
              + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i)
                  (fun y : M => T.toSection y) b‖)) := by ring
    rw [h_rew] at h_bound
    exact h_bound
  -- Each LeviCivita piece bounded by C_2nd · secondAppChartData_i.
  have h_LCPiece_le : ∀ i : Fin N,
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun (fun y : M => T.toSection y) b
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g b i) b
          (smoothOrthoFrame (I := I) g b i b))‖ ≤
        C_2nd * secondAppChartData (I := I) g r s α
          (fun y : M => T.toSection y) b i := by
    intro i
    set Xi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothOrthoFrame (I := I) g b i,
        smoothOrthoFrame_smooth (I := I) g b i⟩ with hXi_def
    have h := hC2nd_bound (b := b) hb_pou T.toSection Xi
    have hXi_toFun : Xi.toFun = smoothOrthoFrame (I := I) g b i := rfl
    rw [hXi_toFun] at h
    unfold secondAppChartData
    have h_assoc :
        C_2nd *
          (max (1 +
            ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b)‖) 1) ^ (max r s) *
          (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
              T.toSection.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ *
              ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b)‖
            + ‖T.toSection.toFun b‖) =
          C_2nd * ((max (1 +
            ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b)‖) 1) ^ (max r s) *
            (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                T.toSection.toFun ∘
                (extChartAt I α).symm) (extChartAt I α b)‖ *
                ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g b i) b
                  (smoothOrthoFrame (I := I) g b i b)‖
              + ‖T.toSection.toFun b‖)) := by ring
    rw [h_assoc] at h
    -- Note T.toSection.toFun = fun y => T.toSection y (definitionally).
    exact h
  -- Now combine via the chart expansion.
  set chartPiece : Fin N → ℝ := fun i =>
      ‖chartTensorRSCovariantDerivative (I := I) r s g α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g b i)
          (fun y : M => T.toSection y))
        (smoothOrthoFrame (I := I) g b i) b‖ with hChartPiece_def
  set LCPiece : Fin N → ℝ := fun i =>
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g b i) b
          (smoothOrthoFrame (I := I) g b i b))‖ with hLCPiece_def
  have h_lhs_le_sum :
      ‖rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b‖ ≤
        ∑ i : Fin N, (chartPiece i + LCPiece i) := by
    -- `T.toSection.toFun = (fun y => T.toSection y)` definitionally.
    change ‖rawTensorConnLap (I := I) g r s T.toSection.toFun b‖ ≤ _
    rw [h_chart_expand]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i _
    exact norm_sub_le _ _
  -- chartFrameData_i and secondAppChartData_i sums.
  set S1 : ℝ := ∑ i : Fin N, chartFrameData (I := I) g r s α
      (fun y : M => T.toSection y) b i with hS1_def
  set S2 : ℝ := ∑ i : Fin N, secondAppChartData (I := I) g r s α
      (fun y : M => T.toSection y) b i with hS2_def
  have hS1_nn : 0 ≤ S1 :=
    Finset.sum_nonneg (fun i _ => chartFrameData_nonneg
      (I := I) g r s α (fun y : M => T.toSection y) b i)
  have hS2_nn : 0 ≤ S2 :=
    Finset.sum_nonneg (fun i _ => secondAppChartData_nonneg
      (I := I) g r s α (fun y : M => T.toSection y) b i)
  -- Bound Σ chartPiece + LCPiece by C_cov · S1 + C_2nd · S2.
  have h_sum_le_split :
      ∑ i : Fin N, (chartPiece i + LCPiece i) ≤ C_cov * S1 + C_2nd * S2 := by
    calc ∑ i : Fin N, (chartPiece i + LCPiece i)
        = (∑ i : Fin N, chartPiece i) + (∑ i : Fin N, LCPiece i) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i : Fin N, C_cov * chartFrameData (I := I) g r s α
              (fun y : M => T.toSection y) b i) +
            (∑ i : Fin N, C_2nd * secondAppChartData (I := I) g r s α
              (fun y : M => T.toSection y) b i) := by
          have h_a : ∑ i : Fin N, chartPiece i ≤
              ∑ i : Fin N, C_cov * chartFrameData (I := I) g r s α
                (fun y : M => T.toSection y) b i :=
            Finset.sum_le_sum (fun i _ => h_chartPiece_le i)
          have h_b : ∑ i : Fin N, LCPiece i ≤
              ∑ i : Fin N, C_2nd * secondAppChartData (I := I) g r s α
                (fun y : M => T.toSection y) b i :=
            Finset.sum_le_sum (fun i _ => h_LCPiece_le i)
          linarith
      _ = C_cov * S1 + C_2nd * S2 := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Bound C_cov · S1 + C_2nd · S2 by max · (S1 + S2).
  have h_combined :
      C_cov * S1 + C_2nd * S2 ≤ max C_cov C_2nd * (S1 + S2) := by
    have h_a : C_cov * S1 ≤ max C_cov C_2nd * S1 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS1_nn
    have h_b : C_2nd * S2 ≤ max C_cov C_2nd * S2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hS2_nn
    have h_d : max C_cov C_2nd * (S1 + S2) =
        max C_cov C_2nd * S1 + max C_cov C_2nd * S2 := by ring
    linarith
  calc ‖rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b‖
      ≤ ∑ i : Fin N, (chartPiece i + LCPiece i) := h_lhs_le_sum
    _ ≤ C_cov * S1 + C_2nd * S2 := h_sum_le_split
    _ ≤ max C_cov C_2nd * (S1 + S2) := h_combined

/-! ## Headline -/

/-- **Pointwise squared op-norm bound for `rawTensorConnLap` by the chart-pulled
representation data.** -/
theorem rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖rawTensorConnLap (I := I) g r s
            (fun y : M => T.toSection y) b‖ ^ 2 ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ ^ 2 +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ ^ 2 +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ ^ 2) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Combined chart-data-only bound.
  -- We need to supply a smooth section to `rawTensorConnLap_pointwise_bound_chart_data`;
  -- the theorem takes `T` as a ContMDiffSection (not SmoothCcTensor). For a given
  -- SmoothCcTensor S, S.toSection is a ContMDiffSection.
  -- Per-i chartFrameData bound.
  have h_cFD_choose : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        chartFrameData (I := I) g r s α
            (fun y : M => T.toSection y) b i ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := fun i =>
    chartFrameData_le_VFI2 (I := I) (M := M)
      h_atlas h_atlas_strong g r s α i
  choose K_cFD hK_cFD_nn hK_cFD_bound using h_cFD_choose
  -- Per-i secondAppChartData bound.
  have h_sACD_choose : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        secondAppChartData (I := I) g r s α
            (fun y : M => T.toSection y) b i ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := fun i =>
    secondAppChartData_le_VFI2 (I := I) (M := M)
      h_atlas h_atlas_strong g r s α i
  choose K_sACD hK_sACD_nn hK_sACD_bound using h_sACD_choose
  -- Universal chart-data bound: C_main is T-independent.
  obtain ⟨C_main, hC_main_nn, hC_main_bound⟩ :=
    rawTensorConnLap_pointwise_bound_chart_data_uniform_in_T
      (I := I) (M := M) h_atlas g r s α
  -- Headline constant.
  set sumK : ℝ := (∑ i, K_cFD i) + (∑ i, K_sACD i) with hsumK_def
  have hsumK_nn : 0 ≤ sumK := by
    have h_a : 0 ≤ ∑ i, K_cFD i := Finset.sum_nonneg (fun i _ => hK_cFD_nn i)
    have h_b : 0 ≤ ∑ i, K_sACD i := Finset.sum_nonneg (fun i _ => hK_sACD_nn i)
    linarith
  set K_lin : ℝ := C_main * sumK with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := mul_nonneg hC_main_nn hsumK_nn
  set K_final : ℝ := 3 * K_lin ^ 2 with hK_final_def
  have hK_final_nn : 0 ≤ K_final := by
    have h_a : 0 ≤ K_lin ^ 2 := sq_nonneg _
    linarith
  refine ⟨K_final, hK_final_nn, ?_⟩
  intro T b hb
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ with hV_def
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFnorm_def
  set I2norm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2norm_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ Fnorm := norm_nonneg _
  have hI2_nn : 0 ≤ I2norm := norm_nonneg _
  have hVFI2_nn : 0 ≤ V + Fnorm + I2norm := by linarith
  -- Apply the universal chart-data bound.
  have h_main := hC_main_bound T (b := b) hb
  -- Sum: Σ chartFrameData ≤ Σ K_cFD · (V+F+I2).
  have h_sum_cFD :
      ∑ i : Fin (Module.finrank ℝ E),
          chartFrameData (I := I) g r s α (fun y : M => T.toSection y) b i ≤
        (∑ i, K_cFD i) * (V + Fnorm + I2norm) := by
    calc ∑ i, chartFrameData (I := I) g r s α (fun y : M => T.toSection y) b i
        ≤ ∑ i, K_cFD i * (V + Fnorm + I2norm) :=
          Finset.sum_le_sum (fun i _ => hK_cFD_bound i T hb)
      _ = (∑ i, K_cFD i) * (V + Fnorm + I2norm) := by rw [Finset.sum_mul]
  have h_sum_sACD :
      ∑ i : Fin (Module.finrank ℝ E),
          secondAppChartData (I := I) g r s α (fun y : M => T.toSection y) b i ≤
        (∑ i, K_sACD i) * (V + Fnorm + I2norm) := by
    calc ∑ i, secondAppChartData (I := I) g r s α (fun y : M => T.toSection y) b i
        ≤ ∑ i, K_sACD i * (V + Fnorm + I2norm) :=
          Finset.sum_le_sum (fun i _ => hK_sACD_bound i T hb)
      _ = (∑ i, K_sACD i) * (V + Fnorm + I2norm) := by rw [Finset.sum_mul]
  -- Combined: Σ + Σ ≤ ((Σ K_cFD) + (Σ K_sACD)) · (V+F+I2) = sumK · (V+F+I2).
  have h_sum_combined :
      ((∑ i : Fin (Module.finrank ℝ E),
          chartFrameData (I := I) g r s α (fun y : M => T.toSection y) b i) +
        ∑ i : Fin (Module.finrank ℝ E),
          secondAppChartData (I := I) g r s α (fun y : M => T.toSection y) b i) ≤
        sumK * (V + Fnorm + I2norm) := by
    have h_distrib : sumK * (V + Fnorm + I2norm) =
        (∑ i, K_cFD i) * (V + Fnorm + I2norm) +
          (∑ i, K_sACD i) * (V + Fnorm + I2norm) := by rw [hsumK_def]; ring
    linarith
  -- ‖raw T b‖ ≤ C_main · sumK · (V+F+I2) = K_lin · (V+F+I2).
  have h_raw_le : ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ ≤ K_lin * (V + Fnorm + I2norm) := by
    have h_step1 : ‖rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b‖ ≤ C_main * (sumK * (V + Fnorm + I2norm)) := by
      have h_sum_nn :
          0 ≤ ((∑ i : Fin (Module.finrank ℝ E),
              chartFrameData (I := I) g r s α (fun y : M => T.toSection y) b i) +
            ∑ i : Fin (Module.finrank ℝ E),
              secondAppChartData (I := I) g r s α
                (fun y : M => T.toSection y) b i) := by
        have h_a : 0 ≤ ∑ i, chartFrameData (I := I) g r s α
            (fun y : M => T.toSection y) b i :=
          Finset.sum_nonneg (fun i _ => chartFrameData_nonneg
            (I := I) g r s α (fun y : M => T.toSection y) b i)
        have h_b : 0 ≤ ∑ i, secondAppChartData (I := I) g r s α
            (fun y : M => T.toSection y) b i :=
          Finset.sum_nonneg (fun i _ => secondAppChartData_nonneg
            (I := I) g r s α (fun y : M => T.toSection y) b i)
        linarith
      have h_step :
          C_main * ((∑ i, chartFrameData (I := I) g r s α
              (fun y : M => T.toSection y) b i) +
            ∑ i, secondAppChartData (I := I) g r s α
              (fun y : M => T.toSection y) b i) ≤
            C_main * (sumK * (V + Fnorm + I2norm)) :=
        mul_le_mul_of_nonneg_left h_sum_combined hC_main_nn
      linarith
    have h_assoc : C_main * (sumK * (V + Fnorm + I2norm)) = K_lin * (V + Fnorm + I2norm) := by
      rw [hK_lin_def]; ring
    linarith
  -- Square both sides.
  have h_raw_nn : 0 ≤ ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ K_lin * (V + Fnorm + I2norm) :=
    mul_nonneg hK_lin_nn hVFI2_nn
  have h_sq : ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ ^ 2 ≤ (K_lin * (V + Fnorm + I2norm)) ^ 2 :=
    pow_le_pow_left₀ h_raw_nn h_raw_le 2
  -- (K_lin · (V+F+I2))^2 = K_lin^2 · (V+F+I2)^2 ≤ K_lin^2 · 3 · (V^2+F^2+I^2) = K_final · (...).
  have h_expand : (K_lin * (V + Fnorm + I2norm)) ^ 2 = K_lin ^ 2 * (V + Fnorm + I2norm) ^ 2 := by
    ring
  have h_sq_inner : (V + Fnorm + I2norm) ^ 2 ≤ 3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) :=
    sq_add_three_le_three_mul_sum_sq V Fnorm I2norm
  have h_K_lin_sq_nn : 0 ≤ K_lin ^ 2 := sq_nonneg _
  have h_step2 : K_lin ^ 2 * (V + Fnorm + I2norm) ^ 2 ≤
      K_lin ^ 2 * (3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2)) :=
    mul_le_mul_of_nonneg_left h_sq_inner h_K_lin_sq_nn
  have h_step3 : K_lin ^ 2 * (3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2)) =
      K_final * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) := by rw [hK_final_def]; ring
  linarith

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
#print axioms
  DifferentialGeometry.Geometry.hasChartSourceConsistentChartAt_self
end Sanity
