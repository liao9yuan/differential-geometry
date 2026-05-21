import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Integral.Connection.RawTensorConnLapPointwiseBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLap2ndApplicationOpNorm
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprFderivBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovApplyReprValueBound
import DifferentialGeometry.Integral.Connection.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Integral.Connection.IntrinsicPieceFderivBound
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Integral.Connection.TensorConnLaplacian
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
`g`, the chart at `α`, the locality hypothesis on the chart map, and the
ranks `r`, `s`; it is independent of `T` and `b`.

## Strategy

The chart-α frame trace identity `rawTensorConnLap_via_chartFrameNormGlobalSmooth`
rewrites the raw operator at `b` as

```
rawTensorConnLap g r s T b
    = rawTensorConnLap_fixedFrame g r s (chartFrameNormGlobalSmooth g α) T b
    = ∑ i, (∇^{(r,s)} (covApply ∇ B_i T) b (B_i b)
            − ∇^{(r,s)} T b ((LeviCivita g) B_i b (B_i b))),
```

where `B_i = chartFrameNormGlobalSmooth g α i` is a fixed globally smooth
tangent-bundle section. The right-hand side now references only the fixed
smooth section `B_i`, never the centre-dependent orthonormal frame.

For each frame index `i`, two per-`i` bounds:

* `fixedFrame_term1_le_VFI2` — bound on the first piece using the chart-frame
  covariant derivative operator-norm bound, the Sub-E chart-pulled `fderiv`
  bound, and the chart-pulled value bound;
* `fixedFrame_term2_le_VFI2` — bound on the second piece using
  `rawTensorConnLap_2ndApplication_opNorm_bound` and the Levi-Civita `X X`
  norm bound.

Both per-`i` bounds use only the local-constancy hypothesis on the chart map
(`HasLocallyConstantChartAt`). Summing over `i`, applying the triangle
inequality, and squaring via `(a + b + c)^2 ≤ 3 · (a^2 + b^2 + c^2)` yields
the headline.
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

/-! ## Uniform fibre-norm bound on the `fderiv` of the chart-pulled
representation of `chartFrameNormGlobalSmooth g α i` -/

/-- Uniform bound on
`‖fderiv ℝ (chartE_section_repr α B.toFun ∘ (extChartAt I α).symm) (extChartAt I α b)‖`
over the chart-`α` POU tsupport, for the fixed smooth section
`B = chartFrameNormGlobalSmooth g α i`. -/
private lemma chartFrameNormGlobalSmooth_fderiv_repr_bound
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖fderiv ℝ
            (chartE_section_repr (I := I) α
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
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

/-! ## Per-`i` bound for the first chart-frame piece -/

/-- For each frame index `i`, the norm of the first chart-frame piece
`∇^{(r,s)} (covApply ∇ B_i T) b (B_i b)` is bounded by a uniform constant
times `V + F + I2`, where `B_i = chartFrameNormGlobalSmooth g α i`. -/
private lemma fixedFrame_term1_le_VFI2
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
              (fun y : M => T.toSection y)) b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)‖ ≤
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
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
  -- Uniform bound on `‖Bg b‖` over POU tsupport.
  obtain ⟨C_Bg, hCBg_nn, hCBg_bound⟩ :=
    chartFrameNormGlobalSmooth_norm_bound (I := I) (M := M) h_atlas g α i
  set const_Mb : ℝ := (max (1 + C_Bg) 1) ^ (max r s) with hconst_Mb_def
  have hconst_Mb_nn : 0 ≤ const_Mb := by
    have : 0 ≤ max (1 + C_Bg) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  -- Sub-E fderiv bound with B := Bg.
  obtain ⟨K_E, hKE_nn, hKE_bound⟩ :=
    chart_pulled_covApply_repr_fderiv_bound
      (I := I) (M := M) h_atlas g r s α Bg
  -- Value bound on the chart-pulled representation of `covApply ∇ Bg T`.
  obtain ⟨K_V, hKV_nn, hKV_bound⟩ :=
    chart_pulled_covApply_repr_value_bound
      (I := I) (M := M) h_atlas g r s α Bg
  -- chartCD op-norm bound.
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
  -- Headline constant.
  -- The chain is: ‖term1‖
  --   ≤ C_cov · const_Mb · (FStuff · ‖Bg b‖ + ‖covT b‖)
  --   ≤ C_cov · const_Mb · (K_E · (V+F+I2) · C_Bg + C_rev · K_V · (V+F+I2))
  --   = C_cov · const_Mb · (K_E · C_Bg + C_rev · K_V) · (V+F+I2).
  set K_lin : ℝ := C_cov * const_Mb * (K_E * C_Bg + C_rev * K_V) with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := by
    have h1 : 0 ≤ K_E * C_Bg := mul_nonneg hKE_nn hCBg_nn
    have h2 : 0 ≤ C_rev * K_V := mul_nonneg hCrev_nn hKV_nn
    have h3 : 0 ≤ K_E * C_Bg + C_rev * K_V := by linarith
    have h4 : 0 ≤ C_cov * const_Mb := mul_nonneg hCcov_nn hconst_Mb_nn
    exact mul_nonneg h4 h3
  refine ⟨K_lin, hK_lin_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
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
  -- Pointwise bound on `‖Bg b‖`.
  have h_Bg_b_le : ‖Bg.toFun b‖ ≤ C_Bg := hCBg_bound b hb_pou
  -- The cov-derivative section `covApply ∇ Bg T`.
  set covT : Π b' : M, TensorRSSpace r s I b' :=
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) Bg.toFun
        (fun y : M => T.toSection y) with hcovT_def
  -- Smoothness witnesses needed to invoke `chartTensorRSCovariantDerivative_eq_abstract`.
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hBg_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (Bg.toFun : Π x : M, TangentSpace I x)) := Bg.contMDiff
  -- Smoothness of `covApply ∇ Bg T` as a tensor section, on Set.univ then at b.
  have hcovApply_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% covT) Set.univ := by
    rw [hcovT_def]
    exact covApply_contMDiffOn
      (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) hBg_total hT_plus
  have hcovT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% covT) :=
    fun y => (hcovApply_on.contMDiffAt (Filter.univ_mem))
  -- Package as a ContMDiffSection.
  set covTsec : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b' : M => TensorRSSpace r s I b'⟯ :=
    ⟨covT, hcovT_total⟩ with hcovTsec_def
  -- chartCD-vs-abstract agreement at b.
  have h_agree :
      chartTensorRSCovariantDerivative (I := I) r s g α covTsec.toFun Bg.toFun b =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun covTsec.toFun b (Bg.toFun b) :=
    chartTensorRSCovariantDerivative_eq_abstract (I := I) (M := M)
      g r s α covTsec Bg (b := b) hb_good
  have hcovTsec_toFun_eq : covTsec.toFun = covT := rfl
  rw [hcovTsec_toFun_eq] at h_agree
  -- Goal: ‖∇^{(r,s)} covT b (Bg b)‖ ≤ K_lin · (V+F+I2).
  rw [← h_agree]
  -- chartCD op-norm bound applied to T := covT, X := Bg.toFun.
  have h_chartCD_bound :=
    hCcov_bound (b := b) hb_pou covT Bg.toFun
  -- Set up subexpressions.
  set Mb_term : ℝ := (max (1 + ‖Bg.toFun b‖) 1) ^ (max r s) with hMb_term_def
  have hMb_term_nn : 0 ≤ Mb_term := by
    have : 0 ≤ max (1 + ‖Bg.toFun b‖) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  have hMb_term_le : Mb_term ≤ const_Mb := by
    rw [hconst_Mb_def, hMb_term_def]
    have h_max_le : max (1 + ‖Bg.toFun b‖) 1 ≤ max (1 + C_Bg) 1 :=
      max_le_max (by linarith [h_Bg_b_le]) (le_refl _)
    have h_max_nn : (0 : ℝ) ≤ max (1 + ‖Bg.toFun b‖) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    exact pow_le_pow_left₀ h_max_nn h_max_le _
  set FStuff : ℝ :=
    ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        covT ∘ (extChartAt I α).symm) (extChartAt I α b)‖
    with hFStuff_def
  set VStuff : ℝ := ‖covT b‖ with hVStuff_def
  have hFStuff_nn : 0 ≤ FStuff := norm_nonneg _
  have hVStuff_nn : 0 ≤ VStuff := norm_nonneg _
  -- Sub-E gives: FStuff ≤ K_E · (V + F + I2).
  have hF2_diff : DifferentiableAt ℝ
      (fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      (extChartAt I α b) :=
    fderiv_reprT_differentiableAt_chart_point (I := I) (M := M) g r s α T hb_good
  have hFStuff_le : FStuff ≤ K_E * (V + Fnorm + I2norm) := by
    rw [hFStuff_def, hcovT_def]
    exact hKE_bound T ⟨hb_pou, hb_good⟩ hF2_diff
  -- Value bound: ‖repr covT b‖ ≤ K_V · (F + V).
  have h_repr_covT_le :
      ‖tensorRSChartE_section_repr (I := I) r s α covT b‖ ≤
        K_V * (Fnorm + V) := by
    rw [hcovT_def]
    exact hKV_bound T ⟨hb_pou, hb_good⟩
  -- Reverse fiber norm: ‖covT b‖ ≤ C_rev · ‖repr covT b‖.
  have h_covT_b_le : VStuff ≤ C_rev * (K_V * (Fnorm + V)) := by
    rw [hVStuff_def]
    have h_rev := hCrev_bound b hb_pou (covT b)
    have h_step :
        C_rev * ‖tensorRSChartE_section_repr (I := I) r s α covT b‖ ≤
          C_rev * (K_V * (Fnorm + V)) :=
      mul_le_mul_of_nonneg_left h_repr_covT_le hCrev_nn
    exact le_trans h_rev h_step
  -- Inner sum.
  set Inner : ℝ := FStuff * ‖Bg.toFun b‖ + VStuff with hInner_def
  have hInner_nn : 0 ≤ Inner := by
    have h_a : 0 ≤ FStuff * ‖Bg.toFun b‖ := mul_nonneg hFStuff_nn (norm_nonneg _)
    linarith
  -- Bound Inner ≤ (K_E · C_Bg + C_rev · K_V) · (V+F+I2).
  have h_FStuff_Bg_le :
      FStuff * ‖Bg.toFun b‖ ≤ (K_E * C_Bg) * (V + Fnorm + I2norm) := by
    have h_a : FStuff * ‖Bg.toFun b‖ ≤
        (K_E * (V + Fnorm + I2norm)) * ‖Bg.toFun b‖ :=
      mul_le_mul_of_nonneg_right hFStuff_le (norm_nonneg _)
    have h_b : (K_E * (V + Fnorm + I2norm)) * ‖Bg.toFun b‖ ≤
        (K_E * (V + Fnorm + I2norm)) * C_Bg :=
      mul_le_mul_of_nonneg_left h_Bg_b_le
        (mul_nonneg hKE_nn hVFI2_nn)
    have h_c : (K_E * (V + Fnorm + I2norm)) * C_Bg =
        (K_E * C_Bg) * (V + Fnorm + I2norm) := by ring
    linarith
  have h_VStuff_VFI2_le :
      VStuff ≤ (C_rev * K_V) * (V + Fnorm + I2norm) := by
    refine le_trans h_covT_b_le ?_
    have h_FV_le : Fnorm + V ≤ V + Fnorm + I2norm := by linarith
    have h_step :
        C_rev * (K_V * (Fnorm + V)) ≤ C_rev * (K_V * (V + Fnorm + I2norm)) := by
      have h_inner : K_V * (Fnorm + V) ≤ K_V * (V + Fnorm + I2norm) :=
        mul_le_mul_of_nonneg_left h_FV_le hKV_nn
      exact mul_le_mul_of_nonneg_left h_inner hCrev_nn
    have h_eq : C_rev * (K_V * (V + Fnorm + I2norm)) =
        (C_rev * K_V) * (V + Fnorm + I2norm) := by ring
    linarith
  have h_Inner_le :
      Inner ≤ (K_E * C_Bg + C_rev * K_V) * (V + Fnorm + I2norm) := by
    rw [hInner_def]
    have h_distrib :
        (K_E * C_Bg + C_rev * K_V) * (V + Fnorm + I2norm) =
          (K_E * C_Bg) * (V + Fnorm + I2norm) +
            (C_rev * K_V) * (V + Fnorm + I2norm) := by ring
    linarith
  -- h_chartCD_bound has shape:
  --   ‖chartCD covT Bg.toFun b‖ ≤ C_cov · Mb_term · Inner.
  -- Need a slight rewrite of the parenthesisation.
  have h_chartCD_assoc :
      C_cov * Mb_term *
          (FStuff * ‖Bg.toFun b‖ + VStuff) =
        C_cov * (Mb_term * (FStuff * ‖Bg.toFun b‖ + VStuff)) := by ring
  -- Chain: ‖chartCD covT Bg b‖ ≤ C_cov · Mb_term · Inner ≤ C_cov · const_Mb · Inner
  --                              ≤ C_cov · const_Mb · ((K_E · C_Bg + C_rev · K_V) · (V+F+I2))
  --                              = K_lin · (V+F+I2).
  have h_step1 : C_cov * Mb_term * Inner ≤ C_cov * const_Mb * Inner := by
    have h_CcovMb_le : C_cov * Mb_term ≤ C_cov * const_Mb :=
      mul_le_mul_of_nonneg_left hMb_term_le hCcov_nn
    exact mul_le_mul_of_nonneg_right h_CcovMb_le hInner_nn
  have hCcovConstMb_nn : 0 ≤ C_cov * const_Mb := mul_nonneg hCcov_nn hconst_Mb_nn
  have h_step2 :
      C_cov * const_Mb * Inner ≤
        C_cov * const_Mb * ((K_E * C_Bg + C_rev * K_V) * (V + Fnorm + I2norm)) :=
    mul_le_mul_of_nonneg_left h_Inner_le hCcovConstMb_nn
  have h_step3 :
      C_cov * const_Mb * ((K_E * C_Bg + C_rev * K_V) * (V + Fnorm + I2norm)) =
        K_lin * (V + Fnorm + I2norm) := by
    rw [hK_lin_def]; ring
  calc ‖chartTensorRSCovariantDerivative (I := I) r s g α covT Bg.toFun b‖
      ≤ C_cov * Mb_term * Inner := by
        rw [hInner_def, hMb_term_def]
        exact h_chartCD_bound
    _ ≤ C_cov * const_Mb * Inner := h_step1
    _ ≤ C_cov * const_Mb * ((K_E * C_Bg + C_rev * K_V) * (V + Fnorm + I2norm)) := h_step2
    _ = K_lin * (V + Fnorm + I2norm) := h_step3

/-! ## Per-`i` bound for the second chart-frame piece -/

/-- For each frame index `i`, the norm of the second chart-frame piece
`∇^{(r,s)} T b ((LeviCivita g) B_i b (B_i b))` is bounded by a uniform
constant times `V + F + I2`, where `B_i = chartFrameNormGlobalSmooth g α i`. -/
private lemma fixedFrame_term2_le_VFI2
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun y : M => T.toSection y) b
            ((LeviCivita (I := I) g).toFun
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))‖ ≤
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
  set Bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    chartFrameNormGlobalSmooth (I := I) (M := M) g α i with hBg_def
  -- LeviCivita X X bound.
  obtain ⟨C_LX, hCLX_nn, hCLX_bound⟩ :=
    leviCivita_X_X_norm_bound_on_pouTsupport (I := I) (M := M) h_atlas g α
  -- Uniform bound on `‖Bg b‖`.
  obtain ⟨C_Bg, hCBg_nn, hCBg_bound⟩ :=
    chartFrameNormGlobalSmooth_norm_bound (I := I) (M := M) h_atlas g α i
  -- Uniform bound on `‖fderiv (chartE_section_repr α Bg.toFun ∘ symm) (φb)‖`.
  obtain ⟨C_dBg, hCdBg_nn, hCdBg_bound⟩ :=
    chartFrameNormGlobalSmooth_fderiv_repr_bound (I := I) (M := M) g α i
  -- Uniform bound on `‖LC Bg b (Bg b)‖`:
  set C_v : ℝ := C_LX * (C_dBg * C_Bg + C_Bg ^ 2) with hC_v_def
  have hC_v_nn : 0 ≤ C_v := by
    have h_a : 0 ≤ C_dBg * C_Bg := mul_nonneg hCdBg_nn hCBg_nn
    have h_b : 0 ≤ C_Bg ^ 2 := sq_nonneg _
    have h_c : 0 ≤ C_dBg * C_Bg + C_Bg ^ 2 := by linarith
    exact mul_nonneg hCLX_nn h_c
  -- 2ndApplication op-norm bound.
  obtain ⟨C_2nd, hC2nd_nn, hC2nd_bound⟩ :=
    rawTensorConnLap_2ndApplication_opNorm_bound
      (I := I) (M := M) h_atlas g r s α
  set const_Mv : ℝ := (max (1 + C_v) 1) ^ (max r s) with hconst_Mv_def
  have hconst_Mv_nn : 0 ≤ const_Mv := by
    have : 0 ≤ max (1 + C_v) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
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
  -- Headline constant: K_lin = C_2nd · const_Mv · (C_v + C_rev).
  set K_lin : ℝ := C_2nd * const_Mv * (C_v + C_rev) with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := by
    have h_a : 0 ≤ C_v + C_rev := by linarith
    have h_b : 0 ≤ C_2nd * const_Mv := mul_nonneg hC2nd_nn hconst_Mv_nn
    exact mul_nonneg h_b h_a
  refine ⟨K_lin, hK_lin_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
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
  -- ‖LC Bg b (Bg b)‖ ≤ C_LX · (C_dBg · C_Bg + C_Bg^2) = C_v.
  have h_LCBg_le :
      ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖ ≤
        C_LX *
          (‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
            + ‖Bg.toFun b‖ ^ 2) := hCLX_bound hb_pou Bg
  have h_Bg_b_le : ‖Bg.toFun b‖ ≤ C_Bg := hCBg_bound b hb_pou
  have h_dBg_le :
      ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ ≤ C_dBg :=
    hCdBg_bound b hb_pou
  have h_Bg_b_nn : 0 ≤ ‖Bg.toFun b‖ := norm_nonneg _
  have h_dBg_nn :
      0 ≤ ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
        (extChartAt I α).symm) (extChartAt I α b)‖ := norm_nonneg _
  have h_LCBg_C_v :
      ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖ ≤ C_v := by
    refine le_trans h_LCBg_le ?_
    rw [hC_v_def]
    have h_a :
        ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖ ≤
          C_dBg * C_Bg := by
      have h_aa := mul_le_mul_of_nonneg_right h_dBg_le h_Bg_b_nn
      have h_ab := mul_le_mul_of_nonneg_left h_Bg_b_le hCdBg_nn
      linarith
    have h_b : ‖Bg.toFun b‖ ^ 2 ≤ C_Bg ^ 2 := by
      exact sq_le_sq' (by linarith) h_Bg_b_le
    have h_sum :
        ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
            + ‖Bg.toFun b‖ ^ 2 ≤ C_dBg * C_Bg + C_Bg ^ 2 := by linarith
    have h_sum_nn :
        0 ≤ ‖fderiv ℝ (chartE_section_repr (I := I) α Bg.toFun ∘
              (extChartAt I α).symm) (extChartAt I α b)‖ * ‖Bg.toFun b‖
            + ‖Bg.toFun b‖ ^ 2 := by
      have h_a := mul_nonneg h_dBg_nn h_Bg_b_nn
      have h_b := sq_nonneg ‖Bg.toFun b‖
      linarith
    exact mul_le_mul_of_nonneg_left h_sum hCLX_nn
  -- ‖T b‖ ≤ C_rev · V.
  have h_T_b_le : ‖T.toSection b‖ ≤ C_rev * V := by
    have h := hCrev_bound b hb_pou (T.toSection b)
    change ‖T.toSection b‖ ≤ _ at h
    change ‖T.toSection b‖ ≤ C_rev * V
    exact h
  -- 2ndApplication bound for T := T.toSection, X := Bg.
  have h_2nd := hC2nd_bound (b := b) hb_pou T.toSection Bg
  -- h_2nd has the form:
  --   ‖∇^{(r,s)} T.toSection b (LC Bg b (Bg b))‖ ≤
  --     C_2nd · (max (1 + ‖LC Bg b (Bg b)‖) 1)^(max r s) ·
  --       (‖fderiv (repr T ∘ symm)‖ · ‖LC Bg b (Bg b)‖ + ‖T.toFun b‖).
  -- T.toSection.toFun = fun y => T.toSection y by definition.
  -- Set Mv_term = (max (1 + ‖LC Bg b (Bg b)‖) 1)^(max r s).
  set vNorm : ℝ := ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖
    with hvNorm_def
  have hvNorm_nn : 0 ≤ vNorm := norm_nonneg _
  set Mv_term : ℝ := (max (1 + vNorm) 1) ^ (max r s) with hMv_term_def
  have hMv_term_nn : 0 ≤ Mv_term := by
    have : 0 ≤ max (1 + vNorm) 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg this _
  have hMv_term_le : Mv_term ≤ const_Mv := by
    rw [hconst_Mv_def, hMv_term_def]
    have h_max_le : max (1 + vNorm) 1 ≤ max (1 + C_v) 1 :=
      max_le_max (by linarith [h_LCBg_C_v]) (le_refl _)
    have h_max_nn : (0 : ℝ) ≤ max (1 + vNorm) 1 :=
      le_trans zero_le_one (le_max_right _ _)
    exact pow_le_pow_left₀ h_max_nn h_max_le _
  -- Inner sum: Fnorm · vNorm + ‖T b‖.
  set Inner : ℝ := Fnorm * vNorm + ‖T.toSection b‖ with hInner_def
  have hInner_nn : 0 ≤ Inner := by
    have h_a : 0 ≤ Fnorm * vNorm := mul_nonneg hF_nn hvNorm_nn
    have h_b : 0 ≤ ‖T.toSection b‖ := norm_nonneg _
    linarith
  -- Bound Inner ≤ (C_v + C_rev) · (V+F+I2).
  have h_Inner_le : Inner ≤ (C_v + C_rev) * (V + Fnorm + I2norm) := by
    rw [hInner_def]
    have h_a : Fnorm * vNorm ≤ Fnorm * C_v :=
      mul_le_mul_of_nonneg_left h_LCBg_C_v hF_nn
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
  -- Now apply h_2nd, with appropriate associativity.
  -- h_2nd's RHS is `C_2nd * Mv_term * (Fnorm * vNorm + ‖T.toFun b‖)` (need .toFun unfolding).
  -- We need: ‖term2‖ ≤ K_lin · (V+F+I2).
  -- Chain: C_2nd · Mv_term · Inner ≤ C_2nd · const_Mv · Inner ≤ C_2nd · const_Mv · ((C_v+C_rev) · (V+F+I2)) = K_lin · (V+F+I2).
  have h_step1 : C_2nd * Mv_term * Inner ≤ C_2nd * const_Mv * Inner := by
    have h_C2nd_Mv_le : C_2nd * Mv_term ≤ C_2nd * const_Mv :=
      mul_le_mul_of_nonneg_left hMv_term_le hC2nd_nn
    exact mul_le_mul_of_nonneg_right h_C2nd_Mv_le hInner_nn
  have hC2ndConstMv_nn : 0 ≤ C_2nd * const_Mv := mul_nonneg hC2nd_nn hconst_Mv_nn
  have h_step2 :
      C_2nd * const_Mv * Inner ≤
        C_2nd * const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) :=
    mul_le_mul_of_nonneg_left h_Inner_le hC2ndConstMv_nn
  have h_step3 :
      C_2nd * const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) =
        K_lin * (V + Fnorm + I2norm) := by
    rw [hK_lin_def]; ring
  -- Now unfold T.toSection.toFun to match h_2nd's shape.
  have hTtoFun_eq : T.toSection.toFun = (fun y : M => T.toSection y) := rfl
  -- h_2nd: ‖∇^{(r,s)} T.toFun b (LC Bg.toFun b (Bg.toFun b))‖ ≤
  --        C_2nd * Mv_term * (Fnorm * vNorm + ‖T.toFun b‖)
  -- after rewriting T.toFun = fun y => T.toSection y, Bg.toFun = ...,
  -- we identify with our goal.
  calc ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (fun y : M => T.toSection y) b
        ((LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b))‖
      ≤ C_2nd * Mv_term * Inner := by
        rw [hInner_def, hMv_term_def]
        -- The RHS shape with explicit Fnorm and vNorm.
        have h_eq :
            Fnorm * ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖
              + ‖T.toSection b‖ =
              Fnorm * vNorm + ‖T.toSection b‖ := by rw [hvNorm_def]
        -- T.toSection.toFun reduces to T.toSection.
        have h_2nd' :
            ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                T.toSection.toFun b
                ((LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b))‖ ≤
              C_2nd *
                (max (1 + ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖) 1) ^
                  (max r s) *
                (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                    T.toSection.toFun ∘ (extChartAt I α).symm) (extChartAt I α b)‖ *
                  ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖
                + ‖T.toSection.toFun b‖) := h_2nd
        -- T.toSection.toFun = fun y => T.toSection y definitionally.
        have hToFun1 : T.toSection.toFun = (fun y : M => T.toSection y) := rfl
        rw [hToFun1] at h_2nd'
        -- Now h_2nd' uses (fun y => T.toSection y) and ‖(fun y => T.toSection y) b‖
        -- = ‖T.toSection b‖.
        -- The RHS Fnorm * vNorm + ‖T b‖ uses hvNorm. Let's see if the LHSes match.
        change ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
            (fun y : M => T.toSection y) b
            ((LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b))‖ ≤
          C_2nd *
            (max (1 + ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖) 1) ^
              (max r s) *
            (‖fderiv ℝ
                (tensorRSChartE_section_repr (I := I) r s α
                  (fun y : M => T.toSection y) ∘
                  (extChartAt I α).symm) (extChartAt I α b)‖ *
                ‖(LeviCivita (I := I) g).toFun Bg.toFun b (Bg.toFun b)‖
              + ‖T.toSection b‖)
        exact h_2nd'
    _ ≤ C_2nd * const_Mv * Inner := h_step1
    _ ≤ C_2nd * const_Mv * ((C_v + C_rev) * (V + Fnorm + I2norm)) := h_step2
    _ = K_lin * (V + Fnorm + I2norm) := h_step3

/-! ## Headline -/

/-- **Pointwise squared op-norm bound for `rawTensorConnLap` by the chart-pulled
representation data.** -/
theorem rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
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
  -- Per-i constants from the term-1 and term-2 bounds.
  have h_t1_choose : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
              (fun y : M => T.toSection y)) b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)‖ ≤
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
    fixedFrame_term1_le_VFI2 (I := I) (M := M) h_atlas g r s α i
  choose K_t1 hKt1_nn hKt1_bound using h_t1_choose
  have h_t2_choose : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun y : M => T.toSection y) b
            ((LeviCivita (I := I) g).toFun
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))‖ ≤
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
    fixedFrame_term2_le_VFI2 (I := I) (M := M) h_atlas g r s α i
  choose K_t2 hKt2_nn hKt2_bound using h_t2_choose
  set sumK : ℝ := (∑ i, K_t1 i) + (∑ i, K_t2 i) with hsumK_def
  have hsumK_nn : 0 ≤ sumK := by
    have h_a : 0 ≤ ∑ i, K_t1 i := Finset.sum_nonneg (fun i _ => hKt1_nn i)
    have h_b : 0 ≤ ∑ i, K_t2 i := Finset.sum_nonneg (fun i _ => hKt2_nn i)
    linarith
  -- Final squared constant K_final := 3 · sumK^2.
  set K_final : ℝ := 3 * sumK ^ 2 with hK_final_def
  have hK_final_nn : 0 ≤ K_final := by
    have h_a : 0 ≤ sumK ^ 2 := sq_nonneg _
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
  -- B3 bridge: rewrite the raw operator using the global chart-α frame.
  have h_via_B3 :
      rawTensorConnLap (I := I) g r s
          (fun y : M => T.toSection y) b =
        rawTensorConnLap_fixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun y : M => T.toSection y) b :=
    rawTensorConnLap_via_chartFrameNormGlobalSmooth
      (I := I) (M := M) g r s T α (b := b) hb
  -- Unfold the fixed-frame sum.
  have h_unfold : rawTensorConnLap_fixedFrame (I := I) g r s
        (fun i : Fin (Module.finrank ℝ E) =>
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
        (fun y : M => T.toSection y) b =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
              (fun y : M => T.toSection y)) b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun y : M => T.toSection y) b
            ((LeviCivita (I := I) g).toFun
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    rawTensorConnLap_fixedFrame_def (I := I) g r s
      (fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
      (fun y : M => T.toSection y) b
  -- Triangle inequality for the sum.
  set t1 : Fin (Module.finrank ℝ E) → ℝ := fun i =>
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
            (fun y : M => T.toSection y)) b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)‖
    with ht1_def
  set t2 : Fin (Module.finrank ℝ E) → ℝ := fun i =>
      ‖(TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun) b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))‖
    with ht2_def
  -- ‖∑ i, (t1_i - t2_i term)‖ ≤ ∑ i, (t1_i + t2_i).
  have h_norm_le_sum :
      ‖rawTensorConnLap (I := I) g r s
          (fun y : M => T.toSection y) b‖ ≤
        ∑ i : Fin (Module.finrank ℝ E), (t1 i + t2 i) := by
    rw [h_via_B3, h_unfold]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i _
    refine le_trans (norm_sub_le _ _) ?_
    rfl
  -- Per-i bounds.
  have h_t1_le : ∀ i : Fin (Module.finrank ℝ E),
      t1 i ≤ K_t1 i * (V + Fnorm + I2norm) := fun i =>
    hKt1_bound i T hb
  have h_t2_le : ∀ i : Fin (Module.finrank ℝ E),
      t2 i ≤ K_t2 i * (V + Fnorm + I2norm) := fun i =>
    hKt2_bound i T hb
  -- ∑ i, (t1 i + t2 i) ≤ sumK · (V + Fnorm + I2norm).
  have h_sum_le_sumK :
      ∑ i : Fin (Module.finrank ℝ E), (t1 i + t2 i) ≤
        sumK * (V + Fnorm + I2norm) := by
    calc ∑ i : Fin (Module.finrank ℝ E), (t1 i + t2 i)
        = (∑ i, t1 i) + (∑ i, t2 i) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i, K_t1 i * (V + Fnorm + I2norm)) +
            (∑ i, K_t2 i * (V + Fnorm + I2norm)) := by
          have h_a : ∑ i, t1 i ≤ ∑ i, K_t1 i * (V + Fnorm + I2norm) :=
            Finset.sum_le_sum (fun i _ => h_t1_le i)
          have h_b : ∑ i, t2 i ≤ ∑ i, K_t2 i * (V + Fnorm + I2norm) :=
            Finset.sum_le_sum (fun i _ => h_t2_le i)
          linarith
      _ = sumK * (V + Fnorm + I2norm) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsumK_def]
          ring
  -- Now: ‖raw‖ ≤ sumK · (V+F+I2).
  have h_raw_le :
      ‖rawTensorConnLap (I := I) g r s
          (fun y : M => T.toSection y) b‖ ≤ sumK * (V + Fnorm + I2norm) :=
    le_trans h_norm_le_sum h_sum_le_sumK
  -- Square.
  have h_raw_nn : 0 ≤ ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ sumK * (V + Fnorm + I2norm) := mul_nonneg hsumK_nn hVFI2_nn
  have h_sq : ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
        (sumK * (V + Fnorm + I2norm)) ^ 2 :=
    pow_le_pow_left₀ h_raw_nn h_raw_le 2
  have h_expand :
      (sumK * (V + Fnorm + I2norm)) ^ 2 =
        sumK ^ 2 * (V + Fnorm + I2norm) ^ 2 := by ring
  have h_sq_inner : (V + Fnorm + I2norm) ^ 2 ≤ 3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) :=
    sq_add_three_le_three_mul_sum_sq V Fnorm I2norm
  have h_sumK_sq_nn : 0 ≤ sumK ^ 2 := sq_nonneg _
  have h_step :
      sumK ^ 2 * (V + Fnorm + I2norm) ^ 2 ≤
        sumK ^ 2 * (3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2)) :=
    mul_le_mul_of_nonneg_left h_sq_inner h_sumK_sq_nn
  have h_final :
      sumK ^ 2 * (3 * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2)) =
        K_final * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) := by
    rw [hK_final_def]; ring
  linarith

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
end Sanity
