import DifferentialGeometry.Tensor.Exterior.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {k : ℕ}

private lemma tangentCoordChange_eq_fderivWithin {x₀ x z : M} :
    tangentCoordChange IM x x₀ z =
      fderivWithin ℝ (extChartAt IM x₀ ∘ (extChartAt IM x).symm) (range IM) (extChartAt IM x z) := by
  rfl

private lemma linearMapAt_symmL_eq_tangentCoordChange {x₀ x z : M}
    (hx : z ∈ (extChartAt IM x).source) (hx₀ : z ∈ (extChartAt IM x₀).source) :
    (trivializationAt EM (TangentSpace IM) x₀).continuousLinearMapAt ℝ z ∘L
        (trivializationAt EM (TangentSpace IM) x).symmL ℝ z =
      tangentCoordChange IM x x₀ z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simpa [extChartAt_source] using hx₀),
    TangentBundle.symmL_trivializationAt_eq_core (by simpa [extChartAt_source] using hx)]
  apply ContinuousLinearMap.ext
  intro v
  have hw : z ∈ (extChartAt IM x).source ∩ (extChartAt IM z).source ∩ (extChartAt IM x₀).source :=
    ⟨⟨by simpa [extChartAt_source] using hx, by simp⟩,
      by simpa [extChartAt_source] using hx₀⟩
  change tangentCoordChange IM z x₀ z (tangentCoordChange IM x z z v) = tangentCoordChange IM x x₀ z v
  exact tangentCoordChange_comp (w := x) (x := z) (y := x₀) (z := z) hw

private lemma localRep_eq_pullback {x₀ x z : M}
    (hx : z ∈ (extChartAt IM x).source) (hx₀ : z ∈ (extChartAt IM x₀).source) (m : ℕ)
    (L : (TangentSpace IM z) [⋀^Fin m]→L[ℝ] (Bundle.Trivial M ℝ z)) :
    (trivializationAt ((EM [⋀^Fin m]→L[ℝ] ℝ)) ((Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))) x ⟨z, L⟩).2 =
      ((trivializationAt ((EM [⋀^Fin m]→L[ℝ] ℝ)) ((Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))) x₀ ⟨z, L⟩).2).compContinuousLinearMap
        (tangentCoordChange IM x x₀ z) := by
  rw [DifferentialGeometry.DifferentialForm.altTriv_apply (m := m) (x₀ := x) (x := z) (L := L),
    DifferentialGeometry.DifferentialForm.altTriv_apply (m := m) (x₀ := x₀) (x := z) (L := L)]
  ext v
  change L ((trivializationAt EM (TangentSpace IM) x).symmL ℝ z ∘ v) =
    L (((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ z ∘ tangentCoordChange IM x x₀ z) ∘ v)
  congr 1
  funext i
  rw [Function.comp_apply, Function.comp_apply]
  rw [← linearMapAt_symmL_eq_tangentCoordChange (x₀ := x₀) (x := x) (z := z) (hx := hx) (hx₀ := hx₀)]
  rw [Function.comp_apply]
  exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt EM (TangentSpace IM) x₀)
    (by simpa [extChartAt_source] using hx₀)
    ((trivializationAt EM (TangentSpace IM) x).symmL ℝ z (v i))).symm

private lemma localRep_contDiffOn (α : DifferentialForm IM M k) (x₀ : M) :
    ContDiffOn ℝ ⊤ (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      ((extChartAt IM x₀).target) := by
  have hsec : ContMDiffOn IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤ (fun z : M =>
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨z, α z⟩).2) (extChartAt IM x₀).source := by
    intro z hz
    have hz₀ : z ∈ (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀).baseSet := by
      change z ∈ (trivializationAt EM (TangentSpace IM) x₀).baseSet ∩
        (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).baseSet
      exact ⟨by simpa [extChartAt_source] using hz, trivial⟩
    exact (Bundle.Trivialization.contMDiffAt_section_iff
      (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀) hz₀).mp (α.contMDiff_toFun z) |>.contMDiffWithinAt
  have hcomp : ContMDiffOn (𝓘(ℝ, EM)) 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ⊤
      (fun y => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀ ⟨(extChartAt IM x₀).symm y, α ((extChartAt IM x₀).symm y)⟩).2)
      ((extChartAt IM x₀).target) := by
    exact hsec.comp (contMDiffOn_extChartAt_symm x₀) (fun y hy => (extChartAt IM x₀).map_target hy)
  exact hcomp.contDiffOn

private lemma compContinuousLinearMap_compContinuousLinearMap {m n : ℕ}
    (L : EM [⋀^Fin m]→L[ℝ] (EM [⋀^Fin n]→L[ℝ] ℝ))
    (A : EM →L[ℝ] EM) (B : EM →L[ℝ] EM) :
    (L.compContinuousLinearMap A).compContinuousLinearMap B =
      L.compContinuousLinearMap (A ∘L B) := by
  ext v
  rfl

private lemma tangentCoordChange_comp_self {x₀ x : M} (hx : x ∈ (extChartAt IM x₀).source) :
    (tangentCoordChange IM x x₀ x) ∘L (tangentCoordChange IM x₀ x x) =
      ContinuousLinearMap.id ℝ EM := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hw : x ∈ (extChartAt IM x₀).source ∩ (extChartAt IM x).source ∩ (extChartAt IM x₀).source := by
    exact ⟨⟨hx, by simp⟩, hx⟩
  rw [tangentCoordChange_comp (I := IM) (w := x₀) (x := x) (y := x₀) (z := x) hw]
  exact tangentCoordChange_self (I := IM) (x := x₀) (z := x) hx

noncomputable def exteriorDerivativeAt (α : DifferentialForm IM M k) (x : M) :
    Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x :=
  (trivializationAt (EM [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + 1)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x).symmL ℝ x
    (extDeriv (fun y : EM => (trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x ⟨(extChartAt IM x).symm y, α ((extChartAt IM x).symm y)⟩).2)
      ((extChartAt IM x) x))

private lemma chartChange_contDiffAt {x₀ x : M} (hx : x ∈ (extChartAt IM x₀).source)
    (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    ContDiffAt ℝ ⊤ ((extChartAt IM x₀) ∘ (extChartAt IM x).symm : EM → EM)
      ((extChartAt IM x) x) := by
  have hy : (extChartAt IM x) x ∈ ((extChartAt IM x).symm ≫ (extChartAt IM x₀)).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨(extChartAt IM x).map_source (by rw [extChartAt_source]; exact mem_chart_source (H := HM) x),
      by simpa [extChartAt_source] using hx⟩
  exact (contDiffWithinAt_ext_coord_change (I := IM) x₀ x hy).contDiffAt
    (range_mem_nhds_isInteriorPoint hxi)

end DifferentialForm
end DifferentialGeometry

end
