import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.ChartJacobianClmSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma tangent_baseSet_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α

private lemma tangent_symmL_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ α = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

private lemma tangent_clmAt_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

private lemma contMDiffOn_coordChangeL_tangent (α β : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _))
    (trivializationAt E (TangentSpace I) α)
    (trivializationAt E (TangentSpace I) β)
  rw [tangent_baseSet_eq, tangent_baseSet_eq] at h
  exact h

private lemma coordChangeL_apply_eq_clmAt_symmL
    (α β : M) {b : M}
    (hbα : b ∈ (chartAt H α).source) (hbβ : b ∈ (chartAt H β).source) (v : E) :
    ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
  have hbα' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [tangent_baseSet_eq]; exact hbα
  have hbβ' : b ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [tangent_baseSet_eq]; exact hbβ
  change ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) b) v =
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
      ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)
  rw [Trivialization.coordChangeL_apply _ _ ⟨hbα', hbβ'⟩]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hbβ',
      Bundle.Trivialization.symmL_apply]

private noncomputable def basisCoordCLM (j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord j).toContinuousLinearMap

@[simp] private lemma basisCoordCLM_apply (j : Fin (Module.finrank ℝ E)) (v : E) :
    basisCoordCLM (E := E) j v = (Module.finBasis ℝ E).coord j v := rfl

theorem chartJinvMatrix_wrapped_entry_contMDiffOn
    (α β : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  
  have hcoord := contMDiffOn_coordChangeL_tangent (I := I) α β
  have hcoord_app : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E)
          ((Module.finBasis ℝ E) i))
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    hcoord.clm_apply contMDiffOn_const
  have hcoordj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (basisCoordCLM (E := E) j) :=
    (basisCoordCLM (E := E) j).contMDiff
  have hwrapped : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (basisCoordCLM (E := E) j)
        (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E)
            ((Module.finBasis ℝ E) i)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro b hb
    exact (hcoordj _).contMDiffWithinAt.comp _ (hcoord_app _ hb) (mapsTo_univ _ _)
  refine hwrapped.congr ?_
  intro b ⟨hbα, hbβ⟩
  rw [basisCoordCLM_apply]
  exact (congrArg ((Module.finBasis ℝ E).coord j)
    (coordChangeL_apply_eq_clmAt_symmL (I := I) α β hbα hbβ
      ((Module.finBasis ℝ E) i))).symm

theorem chartJMatrix_wrapped_entry_contMDiffOn
    (α β : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) β).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  
  have h := chartJinvMatrix_wrapped_entry_contMDiffOn (I := I) β α i j
  
  rw [Set.inter_comm] at h
  exact h

theorem chartJinvMatrix_entry_contMDiffAt_via_wrapped
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      b₀ := by
  have hwrapped := chartJinvMatrix_wrapped_entry_contMDiffOn (I := I) α b₀ i j
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

theorem chartJinvMatrix_entry_wrapped_at_centre
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀
          ((Module.finBasis ℝ E) i))) =
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀
        ((Module.finBasis ℝ E) i)) := by
  have h := tangent_clmAt_self_eq_one (I := I) b₀
  rw [h]
  rfl

theorem chartJMatrix_entry_contMDiffAt_via_wrapped
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      b₀ := by
  have hwrapped := chartJMatrix_wrapped_entry_contMDiffOn (I := I) α b₀ i j
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

theorem chartJMatrix_entry_wrapped_at_centre
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀
          ((Module.finBasis ℝ E) i))) =
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((Module.finBasis ℝ E) i)) := by
  have h := tangent_symmL_self_eq_one (I := I) b₀
  rw [h]
  rfl

end Tensor
end DifferentialGeometry

end
