import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.Basis

/-!
# Output-slot permutations of tensor operator fields

This module supplies the exact fibre and smooth-section operations that
permute the covariant output slots of a mixed tensor operator field.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- Permute the covariant output slots of a mixed tensor fibre. -/
def rsDomDomCongr {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) : TensorRSSpace r s I x :=
  TensorRSSpace.ofCLM
    ((((tensor0SSpace_continuousLinearEquiv s x).symm.toContinuousLinearMap).comp
        (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ).toContinuousLinearEquiv
            : Tensor0SModel s ℝ E ≃L[ℝ] Tensor0SModel s ℝ E).toContinuousLinearMap.comp
          ((tensor0SSpace_continuousLinearEquiv s x).toContinuousLinearMap))).comp
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T))

set_option linter.unusedSectionVars false in
/-- Taking the model of an output-slot permutation is model slot
permutation after applying the original operator. -/
lemma toModel_rsDomDomCongr_apply {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from rsDomDomCongr σ T) d) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)) := by
  rw [rsDomDomCongr, TensorRSSpace.ofCLM]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [Tensor0SSpace.toModel]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

set_option linter.unusedSectionVars false in
/-- Evaluation of a permuted mixed tensor reads the original output on the
permuted tuple. -/
lemma rsDomDomCongr_apply_eval {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T : TensorRSSpace r s I x) (d : Tensor0SSpace r I x)
    (v : Fin s → TangentSpace I x) :
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from rsDomDomCongr σ T) d v =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d (fun k => v (σ k)) := by
  classical
  have hL := toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      (y : Tensor0SSpace s I x) w = Tensor0SSpace.toModel y w := fun y w => rfl
  rw [hfib, hL, ContinuousMultilinearMap.domDomCongr_apply, ← hfib]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- Output-slot permutation preserves smoothness of a mixed tensor operator
field. -/
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (rsDomDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => rsDomDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        R.toSection x) (Y x))).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
/-- Permute the covariant output slots of a smooth mixed tensor operator
field. -/
def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => rsDomDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Canonical congruence theorem for output-slot permutation fields. -/
@[congr] theorem rsDomDom_congr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ σ' : Equiv.Perm (Fin s)) (hσ : σ = σ') :
    ∀ (R R' : SmoothCcTensor g r s), R = R' →
      rsDomDomCongrSection (I := I) (M := M) g r s σ R =
        rsDomDomCongrSection (I := I) (M := M) g r s σ' R' := by
  subst σ'
  intro R R' hR
  subst R'
  rfl

set_option linter.unusedSectionVars false in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      rsDomDomCongr σ (R.toSection x) := rfl

end Connection
end Integral
end DifferentialGeometry

end
