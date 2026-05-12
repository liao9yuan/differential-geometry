import RicciFlower.Coordinates.NablaComponents.Basic
import RicciFlower.Tensor.RSTensor.Basis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate components of mixed tensor covariant derivatives

This file extends the coordinate-frame component API from covariant tensors to
mixed `(r,s)` tensors.  It stays independent of Ricci-flow evolution files and
only bridges the fixed-chart model derivative to the coordinate-frame scalar
component derivative.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Directional derivative of a mixed tensor coordinate-frame component.

The Hom-input tensor is kept constant in the chart centered at `x₀`; this avoids
the moving-center component derivative. -/
def coordDerivRSAt {r s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r x₀ β₀
  mfderiv I 𝓘(𝕜, 𝕜)
    (fun y : M =>
      (T y (β y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
    x₀ (X x₀)

/-- The chart-model derivative term appearing definitionally in `nablaRSFun`. -/
def modelDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
    (fun x => X x) (Set.range I)
  let T' : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ T
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  (fderivWithin 𝕜 T'
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)
      (X' (extChartAt I x₀ x₀))
    β₀)
    (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))

/-- Predicate recording that the fixed-chart model derivative agrees with the
manifold scalar derivative of mixed tensor coordinate components. -/
def ModelDerivEqCoordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x) :
    Prop :=
  forall upper lower,
    modelDerivRSAt (I := I) X x₀ T upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ T upper lower

set_option backward.isDefEq.respectTransparency false in
/-- At the base point, mixed tensor model components in the fixed
trivialization agree with coordinate-frame components. -/
theorem tensorRSModelAt_coordComponentRSAt {r s : ℕ} (x₀ : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ x₀ T
      ((continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
      (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))
    =
      coordComponentRSAt (I := I) T upper lower := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := 𝕜) (E := E) r
  unfold tensorRSModelAt
  rw [coordComponentRSAt_apply, componentRS_apply]
  have hx : x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [TensorRSSpace.trivializationAt_basis_coord
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) (r := r) (s := s)
    (bE := Module.finBasis 𝕜 E) hx T upper lower]
  congr 2
  · change
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
          ((continuousMultilinearMap_basis
            (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) =
        basisTensor0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) upper
    ext v
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    change
      ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper)) v =
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) v
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hmodel := congrArg (fun A : Tensor0SModel r 𝕜 E => A v)
      (TensorLieDeriv.tensor0SModelAt_trivializationAt_symm
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
    dsimp at hmodel
    rw [TensorLieDeriv.tensor0SModelAt_apply] at hmodel
    conv at hmodel =>
      lhs
      arg 2
      ext a
      rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
      rw [mfderivWithin_range_extChartAt_symm]
    simpa [Trivialization.symmL_apply, mfderivWithin_range_extChartAt_symm] using hmodel
  · funext b
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
    rw [mfderivWithin_range_extChartAt_symm]
    rfl

private theorem model_RS_component_eq_coord_component_comp_eventually {r s : ℕ}
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    let β₀ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
    (fun y : E =>
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s x₀ T y β₀)
          (fun b => (Module.finBasis 𝕜 E) (lower b))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        (T ((extChartAt I x₀).symm y)
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β₀ ((extChartAt I x₀).symm y)))
          (fun b =>
            coordinateFrameAt (I := I) x₀ (lower b)
              ((extChartAt I x₀).symm y))) := by
  intro β₀
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  unfold tensorRSModelInChart tensorRSModelAt Tensor0SSpace.constInChart
  rw [TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := (extChartAt I x₀).symm y)
    (r := r) (s := s)]
  · congr 2
    funext b
    have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
    rw [coordinateFrameAt_apply_of_mem (I := I) hy_base (lower b)]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hy_src]
    rfl
  · have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    simpa [trivializationAt] using hy_src

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-bundle chart derivative used by `nablaRSFun` agrees with the
manifold directional derivative of the corresponding coordinate-frame mixed
component. -/
theorem modelDeriv_eq_coordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x) := by
  classical
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI : NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := inferInstance
  intro upper lower
  let z₀ : E := extChartAt I x₀ x₀
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let u : Fin s -> E := fun b => (Module.finBasis 𝕜 E) (lower b)
  let Tchart : E -> TensorRSModel r s 𝕜 E :=
    fun y => tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x) y
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    fun x => Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r x₀ β₀ x
  let f : M -> 𝕜 :=
    fun y => (T y (β y))
      (fun b => coordinateFrameAt (I := I) x₀ (lower b) y)
  have hS : S = Set.range I := by
    ext y
    simp [S]
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hzS : z₀ ∈ S := by
    simpa [hS] using hzRange
  have huniq : UniqueDiffWithinAt 𝕜 S z₀ := by
    simpa [hS, z₀] using I.uniqueDiffOn z₀ hzRange
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hmodel_eventually :
      (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[S] z₀]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    have h := model_RS_component_eq_coord_component_comp_eventually
      (I := I) (M := M) (r := r) (s := s) x₀ (fun x => T x) upper lower
    simpa [S, z₀, Tchart, β₀, u, β, f, writtenInExtChartAt] using h
  have hT_model := by
    have h := T.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensorRSModelAt] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm S z₀ := by
    simpa [S, z₀] using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hT_model_center :
      ContMDiffAt I
        𝓘(𝕜, TensorRSModel r s 𝕜 E)
        (∞ : WithTop ℕ∞)
        (fun x : M =>
          tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s x₀ x (T x))
        ((extChartAt I x₀).symm z₀) := by
    simpa [z₀, extChartAt_to_inv] using hT_model
  have hTchart_cd := by
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := z₀) hT_model_center hsymm
    simpa [Tchart, tensorRSModelInChart, Function.comp, z₀] using hcomp
  have hTchart_diff :
      DifferentiableWithinAt 𝕜 Tchart S z₀ := by
    exact hTchart_cd.contDiffWithinAt.differentiableWithinAt (by simp)
  have hscalar_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ := by
    have hfun_diff :
        DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ :=
      hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
    exact hfun_diff.continuousMultilinear_apply_const u
  have hwritten_diff :
      DifferentiableWithinAt 𝕜
        (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) (Set.range I) z₀ := by
    have hscalar_diff_range :
        DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) (Set.range I) z₀ := by
      simpa [hS] using hscalar_diff
    have hmodel_range :
        (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[Set.range I] z₀]
          writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
      simpa [hS] using hmodel_eventually
    exact (hmodel_range.differentiableWithinAt_iff_of_mem hzRange).mp hscalar_diff_range
  have hf_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀ := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(𝕜, 𝕜))
      (x := x₀) (x' := x₀) (mem_chart_source H x₀)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, z₀, extChartAt, Function.comp_def] using hwritten_diff
  unfold modelDerivRSAt coordDerivRSAt
  change
    ((fderivWithin 𝕜 Tchart S z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀)) β₀) u =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf_md.mfderiv]
  have happly₁ :
      (fderivWithin 𝕜 Tchart S z₀ (X x₀)) β₀ =
        fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀) := by
    have hconst : DifferentiableWithinAt 𝕜 (fun _ : E => β₀) S z₀ :=
      differentiableWithinAt_const β₀
    have h :=
      congrArg (fun L => L (X x₀))
        (fderivWithin_clm_apply (𝕜 := 𝕜) (s := S) (x := z₀)
          huniq hTchart_diff hconst)
    simpa [fderivWithin_const_apply] using h.symm
  rw [happly₁]
  have hfun_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ := by
    exact hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
  have happly₂ :
      (fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀)) u =
        fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ (X x₀) := by
    exact (fderivWithin_continuousMultilinear_apply_const_apply
      huniq hfun_diff u (X x₀)).symm
  rw [happly₂]
  have hfd :
      fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) S z₀ :=
    hmodel_eventually.fderivWithin_eq_of_mem hzS
  rw [hfd]
  rw [hS]
  rfl

/-- Coordinate-frame component formula for `nablaRSFun` in arbitrary mixed
valence. -/
theorem nablaRS_coordFrame_slots {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x))
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  classical
  simp only [nablaRSFun, TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection]
  rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensorRSWithin
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s X
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      T Set.univ x₀) upper lower]
  have hmodel := TensorLieDeriv.covariantDeriv_tensorRSModelWithin_apply_basis_slots
    (𝕜 := 𝕜) (E := E)
    (basis := Module.finBasis 𝕜 E)
    (X := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (ΓX := connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (T := tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x))
    (u := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (x := extChartAt I x₀ x₀)
    (upper := upper)
    (lower := lower)
  unfold TensorLieDeriv.mcovariantDeriv_tensorRSWithin
  rw [TensorLieDeriv.tensorRSModelAt_trivializationAt_symm]
  refine hmodel.trans ?_
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  change
    modelDerivRSAt (I := I) X x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b)))
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower)
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k))
  rw [hderiv upper lower]
  have hupperSum :
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))) =
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    rw [tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      (Function.update upper a k) lower]
  have hlowerSum :
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    have hslots :
        Function.update
            (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
            b ((Module.finBasis 𝕜 E) k) =
          fun c : Fin s => (Module.finBasis 𝕜 E) (Function.update lower b k c) := by
      funext c
      by_cases hc : c = b
      · subst hc
        simp
      · simp [Function.update, hc]
    rw [hslots]
    rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      upper (Function.update lower b k)]
  rw [hupperSum, hlowerSum]

/-- Coordinate-frame component formula for `nablaRSFun`, with the model/scalar
derivative bridge discharged by smoothness of the tensor field. -/
theorem nablaRS_coordFrame_slots_of_smooth {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  exact nablaRS_coordFrame_slots (I := I) cov X T x₀
    (modelDeriv_eq_coordDerivRSAt (I := I) X x₀ T) upper lower

end Coordinates
end RicciFlower
