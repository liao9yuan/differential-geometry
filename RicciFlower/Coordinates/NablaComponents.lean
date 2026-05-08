import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.Tensor.RSTensor.NablaOnTensors

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate components of realized covariant derivatives

This file bridges the model-level tensor covariant derivative formulas in
`Tensor.RSTensor.NablaOnTensors` to the chart-induced coordinate frame.

The purely algebraic Christoffel correction identities live in
`NablaOnTensors.lean`; this file only identifies the model coefficients and
coordinate derivative terms used by the coordinate-frame component statements.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace Real]

/-- The coordinate frame as a `C¹` local frame, for Christoffel-component APIs. -/
def coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (1 : WithTop ℕ∞) (Module.finBasis Real E)

/-- At the base point, the chart-induced coordinate basis is the model-space basis. -/
theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E := by
  ext i
  rw [coordinateFrameAt_toBasis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) (coordinateFrameAt_mem (I := I) x₀) i]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

private theorem tangentConstInChart_eq_coordinateFrame_eventually
    (x₀ : M) (i : CoordinateIdx E) :
    (tangentConstInChart (𝕜 := Real) (I := I) x₀ ((Module.finBasis Real E) i) :
        (x : M) → TangentSpace I x) =ᶠ[𝓝 x₀]
      coordinateFrameAt (I := I) x₀ i := by
  filter_upwards
    [((coordinateTrivializationAt (I := I) x₀).open_baseSet.mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))] with x hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [tangentConstInChart_apply]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src]
  rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := x) hx i]
  rfl

/-- Model connection coefficients agree with coordinate-frame Christoffel coefficients
in the chart-induced coordinate frame. -/
theorem connCoeff_eq_christoffelAlong_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (j k : CoordinateIdx E) :
    connectionEndomorphismCoeff (𝕜 := Real) (E := E) (Module.finBasis Real E)
        (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀
          (extChartAt I x₀ x₀)) j k =
      christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) j k := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  have hx_base : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt, coordinateFrameAt_mem (I := I) x₀]
  have hconst :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := Real) (I := I) x₀
          ((Module.finBasis Real E) j) : (x : M) → TangentSpace I x)) x₀ :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x₀) (p := x₀)
      ((Module.finBasis Real E) j) hx_base
  have hframe :
      MDiffAt (T% (coordinateFrameAt (I := I) x₀ j)) x₀ :=
    ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (tangentConstInChart (𝕜 := Real) (I := I) x₀
            ((Module.finBasis Real E) j)) x₀ =
        cov (coordinateFrameAt (I := I) x₀ j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hconst hframe
      (by simp)
      (tangentConstInChart_eq_coordinateFrame_eventually (I := I) x₀ j)
  unfold connectionEndomorphismCoeff christoffelAlongInFrame
  rw [connectionEndomorphismInChart_apply_of_mem
    (𝕜 := Real) (I := I) cov X x₀ (mem_extChartAt_target x₀)
    ((Module.finBasis Real E) j)]
  rw [extChartAt_to_inv]
  rw [hcov]
  have hcoeff :
      ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k x₀
        ((cov (coordinateFrameAt (I := I) x₀ j) x₀) (X x₀))) =
        (Module.finBasis Real E).coord k
          ((coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt Real x₀
            ((cov (coordinateFrameAt (I := I) x₀ j) x₀) (X x₀))) := by
    have hbasis (hx : x₀ ∈ coordinateFrameSet (I := I) x₀) :
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
          (coordinateTrivializationAt (I := I) x₀).basisAt
            (Module.finBasis Real E)
            (by simpa [coordinateFrameSet, coordinateTrivializationAt] using hx) := by
      ext a
      rw [IsLocalFrameOn.toBasisAt_coe]
      simp [coordinateFrameAt_isLocalFrame_one, coordinateFrameAt,
        coordinateFrameSet, coordinateTrivializationAt]
    unfold IsLocalFrameOn.coeff
    rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
    rw [hbasis (coordinateFrameAt_mem (I := I) x₀)]
    simp [Bundle.Trivialization.basisAt]
    rw [Bundle.Trivialization.linearMapAt_apply]
    simp [coordinateFrameAt_mem, coordinateFrameSet, coordinateTrivializationAt]
  rw [hcoeff]

/-- Directional derivative of a coordinate-frame covariant tensor component. -/
def coordDeriv0SAt {s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx E) : Real :=
  mfderiv I 𝓘(Real, Real)
    (fun y : M => α y (fun a => coordinateFrameAt (I := I) x₀ (slots a) y))
    x₀ (X x₀)

/-- The chart-model derivative term that appears definitionally in `nabla0SFun`. -/
def modelDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx E) : Real :=
  let X' := VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
    (fun x => X x) (Set.range I)
  let α' : E -> ContinuousMultilinearMap Real (fun _ : Fin s => E) Real :=
    fun y => tensor0SSpace_continuousLinearEquiv (I := I) s
      ((extChartAt I x₀).symm y) (α ((extChartAt I x₀).symm y))
  fderivWithin Real α'
    (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (extChartAt I x₀ x₀) (X' (extChartAt I x₀ x₀))
    (fun a => (Module.finBasis Real E) (slots a))

/-- Predicate recording that the chart-model derivative term agrees with the
scalar directional derivative of coordinate-frame components. This is the
remaining analytic/chart-identification bridge. -/
def ModelDerivEqCoordDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x) : Prop :=
  forall slots : Fin s -> CoordinateIdx E,
    modelDeriv0SAt (I := I) X x₀ α slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ α slots

private theorem covariantDeriv_tensor0SModelWithin_one_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real E)
    (X : E -> E) (ΓX : E -> E →L[Real] E)
    (α : E -> Tensor0SModel (𝕜 := Real) (E := E) 1)
    (u : Set E) (y : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := Real) (E := E) 1 X ΓX α u y
        (fun _ : Fin 1 => basis j) =
      fderivWithin Real α u y (X y) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff (𝕜 := Real) (E := E)
          basis (ΓX y) j k * α y (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_one_apply_basis (𝕜 := Real) (E := E)
    basis (fderivWithin Real α u y (X y)) (ΓX y) (α y) j

private theorem covariantDeriv_tensor0SModelWithin_two_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real E)
    (X : E -> E) (ΓX : E -> E →L[Real] E)
    (A : E -> Tensor0SModel (𝕜 := Real) (E := E) 2)
    (u : Set E) (y : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := Real) (E := E) 2 X ΓX A u y
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin Real A u y (X y)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff (𝕜 := Real) (E := E)
          basis (ΓX y) j k *
          A y (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff (𝕜 := Real) (E := E)
          basis (ΓX y) l k *
          A y (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_two_apply_basis (𝕜 := Real) (E := E)
    basis (fderivWithin Real A u y (X y)) (ΓX y) (A y) j l

/-- Coordinate-frame component formula for the covariant derivative of a one-form,
with the derivative term kept in the chart-model form used by `nabla0SFun`. -/
theorem nabla0S_one_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  classical
  simp only [coordComponent0SAt, component0S,
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀,
    nabla0SFun, TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensor0SWithin]
  rw [Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_symm_apply]
  letI : NormedAddCommGroup (Tensor0SModel 1 Real E) :=
    Tensor0SBundle.instNormedAddCommGroupTensor0SModel (𝕜 := Real) (E := E) 1
  letI : NormedSpace Real (Tensor0SModel 1 Real E) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) 1
  simp only [Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  unfold TensorLieDeriv.covariantDeriv_tensor0SModelWithin
  rw [TensorLieDeriv.covariantDeriv_tensor0SModelAt_one_apply_basis
    (basis := Module.finBasis Real E)
    (dα_X :=
      (fderivWithin Real (fun y => α.toFun ((extChartAt I x₀).symm y))
        (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
        (extChartAt I x₀ x₀))
        (VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (⇑X) (Set.range I) (extChartAt I x₀ x₀)))
    (ΓX := connectionEndomorphismInChart (𝕜 := Real) (I := I)
      cov (fun x => X x) x₀ (extChartAt I x₀ x₀))
    (α := (fun y => α.toFun ((extChartAt I x₀).symm y)) (extChartAt I x₀ x₀))
    (j := j)]
  rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  simp only [modelDeriv0SAt, coordComponent0SAt, component0S,
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
  rfl

/-- Coordinate-frame component formula for one-forms, after supplying the
derivative-identification bridge. -/
theorem nabla0S_one_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
  rw [nabla0S_one_model_coord (I := I) cov X α x₀ j, hderiv]

end Coordinates
end RicciFlower
