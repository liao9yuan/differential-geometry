import RicciFlower.Tensor.RSTensor.NablaOnTensors.RawDefs
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.Multilinear.Basis
import RicciFlower.VectorBundle.PartialMfderiv

/-!
# Regularity for tensor covariant derivatives

This module proves regularity for the raw `nabla0SFun` API using the intrinsic local-frame
route. Coordinate component modules should consume these theorems rather than carry the
smoothness proof themselves.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : Fin (Module.finrank 𝕜 E),
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  apply b.ext_elem
  intro i
  let L : E →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
  have hcomp :
      fderivWithin 𝕜 (fun z : E => L (F z)) u y =
        L.comp (fderivWithin 𝕜 F u y) := by
    have hlin :
        DifferentiableAt 𝕜 (fun w : E => L w) (F y) :=
      L.differentiableAt
    have hcomp0 :=
      (fderivWithin_comp (x := y) (f := F)
        (g := fun w : E => L w) (s := u) (t := Set.univ)
        (by simpa using hlin.differentiableWithinAt)
        hF (by intro z hz; simp) hu)
    rw [L.fderivWithin (s := Set.univ) (x := F y) uniqueDiffWithinAt_univ] at hcomp0
    simpa [L, b, Function.comp_def] using hcomp0
  have hcoord' :
      b.coord i ((fderivWithin 𝕜 F u y) Xy) =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    change L ((fderivWithin 𝕜 F u y) Xy) =
      fderivWithin 𝕜 (fun z : E => L (F z)) u y Xy
    rw [hcomp]
    simp [L, LinearMap.coe_toContinuousLinearMap']
  have hcoord :
      b.repr ((fderivWithin 𝕜 F u y) Xy) i =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    simpa [Module.Basis.coord_apply] using hcoord'
  rw [hcoord]
  change (fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y) Xy =
    b.coord i
      (∑ j : Fin (Module.finrank 𝕜 E),
        (fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord j (F z)) u y) Xy •
          (Module.finBasis 𝕜 E) j)
  rw [map_sum]
  simp only [b, Module.Basis.coord_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hrepr :
        ((Module.finBasis 𝕜 E).repr ((Module.finBasis 𝕜 E) j)) i = 0 := by
      have hji : i ≠ j := fun h => hj h.symm
      rw [(Module.finBasis 𝕜 E).repr_self j]
      exact Finsupp.single_eq_of_ne hji
    rw [hrepr]
    simp
  · intro hi
    simp at hi

private theorem fderivWithin_chart_scalar_eq_extDerivFun
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (φ : E -> 𝕜) (f : M -> 𝕜)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀)
    (heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) :
    fderivWithin 𝕜 φ (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) f x₀ (X x₀) := by
  let z₀ : E := extChartAt I x₀ x₀
  have hzRange : z₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hfd :
      fderivWithin 𝕜 φ (Set.range I) z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  change
    fderivWithin 𝕜 φ (Set.range I) z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀) =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf.mfderiv, hfd]
  rfl

private theorem tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i := by
  classical
  let F : E -> E := tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  have hbasis := fderivWithin_eq_sum_basis_coord
    (F := F) (u := Set.range I) (y := extChartAt I x₀ x₀)
    (Xy := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))
    hVmodel (I.uniqueDiffOn (extChartAt I x₀ x₀)
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  rw [hbasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  let f : M -> 𝕜 := fun p : M => b.coord i (F (extChartAt I x₀ p))
  let φ : E -> 𝕜 := fun y : E => b.coord i (F y)
  have hφ : DifferentiableWithinAt 𝕜 φ (Set.range I) (extChartAt I x₀ x₀) := by
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp_differentiableWithinAt
      (x := extChartAt I x₀ x₀) hVmodel
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
      (extChartAt I x₀).right_inv hy
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    change b.coord i (F y) =
      b.coord i (F (extChartAt I x₀ ((extChartAt I x₀).symm y)))
    rw [hright]
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f (hcoord i) heq

theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
  classical
  let b := Module.finBasis 𝕜 E
  let zfun : Fin (Module.finrank 𝕜 E) -> M -> 𝕜 :=
    fun i p =>
      b.coord i
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p))
  have hsum := covariantDerivative_modelInChart_center_eq_sum
    (𝕜 := 𝕜) (I := I) cov (fun x => X x) V x₀ hV hcoord
  have hderiv :=
    tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
      (I := I) X V x₀ hVmodel hcoord
  calc
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀)
        =
      (∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I) (zfun i) x₀ (X x₀) • b i) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          simpa [b, zfun] using hsum
    _ =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          rw [hderiv]

private theorem tangentFieldModelInChart_center_symmL
    (V : (x : M) -> TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) =
      V x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  unfold tangentFieldModelInChart
  change e.symmL 𝕜 x₀
      (e.continuousLinearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀)))) =
    V x₀
  rw [extChartAt_to_inv]
  exact e.symmL_continuousLinearMapAt
    (R := 𝕜) (FiberBundle.mem_baseSet_trivializationAt' x₀) (V x₀)

private theorem tensor0SModelInChart_apply_modelSlots_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
            (extChartAt I x₀ x₀)) =
      A x₀ (fun a : Fin s => V a x₀) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext a
  exact tangentFieldModelInChart_center_symmL (I := I) (V a) x₀

private theorem tensor0SModelInChart_apply_update_modelSlot_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      A x₀ (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_self, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) W x₀
  · simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_of_ne hb, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀

private theorem fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ (fun x => α x) y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ (fun x => α x) y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

private theorem fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ β y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ β y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => β p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

set_option backward.isDefEq.respectTransparency false in
private theorem fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun {r s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r s x₀ (fun x => T x) y
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r x₀ β y))
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := inferInstance
  let φ : E -> 𝕜 :=
    fun y : E =>
      (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r s x₀ (fun x => T x) y
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β y))
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => (T p (β p)) (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    unfold tensorRSModelInChart tensorRSModelAt
    rw [TensorRSSpace.trivializationAt_apply]
    · congr 2
      · unfold tensor0SModelInChart tensor0SModelAt
        let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀
        let p := (extChartAt I x₀).symm y
        have hbaseβ : p ∈ eβ.baseSet := hbase
        change eβ.symmL 𝕜 p ((eβ ⟨p, β p⟩).2) = β p
        have hcoord : (eβ ⟨p, β p⟩).2 = eβ.continuousLinearMapAt 𝕜 p (β p) := by
          rw [Bundle.Trivialization.continuousLinearMapAt_apply]
          rw [eβ.coe_linearMapAt_of_mem (R := 𝕜) hbaseβ]
        rw [hcoord]
        exact eβ.symmL_continuousLinearMapAt (R := 𝕜) hbaseβ (β p)
      · funext a
        unfold tangentFieldModelInChart
        exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
          (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
    · exact hbase
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

private noncomputable def localCovariantDerivTensor0SAt (r : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M) : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ :=
  (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm x₀
    (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I))
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))

set_option backward.isDefEq.respectTransparency false in
private theorem localCovariantDerivTensor0SAt_eval_moving_raw {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
        x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let βm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) r :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin r -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin r -> E := fun a => Vm a y₀
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := r) βm Vm (Set.range I) y₀ Xmodel
      hβmodel hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => βm y (fun a : Fin r => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) := by
    simpa [βm, Vm, Xmodel, y₀] using
      fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X β V x₀ hpair
  have hcov_model : ∀ a : Fin r,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin r =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin r => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀) =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := by
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    let Mβ : Tensor0SModel r 𝕜 E :=
      covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀
    have hcoordEval :
        ((eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
            slots =
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
            (fun a : Fin r => V a x₀) := by
      have h := Tensor0SSpace.trivializationAt_apply
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        slots
      rw [hslots_center] at h
      exact h
    have hmodel :
        (eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2 =
          Mβ := by
      unfold localCovariantDerivTensor0SAt
      change (eβ ⟨x₀, eβ.symm x₀ Mβ⟩).2 = Mβ
      rw [eβ.apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀)]
    calc
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀)
          = ((eβ ⟨x₀, localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
              slots := hcoordEval.symm
      _ = Mβ slots := by rw [hmodel]
  have hcorr_sum :
      ∑ a : Fin r,
        βm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) β V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀)
        =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := hleft_model
    _ =
      fderivWithin 𝕜 βm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin r, βm y₀ (Function.update slots a (Γ (slots a))) := by
          simp [covariantDeriv_tensor0SModelWithin_apply_slots, βm, Xmodel, Γ, slots, y₀]
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          βm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(βm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRSModelInChart_apply_modelSlots_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (βm : Tensor0SModel r 𝕜 E) (slots : Fin s -> E) (x₀ : M) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀) βm) slots =
      (A x₀
        ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ βm))
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
            (slots a)) := by
  rw [tensorRSModelInChart, extChartAt_to_inv]
  exact TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r s
    (FiberBundle.mem_baseSet_trivializationAt' x₀) (A x₀) βm slots

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRSModelInChart_apply_update_modelOutputSlot_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β (extChartAt I x₀ x₀)))
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      (A x₀ (β x₀)) (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensorRSModelInChart_apply_modelSlots_center]
  have hβ :
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
          (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β (extChartAt I x₀ x₀)) =
        β x₀ := by
    unfold tensor0SModelInChart tensor0SModelAt
    rw [extChartAt_to_inv]
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
    have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    rw [hcoord]
    exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
      (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
  have hslots :
      (fun b : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          ((Function.update
            (fun b : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
                (extChartAt I x₀ x₀))
            a
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
              (extChartAt I x₀ x₀))) b)) =
        Function.update (fun b : Fin s => V b x₀) a (W x₀) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Function.update_self]
      exact tangentFieldModelInChart_center_symmL (I := I) W x₀
    · simp only [Function.update_of_ne hb]
      exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀
  rw [hβ, hslots]

set_option backward.isDefEq.respectTransparency false in
private theorem nablaRSFun_eval_moving_raw {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let Tm : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x₀ (fun x => T x)
  let βm : E -> Tensor0SModel r 𝕜 E :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hTdiff : DifferentiableWithinAt 𝕜 Tm (Set.range I) y₀ := by
    have hcd := (T.contMDiff x₀)
    rw [contMDiffAt_section] at hcd
    have hsymm :
        ContMDiffWithinAt 𝓘(𝕜, E) I (⊤ : WithTop ℕ∞)
          (extChartAt I x₀).symm (Set.range I) y₀ := by
      simpa [y₀] using
        contMDiffWithinAt_extChartAt_symm_range_self
          (I := I) (n := (⊤ : WithTop ℕ∞)) x₀
    have hmodel_center :
        ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) (⊤ : WithTop ℕ∞)
          (fun x : M => tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ x (T x))
          ((extChartAt I x₀).symm y₀) := by
      simpa [tensorRSModelAt, y₀, extChartAt_to_inv] using hcd
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := y₀) hmodel_center hsymm
    have hdiff := hcomp.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [Tm, tensorRSModelInChart, y₀] using hdiff
  have hprod := covariantDeriv_tensorRSModelWithin_eval_derivation
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    Tm βm Vm
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (Set.range I) y₀ hTdiff hβmodel hVmodel
    (I.uniqueDiffOn y₀
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [Tm, βm, Vm, Xmodel, y₀] using
      fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun
        (I := I) X T β V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
        (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := by
    let eRS := trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀
    let F₀ : TensorRSSpace r s I x₀ :=
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀
    let MRS : TensorRSModel r s 𝕜 E :=
      covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        Tm (Set.range I) y₀
    have hβcenter :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ (βm y₀) =
          β x₀ := by
      unfold βm tensor0SModelInChart tensor0SModelAt
      rw [extChartAt_to_inv]
      let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀
      change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
      have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
        rw [Bundle.Trivialization.continuousLinearMapAt_apply]
        rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
          (FiberBundle.mem_baseSet_trivializationAt' x₀)]
      rw [hcoord]
      exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
    have hcoordEval :
        ((eRS ⟨x₀, F₀⟩).2 (βm y₀)) slots =
          F₀ (β x₀) (fun a : Fin s => V a x₀) := by
      have h := TensorRSSpace.trivializationAt_apply
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r s
        (FiberBundle.mem_baseSet_trivializationAt' x₀) F₀ (βm y₀) slots
      rw [hβcenter, hslots_center] at h
      exact h
    have hmodel :
        (eRS ⟨x₀, F₀⟩).2 = MRS := by
      unfold F₀ MRS nablaRSFun TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection
        TensorLieDeriv.mcovariantDeriv_tensorRSWithin
      change (eRS ⟨x₀, eRS.symm x₀
        (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r s x₀ (fun x => T x))
          ((extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I)
          (extChartAt I x₀ x₀))⟩).2 = MRS
      rw [eRS.apply_mk_symm
        (mem_baseSet_trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)]
      simp [MRS, Tm, y₀]
    calc
      F₀ (β x₀) (fun a : Fin s => V a x₀)
          = ((eRS ⟨x₀, F₀⟩).2 (βm y₀)) slots := hcoordEval.symm
      _ = (MRS (βm y₀)) slots := by rw [hmodel]
  have hinput :
      (Tm y₀
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          βm (Set.range I) y₀)) slots =
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) := by
    have h := tensorRSModelInChart_apply_modelSlots_center
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (A := fun x => T x)
      (βm := covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀)
      (slots := slots) x₀
    rw [hslots_center] at h
    simpa [Tm, βm, localCovariantDerivTensor0SAt, Xmodel, Γ, y₀] using h
  have houtput_sum :
      (∑ a : Fin s,
        (Tm y₀ (βm y₀))
          (Function.update (fun b : Fin s => Vm b y₀) a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀)))) =
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    simpa [Tm, βm, Vm, slots, y₀] using
      tensorRSModelInChart_apply_update_modelOutputSlot_center
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (r := r) (s := s) (A := fun x => T x) (β := β)
        (V := V) (W := fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀)
        =
      (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := hleft_model
    _ =
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel -
        (Tm y₀
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              (fun x => X x) (Set.range I))
            (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
            βm (Set.range I) y₀))
          (fun a : Fin s => Vm a y₀) -
        ∑ a : Fin s,
          (Tm y₀ (βm y₀))
            (Function.update
              (fun b : Fin s => Vm b y₀)
              a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀))) := by
          simpa [Xmodel, Γ, slots] using hprod
    _ =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hpair_deriv, hinput, houtput_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise moving-slot derivation formula for `nabla0SFun` in arbitrary
covariant valence.

This is the `(0,s)` version of
`nabla0SFun_one_eval_coordFrame_moving_raw`. The hypotheses are deliberately
local: the moving slots only need the fixed-chart model differentiability needed
by the product rule and the vector-field covariant-derivative chart formula. -/
theorem nabla0SFun_eval_coordFrame_moving_raw {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀)
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let αm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x₀ (fun x => α x)
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hαdiff : DifferentiableWithinAt 𝕜 αm (Set.range I) y₀ := by
    have hcd := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s x₀ α
    have hdiff := hcd.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [αm, y₀] using hdiff
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := s) αm Vm (Set.range I) y₀ Xmodel
      hαdiff hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => αm y (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [αm, Vm, Xmodel, y₀] using
      fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X α V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hfixed := fixedChartNabla0SModel_apply_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) s cov X α x₀ y₀ slots
  have hself := nabla0SFun_apply_selfChart_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov X α x₀ slots
  have hslot :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm, tangentConstInChart] using
      tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hcorr_sum :
      ∑ a : Fin s,
        αm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin s,
        α x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) (fun x => α x) V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀)
        =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x₀)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) := by
          rw [hslot]
    _ = fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := (⊤ : WithTop ℕ∞)) s cov X α x₀ y₀ slots := hself
    _ =
      fderivWithin 𝕜 αm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin s, αm y₀ (Function.update slots a (Γ (slots a))) := by
          simpa [αm, Xmodel, Γ, y₀] using hfixed
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          αm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(αm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]

private theorem tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContDiffWithinAt 𝕜 (∞ : WithTop ℕ∞)
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        ((fun p : M => (e ⟨p, V p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have heq :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
        =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
      (fun p : M => (e ⟨p, V p⟩).2) ∘ (extChartAt I x₀).symm := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hp_base : (extChartAt I x₀).symm y ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
    have hcoe :
        ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm y)) =
          fun z => (e ⟨(extChartAt I x₀).symm y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
    unfold tangentFieldModelInChart
    change e.linearMapAt 𝕜 ((extChartAt I x₀).symm y)
        (V ((extChartAt I x₀).symm y)) =
      (e ⟨(extChartAt I x₀).symm y, V ((extChartAt I x₀).symm y)⟩).2
    rw [hcoe]
  have hmdiff :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀) := by
    refine hfixed.congr_of_eventuallyEq heq ?_
    have hy : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
      mem_extChartAt_target (I := I) x₀
    have hp_source :
        (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hp_base : (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ e.baseSet := by
      simp [e, TangentBundle.trivializationAt_baseSet] at hp_source ⊢
    have hcoe :
        ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
          fun z => (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀), z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
    unfold tangentFieldModelInChart
    change e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
      (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀),
        V ((extChartAt I x₀).symm (extChartAt I x₀ x₀))⟩).2
    rw [hcoe]
  exact hmdiff.contDiffWithinAt

private theorem tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    DifferentiableWithinAt 𝕜
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact (tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (I := I) V x₀ hV).differentiableWithinAt (by simp)

private theorem tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (i : Fin (Module.finrank 𝕜 E)) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hscalar :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2)) x₀ :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).contMDiffAt.comp
      x₀ hcoord
  have heq :
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p)))
        =ᶠ[𝓝 x₀]
      fun p : M => (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
    have hp_source : p ∈ (extChartAt I x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
    have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
      (extChartAt I x₀).left_inv hp_source
    have hcoe :
        ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp
    unfold tangentFieldModelInChart
    rw [hleft]
    change (Module.finBasis 𝕜 E).coord i
        (e.linearMapAt 𝕜 p (V p)) =
      (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2)
    rw [hcoe]
  exact (hscalar.congr_of_eventuallyEq heq).mdifferentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SConstInChart_contMDiffAt_of_mem {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) {x : M}
    (hx : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun p : M => Tensor0SSpace r I p) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x := by
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx' : x ∈ e.baseSet := by simpa [e] using hx
  refine (e.contMDiffAt_section_iff hx').mpr ?_
  have hconst : ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
      (fun _ : M => β) x := contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx'] with p hp
  have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hp
  change (e ⟨p, e.symmL 𝕜 p β⟩).2 = β
  simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
    (e.continuousLinearMapAt_symmL (R := 𝕜) hp β)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SConstInChart_contMDiffAt {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
  exact tensor0SConstInChart_contMDiffAt_of_mem
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    x₀ β (mem_baseSet_trivializationAt
      (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SModelInChart_contDiffWithinAt_center_of_contMDiffAt {r : ℕ}
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀) :
    ContDiffWithinAt 𝕜 (∞ : WithTop ℕ∞)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, β p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hβ
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, β p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel r 𝕜 E)
        (∞ : WithTop ℕ∞)
        ((fun p : M => (e ⟨p, β p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have heq :
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β
        =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
      (fun p : M => (e ⟨p, β p⟩).2) ∘ (extChartAt I x₀).symm := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    simp [tensor0SModelInChart, tensor0SModelAt, e]
  have hmdiff :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel r 𝕜 E)
        (∞ : WithTop ℕ∞)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β)
        (Set.range I) (extChartAt I x₀ x₀) := by
    refine hfixed.congr_of_eventuallyEq heq ?_
    simp [tensor0SModelInChart, tensor0SModelAt, e]
  exact hmdiff.contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt {r : ℕ}
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀) :
    DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) :=
  (tensor0SModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (I := I) β x₀ hβ).differentiableWithinAt (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorRS_eval_contMDiffAt {r s : ℕ}
    (T : (p : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s p)
    (β : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p)
    (V : Fin s -> (p : M) -> TangentSpace I p) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, T p⟩ :
          TotalSpace (TensorRSModel r s 𝕜 E)
            (fun p : M => TensorRSSpace r s I p))) x₀)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀)
    (hV : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀ := by
  have hApplied :
      ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, T p (β p)⟩ :
            TotalSpace (Tensor0SModel s 𝕜 E)
              (fun p : M => Tensor0SSpace s I p))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := 𝕜) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r 𝕜 E) (F₂ := Tensor0SModel s 𝕜 E)
      (E₁ := fun p : M => Tensor0SSpace r I p)
      (E₂ := fun p : M => Tensor0SSpace s I p)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun p : M => T p) (v := fun p : M => β p) hT hβ
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun p : M => T p (β p)) hApplied
    (v := V) hV
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of a `(0,s)` tensor field evaluated on the chart-constant
tangent fields from `trivializationAt E (TangentSpace I) x₀`.

This is the tensor-layer replacement for the coordinate-frame coefficient
smoothness lemma. -/
theorem tensor0S_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        α y
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) y))
      x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hframe :
      ∀ a : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y,
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                ((Module.finBasis 𝕜 E) (slots a)) y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
            ((Module.finBasis 𝕜 E) (slots a)) :
            (p : M) -> TangentSpace I p)) := by
      simpa [e] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun a : Fin s =>
      tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
        ((Module.finBasis 𝕜 E) (slots a)))
    (hv := hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

private theorem tangentConst_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (v : E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hW_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M =>
          (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (Xinf p))) := by
    simpa [e, Xinf] using
      (covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        cov hcov Xinf x₀ v)
  exact ((hW_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)).of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of one chart-constant correction term in the `(0,s)` tensor
derivation formula. -/
theorem tensor0S_eval_tangentConst_covariantDerivative_slot_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) (a : Fin s) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        α p
          (Function.update
            (fun b : Fin s =>
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                ((Module.finBasis 𝕜 E) (slots b)) p)
            a
            ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a))) p) (X p))))
      x₀ := by
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  let W : (p : M) -> TangentSpace I p :=
    fun p : M =>
      (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
        ((Module.finBasis 𝕜 E) (slots a))) p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    simpa [W] using
      tangentConst_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ ((Module.finBasis 𝕜 E) (slots a))
  have hframe :
      ∀ i : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p,
              Function.update
                (fun b : Fin s =>
                  tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                    ((Module.finBasis 𝕜 E) (slots b)) p)
                a
                (W p) i⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa using hW
    · let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
      have hbase_on :
          CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
            (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots i)) :
              (p : M) -> TangentSpace I p)) := by
        simpa [e] using
          (tangentConstInChart_contMDiffOn_baseSet
            (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
            x₀ ((Module.finBasis 𝕜 E) (slots i)))
      have hbase := (hbase_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
      simpa [Function.update, hi] using hbase
  have hEval := TensorMultilinear.contMDiffAt_section_apply
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
    (v := fun i : Fin s =>
      fun p : M =>
        Function.update
          (fun b : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots b)) p)
          a
          (W p) i)
    (hv := hframe)
  simpa [αinf, W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    using hEval

set_option backward.isDefEq.respectTransparency false in
private theorem localCovariantDerivTensor0SAt_constInChart_eval_tangentConstInChart_contMDiffAt
    {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (β : Tensor0SModel r 𝕜 E)
    (slots : Fin r -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
          (fun y : M => Tensor0SSpace.constInChart
            (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p)
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) p)) x₀ := by
  let βsec : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p :=
    fun p : M => Tensor0SSpace.constInChart
      (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p
  let V : Fin r -> (p : M) -> TangentSpace I p :=
    fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
      ((Module.finBasis 𝕜 E) (slots a))
  let pair : M -> 𝕜 := fun p : M => βsec p (fun a : Fin r => V a p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hβsec : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, βsec p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
    simpa [βsec] using
      tensor0SConstInChart_contMDiffAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ β
  have hV :
      ∀ a : Fin r,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M => (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          x₀ := by
    intro a
    let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [e, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    have hEval := TensorMultilinear.contMDiffAt_section_apply
      (I := I) (M := M) (n := r) (x₀ := x₀)
      (T := βsec) hβsec
      (v := V) hV
    simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hEval
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
    simpa [Xinf] using RicciFlower.extDerivFun_apply_contMDiffAt I hpair Xinf
  have hcorr_sum :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          ∑ a : Fin r,
            βsec p
              (Function.update
                (fun b : Fin r => V b p)
                a
                ((cov (V a) p) (X p)))) x₀ := by
    apply ContMDiffAt.sum
    intro a _
    let W : (p : M) -> TangentSpace I p := fun p : M => (cov (V a) p) (X p)
    have hW :
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          x₀ := by
      simpa [W, V] using
        tangentConst_covariantDeriv_apply_contMDiffAt
          (I := I) cov hcov X x₀ ((Module.finBasis 𝕜 E) (slots a))
    have hframe :
        ∀ i : Fin r,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun p : M =>
              (⟨p, Function.update (fun b : Fin r => V b p) a (W p) i⟩ :
                TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
      intro i
      by_cases hi : i = a
      · subst hi
        simpa using hW
      · simpa [Function.update, hi] using hV i
    have hEval := TensorMultilinear.contMDiffAt_section_apply
      (I := I) (M := M) (n := r) (x₀ := x₀)
      (T := βsec) hβsec
      (v := fun i : Fin r => fun p : M =>
        Function.update (fun b : Fin r => V b p) a (W p) i)
      (hv := hframe)
    simpa [W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hEval
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            ∑ a : Fin r,
              βsec p
                (Function.update
                  (fun b : Fin r => V b p)
                  a
                  ((cov (V a) p) (X p)))) x₀ :=
    hderiv.sub hcorr_sum
  refine hmain.congr_of_eventuallyEq ?_
  let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx₀Tan : x₀ ∈ eTan.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀β : x₀ ∈ eβ.baseSet := by
    simpa [eβ] using
      (mem_baseSet_trivializationAt
        (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
  filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan,
    eβ.open_baseSet.mem_nhds hx₀β] with p hpTan hpβ
  have hβ_p : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, βsec y⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun y : M => Tensor0SSpace r I y))) p := by
    simpa [βsec] using
      tensor0SConstInChart_contMDiffAt_of_mem
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ β hpβ
  have hV_p :
      ∀ a : Fin r,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          p := by
    intro a
    have hconst_on :
        CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [eTan, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on p hpTan).contMDiffAt (eTan.open_baseSet.mem_nhds hpTan)
  have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
    have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
      have hEval := TensorMultilinear.contMDiffAt_section_apply
        (I := I) (M := M) (n := r) (x₀ := p)
        (T := βsec) hβ_p
        (v := V) hV_p
      simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
        using hEval
    exact hpair_p.mdifferentiableAt (by simp)
  have hβmodel_p :
      DifferentiableWithinAt 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r p βsec)
        (Set.range I) (extChartAt I p p) :=
    tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) βsec p hβ_p
  have hV_md : ∀ a : Fin r, MDiffAt (T% (V a)) p :=
    fun a => (hV_p a).mdifferentiableAt (by simp)
  have hVmodel_p : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
        (Set.range I) (extChartAt I p p) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_p a)
  have hcoord_p : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
              (extChartAt I p q))) p :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_p a) i
  rw [localCovariantDerivTensor0SAt_eval_moving_raw
    (I := I) cov X βsec V p hpair_md hβmodel_p hV_md hVmodel_p hcoord_p]

set_option backward.isDefEq.respectTransparency false in
private theorem localCovariantDerivTensor0SAt_constInChart_contMDiffAt
    {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p,
          localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
            (fun y : M => Tensor0SSpace.constInChart
              (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p :=
    fun p : M =>
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
        (fun y : M => Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  rw [contMDiffAt_section]
  let g : M -> Tensor0SModel r 𝕜 E := fun p : M => (e ⟨p, F p⟩).2
  change ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞) g x₀
  let B := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) b r
  rw [show g = fun p : M => B.equivFun.symm (B.equivFun (g p)) from
      funext fun p => (B.equivFun.symm_apply_apply (g p)).symm]
  exact (B.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
    (contMDiffAt_pi_space.mpr fun σ => by
      have hcoeff :=
        localCovariantDerivTensor0SAt_constInChart_eval_tangentConstInChart_contMDiffAt
          (I := I) cov hcov X x₀ β σ
      refine hcoeff.congr_of_eventuallyEq ?_
      let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀Tan : x₀ ∈ eTan.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
      filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan] with p hp
      change B.repr (g p) σ =
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
          (fun y : M => Tensor0SSpace.constInChart
            (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p)
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (σ a)) p)
      rw [continuousMultilinearMap_basis_repr]
      change ((trivializationAt (Tensor0SModel r 𝕜 E)
          (Bundle.continuousMultilinearMap 𝕜 r E (TangentSpace I : M -> Type _)) x₀
          ⟨p, F p⟩).2)
          (fun a : Fin r => b (σ a)) =
        F p
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
      change (F p).compContinuousLinearMap
          (fun _ : Fin r =>
            (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
          (fun a : Fin r => b (σ a)) =
        F p
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar coefficient smoothness for `nabla0SFun s` on chart-constant
tangent slots. -/
theorem nabla0SFun_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) p)) x₀ := by
  let V : Fin s -> (p : M) -> TangentSpace I p :=
    fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
      ((Module.finBasis 𝕜 E) (slots a))
  let pair : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, V] using
      tensor0S_eval_tangentConstInChart_contMDiffAt
        (I := I) α x₀ slots
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
    simpa [Xinf] using RicciFlower.extDerivFun_apply_contMDiffAt I hpair Xinf
  have hcorr_sum :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          ∑ a : Fin s,
            α p
              (Function.update
                (fun b : Fin s => V b p)
                a
                ((cov (V a) p) (X p)))) x₀ := by
    apply ContMDiffAt.sum
    intro a _
    simpa [V] using
      tensor0S_eval_tangentConst_covariantDerivative_slot_contMDiffAt
        (I := I) cov hcov X α x₀ slots a
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            ∑ a : Fin s,
              α p
                (Function.update
                  (fun b : Fin s => V b p)
                  a
                  ((cov (V a) p) (X p)))) x₀ :=
    hderiv.sub hcorr_sum
  refine hmain.congr_of_eventuallyEq ?_
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
  have hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    intro a
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [e, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on p hp).contMDiffAt (e.open_baseSet.mem_nhds hp)
  have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
    have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
      have hα_top := α.contMDiff p
      have hα := hα_top.of_le
        (by simp : (∞ : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
      have hEval := TensorMultilinear.contMDiffAt_section_apply
        (I := I) (M := M) (n := s) (x₀ := p)
        (T := fun y : M => α y) hα
        (v := fun a : Fin s => V a)
        (hv := hV_at)
      simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
        using hEval
    exact hpair_p.mdifferentiableAt (by simp)
  have hV_md : ∀ a : Fin s, MDiffAt (T% (V a)) p :=
    fun a => (hV_at a).mdifferentiableAt (by simp)
  have hVmodel_p : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
        (Set.range I) (extChartAt I p p) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_at a)
  have hcoord_p : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
              (extChartAt I p q))) p :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_at a) i
  rw [nabla0SFun_eval_coordFrame_moving_raw
    (I := I) cov X V α p hpair_md hV_md hVmodel_p hcoord_p]

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the canonical raw covariant derivative for `(0,s)` tensor
fields, proved by local-frame coefficients in the tangent-bundle
trivialization. -/
theorem nabla0S_reg (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s) :
    Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hsec :
      ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, F p⟩ :
            TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p))) := by
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
      (∞ : WithTop ℕ∞) b F).mpr ?_
    intro σ x₀
    have hcoeff :=
      nabla0SFun_eval_tangentConstInChart_contMDiffAt
        (I := I) cov hcov X α x₀ σ
    refine hcoeff.congr_of_eventuallyEq ?_
    let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
    rw [continuousMultilinearMap_basis_repr]
    change ((trivializationAt (Tensor0SModel s 𝕜 E)
        (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M -> Type _)) x₀
        ⟨p, F p⟩).2)
        (fun a : Fin s => b (σ a)) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
    change (F p).compContinuousLinearMap
        (fun _ : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
        (fun a : Fin s => b (σ a)) =
      F p
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr
  exact hsec

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the canonical raw covariant derivative for mixed `(r,s)`
tensor fields, proved through Hom coordinates and local `(0,r)` input
regularity. -/
theorem nablaRS_reg (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s) :
    NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_smooth (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) (n := (∞ : WithTop ℕ∞)) r s
  letI : FiniteDimensional 𝕜 (TensorRSModel r s 𝕜 E) := inferInstance
  let F : (p : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s p :=
    fun p : M =>
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T p
  intro x₀
  rw [contMDiffAt_section]
  let e := trivializationAt (TensorRSModel r s 𝕜 E)
    (fun p : M => TensorRSSpace r s I p) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (TensorRSModel r s 𝕜 E) (fun p : M => TensorRSSpace r s I p) x₀)
  let G : M -> TensorRSModel r s 𝕜 E := fun p => (e ⟨p, F p⟩).2
  let d := Module.finrank 𝕜 E
  let bE : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hG : ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E)
      (∞ : WithTop ℕ∞) G x₀ := by
    refine contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
      (I := I) (bE := bE) (G := G) (x₀ := x₀)
      (n := (∞ : WithTop ℕ∞)) ?_
    intro ρ σ
    let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
    let βρ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ
    let vσ : Fin s -> E := fun a => bE (σ a)
    have hintrinsic :
        ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (F p (Tensor0SSpace.constInChart
              (𝕜 := 𝕜) (I := I) (M := M) r x₀ βρ p))
              (fun a : Fin s => eTan.symmL 𝕜 p (vσ a))) x₀ := by
      let βsec : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) r p :=
        fun p : M => Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ βρ p
      let V : Fin s -> (p : M) -> TangentSpace I p :=
        fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (vσ a)
      let pair : M -> 𝕜 := fun p : M => (T p (βsec p)) (fun a : Fin s => V a p)
      let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
        ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
      have hT : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, T p⟩ :
              TotalSpace (TensorRSModel r s 𝕜 E)
                (fun p : M => TensorRSSpace r s I p))) x₀ :=
        (T.contMDiff x₀).of_le (by simp :
          (∞ : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
      have hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, βsec p⟩ :
              TotalSpace (Tensor0SModel r 𝕜 E)
                (fun p : M => Tensor0SSpace r I p))) x₀ := by
        simpa [βsec] using
          tensor0SConstInChart_contMDiffAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ βρ
      have hV : ∀ a : Fin s,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun p : M => (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
            x₀ := by
        intro a
        have hx₀Tan : x₀ ∈ eTan.baseSet := by
          dsimp [eTan]
          exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
        have hconst_on :
            CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
          simpa [eTan, V, vσ] using
            (tangentConstInChart_contMDiffOn_baseSet
              (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
              x₀ (vσ a))
        exact (hconst_on x₀ hx₀Tan).contMDiffAt (eTan.open_baseSet.mem_nhds hx₀Tan)
      have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
        simpa [pair] using
          tensorRS_eval_contMDiffAt
            (I := I) (T := fun p : M => T p) (β := βsec) (V := V) x₀ hT hβ hV
      have hderiv :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
        simpa [Xinf] using RicciFlower.extDerivFun_apply_contMDiffAt I hpair Xinf
      have hinput :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              (T p
                (localCovariantDerivTensor0SAt
                  (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
                (fun a : Fin s => V a p)) x₀ := by
        have hβcorr :
            ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
              (∞ : WithTop ℕ∞)
              (fun p : M =>
                (⟨p,
                  localCovariantDerivTensor0SAt
                    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p⟩ :
                  TotalSpace (Tensor0SModel r 𝕜 E)
                    (fun p : M => Tensor0SSpace r I p))) x₀ := by
          simpa [βsec] using
            localCovariantDerivTensor0SAt_constInChart_contMDiffAt
              (I := I) cov hcov X x₀ βρ
        exact tensorRS_eval_contMDiffAt
          (I := I) (T := fun p : M => T p)
          (β := fun p : M =>
            localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p)
          (V := V) x₀ hT hβcorr hV
      have houtput :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              ∑ a : Fin s,
                (T p (βsec p))
                  (Function.update (fun b : Fin s => V b p) a
                    ((cov (V a) p) (X p)))) x₀ := by
        apply ContMDiffAt.sum
        intro a _
        let W : (p : M) -> TangentSpace I p := fun p : M => (cov (V a) p) (X p)
        have hW :
            ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
              (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
              x₀ := by
          simpa [W, V] using
            tangentConst_covariantDeriv_apply_contMDiffAt
              (I := I) cov hcov X x₀ (vσ a)
        have hVupdate : ∀ i : Fin s,
            ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
              (fun p : M =>
                (⟨p, Function.update (fun b : Fin s => V b p) a (W p) i⟩ :
                  TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
          intro i
          by_cases hi : i = a
          · subst hi
            simpa using hW
          · simpa [Function.update, hi] using hV i
        exact tensorRS_eval_contMDiffAt
          (I := I) (T := fun p : M => T p) (β := βsec)
          (V := fun i : Fin s => fun p : M =>
            Function.update (fun b : Fin s => V b p) a (W p) i)
          x₀ hT hβ hVupdate
      have hmain :
          ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
            (fun p : M =>
              extDerivFun (I := I) pair p (X p) -
                (T p
                  (localCovariantDerivTensor0SAt
                    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
                  (fun a : Fin s => V a p) -
                ∑ a : Fin s,
                  (T p (βsec p))
                    (Function.update (fun b : Fin s => V b p) a
                      ((cov (V a) p) (X p)))) x₀ :=
        (hderiv.sub hinput).sub houtput
      refine hmain.congr_of_eventuallyEq ?_
      let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
        (fun p : M => Tensor0SSpace r I p) x₀
      have hx₀Tan : x₀ ∈ eTan.baseSet := by
        dsimp [eTan]
        exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀β : x₀ ∈ eβ.baseSet := by
        simpa [eβ] using
          (mem_baseSet_trivializationAt
            (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
      filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan,
        eβ.open_baseSet.mem_nhds hx₀β] with p hpTan hpβ
      have hT_p : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun q : M =>
            (⟨q, T q⟩ :
              TotalSpace (TensorRSModel r s 𝕜 E)
                (fun q : M => TensorRSSpace r s I q))) p :=
        (T.contMDiff p).of_le (by simp :
          (∞ : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
      have hβ_p : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
          (∞ : WithTop ℕ∞)
          (fun q : M =>
            (⟨q, βsec q⟩ :
              TotalSpace (Tensor0SModel r 𝕜 E)
                (fun q : M => Tensor0SSpace r I q))) p := by
        simpa [βsec] using
          tensor0SConstInChart_contMDiffAt_of_mem
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ βρ hpβ
      have hV_p : ∀ a : Fin s,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun q : M => (⟨q, V a q⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
            p := by
        intro a
        have hconst_on :
            CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
          simpa [eTan, V, vσ] using
            (tangentConstInChart_contMDiffOn_baseSet
              (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
              x₀ (vσ a))
        exact (hconst_on p hpTan).contMDiffAt (eTan.open_baseSet.mem_nhds hpTan)
      have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
        have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
          simpa [pair] using
            tensorRS_eval_contMDiffAt
              (I := I) (T := fun q : M => T q) (β := βsec) (V := V) p
              hT_p hβ_p hV_p
        exact hpair_p.mdifferentiableAt (by simp)
      have hβmodel_p :
          DifferentiableWithinAt 𝕜
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r p βsec)
            (Set.range I) (extChartAt I p p) :=
        tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
          (I := I) βsec p hβ_p
      have hV_md : ∀ a : Fin s, MDiffAt (T% (V a)) p :=
        fun a => (hV_p a).mdifferentiableAt (by simp)
      have hVmodel_p : ∀ a : Fin s,
          DifferentiableWithinAt 𝕜
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
            (Set.range I) (extChartAt I p p) :=
        fun a =>
          tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
            (I := I) (V a) p (hV_p a)
      have hcoord_p : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
          MDifferentiableAt I 𝓘(𝕜, 𝕜)
            (fun q : M =>
              (Module.finBasis 𝕜 E).coord i
                (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
                  (extChartAt I p q))) p :=
        fun a i =>
          tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
            (I := I) (V a) p (hV_p a) i
      have hVeq :
          (fun a : Fin s => eTan.symmL 𝕜 p (vσ a)) =
            fun a : Fin s => V a p := by
        funext a
        simp [V, eTan]
      change ((nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T p) (βsec p))
          (fun a : Fin s => eTan.symmL 𝕜 p (vσ a)) =
        ((extDerivFun (I := I) pair p) (X p) -
            (T p (localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X βsec p))
              (fun a : Fin s => V a p)) -
          ∑ a : Fin s,
            (T p (βsec p))
              (Function.update (fun b : Fin s => V b p) a ((cov (V a) p) (X p)))
      rw [hVeq]
      rw [nablaRSFun_eval_moving_raw
        (I := I) cov X T βsec V p hpair_md hβmodel_p hV_md hVmodel_p hcoord_p]
    refine hintrinsic.congr_of_eventuallyEq ?_
    have hx₀Tan : x₀ ∈ eTan.baseSet := by
      dsimp [eTan]
      exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
    filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan] with p hp
    simpa [G, F, e, eTan, βρ, vσ] using
      (TensorRSSpace.trivializationAt_basis_coord
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := p)
        (bE := bE) (r := r) (s := s) hp (F p) ρ σ)
  simpa [G, F, e] using hG



end Tensor0SBundle
