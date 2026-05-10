import RicciFlower.Realized.CurvatureTensor
import RicciFlower.VectorBundle.TangentConst
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Pointwise Riemann and Ricci tensors

This file starts a definition-first curvature layer.  The auxiliary curvature
operator is the usual vector-field formula, and the pointwise tensors are the
objects intended for downstream use.  The tensoriality proofs are recorded here
as the mathematical frontier, rather than hidden behind realization predicates.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Bundle Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace RicciFlower.Realized

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

private noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

/-- The curvature operator of a covariant derivative, before tensorial descent.

The sign convention is
`∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/
def riemannCurvatureAux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) : TangentSpace I x :=
  (cov (fun p => (cov Z p) (Y p)) x) (X x) -
    (cov (fun p => (cov Z p) (X p)) x) (Y x) -
      (cov Z x) (VectorField.mlieBracket I X Y x)

@[simp]
theorem riemannCurvatureAux_eq_connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) :
    riemannCurvatureAux cov X Y Z x =
      connectionRiemannCurvatureField cov X Y Z x := rfl

/-- Curvature is tensorial in its first vector-field input. -/
theorem riemannCurvatureAux_tensorial₁
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (Y Z : (p : M) → TangentSpace I p)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X => riemannCurvatureAux cov X Y Z x) x := by
  sorry

/-- Curvature is tensorial in its second vector-field input. -/
theorem riemannCurvatureAux_tensorial₂
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (X Z : (p : M) → TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun Y => riemannCurvatureAux cov X Y Z x) x := by
  sorry

/-- Curvature is tensorial in its third vector-field input. -/
theorem riemannCurvatureAux_tensorial₃
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x : M) (X Y : (p : M) → TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z => riemannCurvatureAux cov X Y Z x) x := by
  sorry

private noncomputable def riemannCurvatureModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ where
  toFun v :=
    cotangentToDual α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
        (tangentConstAt (I := I) x (v 2)) x)
  map_update_add' := by
    sorry
  map_update_smul' := by
    sorry
  cont := by
    sorry

/-- The pointwise `(1,3)` Riemann curvature tensor of a covariant derivative. -/
noncomputable def riemannCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    Tensor13At (I := I) (M := M) x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        riemannCurvatureModel cov x (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α)
      map_add' := by
        sorry
      map_smul' := by
        sorry })

@[simp]
theorem riemannCurvatureAt_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureAt cov x α (vec3 X Y Z) =
      cotangentToDual α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  sorry

/-- Evaluation of the `(1,3)` tensor on smooth local vector-field representatives. -/
theorem riemannCurvatureAt_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : (p : M) → TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    riemannCurvatureAt cov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual α (riemannCurvatureAux cov X Y Z x) := by
  sorry

private noncomputable def riemannCurvature04Model
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ where
  toFun v :=
    g.inner x (v 0)
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x (v 1)) (tangentConstAt (I := I) x (v 2))
        (tangentConstAt (I := I) x (v 3)) x)
  map_update_add' := by
    sorry
  map_update_smul' := by
    sorry
  cont := by
    sorry

/-- The lowered pointwise `(0,4)` Riemann curvature tensor. -/
noncomputable def riemannCurvature04At
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    Tensor04At (I := I) (M := M) x :=
  Tensor0SSpace.ofModel (riemannCurvature04Model g cov x)

@[simp]
theorem riemannCurvature04At_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov x (vec4 W X Y Z) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  sorry

/-- Evaluation of the lowered tensor on smooth local vector-field representatives. -/
theorem riemannCurvature04At_apply
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] {x : M}
    (W X Y Z : (p : M) → TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    riemannCurvature04At g cov x (vec4 (W x) (X x) (Y x) (Z x)) =
      g.inner x (W x) (riemannCurvatureAux cov X Y Z x) := by
  sorry

/-- The pointwise Ricci tensor, obtained by tracing the `(1,3)` tensor. -/
noncomputable def ricciCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    Tensor02At (I := I) (M := M) x :=
  ricciFromRm13At (riemannCurvatureAt cov x)

@[simp]
theorem ricciCurvatureAt_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x : M) :
    ricciCurvatureAt cov x = ricciFromRm13At (riemannCurvatureAt cov x) := rfl

/-- The lowered `(0,4)` tensor is evaluation of the metric on the `(1,3)` tensor. -/
theorem riemannCurvature04At_eq_lower_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] {x : M}
    (W X Y Z : TangentSpace I x) :
    riemannCurvature04At g cov x (vec4 W X Y Z) =
      riemannCurvatureAt cov x (dualToCotangent ((tangentFlatLinear g x) W))
        (vec3 X Y Z) := by
  sorry

end CovariantDerivative

end RicciFlower.Realized
