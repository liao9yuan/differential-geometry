import RicciFlower.Realized.RicciFlow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Realized Curvature Interfaces

Curvature fields are data. Realization of those fields from the connection is a
separate predicate. In this first realized-core pass, the connection-built
Riemann operator is expressible directly from mathlib's `CovariantDerivative`.
Ricci and scalar contractions remain separate fields until the finite-frame
trace/contraction API is rebuilt in the realized layer.
-/

namespace RicciFlower
namespace Realized

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A possibly nonsmooth tangent field, matching the input type of mathlib's
bundled covariant derivative. -/
abbrev TangentField :=
  (x : M) -> TangentSpace I x

/-- Riemann curvature operator of a realized connection on tangent fields:
`R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z`. -/
noncomputable def connectionRiemannField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : TangentField (I := I) (M := M)) :
    TangentField (I := I) (M := M) :=
  fun x =>
    cov (fun y => cov Z y (Y y)) x (X x) -
      cov (fun y => cov Z y (X y)) x (Y x) -
      cov Z x (VectorField.mlieBracket I X Y x)

@[simp] theorem connectionRiemannField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : TangentField (I := I) (M := M)) (x : M) :
    connectionRiemannField cov X Y Z x =
      cov (fun y => cov Z y (Y y)) x (X x) -
        cov (fun y => cov Z y (X y)) x (Y x) -
        cov Z x (VectorField.mlieBracket I X Y x) := by
  rfl

variable {Time : Type*}

/-- Realized curvature fields attached to a time family.

The fields are data only. Equalities identifying them with connection-built
curvatures live in `CurvatureFieldsRealizeConnection`. -/
structure CurvatureFields where
  riemann :
    Time -> TangentField (I := I) (M := M) ->
      TangentField (I := I) (M := M) ->
      TangentField (I := I) (M := M) ->
      TangentField (I := I) (M := M)
  ricci : RealizedTwoTensorField (I := I) (M := M) Time
  scalar : Time -> M -> Real

/-- Predicate tying curvature data back to the connection-built Riemann operator.

Ricci and scalar are intentionally not forced here until V2 has a realized
trace/contraction layer for connection curvature. -/
structure CurvatureFieldsRealizeConnection
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (K : CurvatureFields (I := I) (M := M) (Time := Time)) : Prop where
  riemann_eq :
    forall (t : Time)
      (X Y Z : TangentField (I := I) (M := M)),
      K.riemann t X Y Z = connectionRiemannField (G.connection t) X Y Z

theorem riemann_eq_connection_of_curvatureFieldsRealizeConnection
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (hK : CurvatureFieldsRealizeConnection G K)
    (t : Time) (X Y Z : TangentField (I := I) (M := M)) :
    K.riemann t X Y Z = connectionRiemannField (G.connection t) X Y Z :=
  hK.riemann_eq t X Y Z

/-- Explicit interface saying the Ricci field is the chosen realized trace of
the Riemann field.

The trace construction is intentionally supplied as an argument until the
realized finite-frame contraction layer exists. -/
def RicciFieldRealizesRiemannTrace
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (ricciFromTrace : RealizedTwoTensorField (I := I) (M := M) Time) : Prop :=
  forall (t : Time) (x : M) (X Y : TangentSpace I x),
    K.ricci t x X Y = ricciFromTrace t x X Y

/-- Explicit interface saying the scalar field is the chosen realized trace of
the Ricci field. -/
def ScalarFieldRealizesRicciTrace
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (scalarFromTrace : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M), K.scalar t x = scalarFromTrace t x

theorem ricci_eq_trace_of_ricciFieldRealizesRiemannTrace
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (ricciFromTrace : RealizedTwoTensorField (I := I) (M := M) Time)
    (hK : RicciFieldRealizesRiemannTrace K ricciFromTrace)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    K.ricci t x X Y = ricciFromTrace t x X Y :=
  hK t x X Y

theorem scalar_eq_trace_of_scalarFieldRealizesRicciTrace
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (scalarFromTrace : Time -> M -> Real)
    (hK : ScalarFieldRealizesRicciTrace K scalarFromTrace)
    (t : Time) (x : M) :
    K.scalar t x = scalarFromTrace t x :=
  hK t x

end Realized
end RicciFlower
