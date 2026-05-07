import RicciFlower.Realized.RicciFlow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Realized Curvature Interfaces

Curvature fields are data. Realization of those fields from the connection is a
separate predicate. In this first realized-core pass, the connection-built
Riemann operator is expressible directly from mathlib's `CovariantDerivative`.
Ricci and scalar contractions remain separate fields of the data package, but
this file now provides frame-level metric trace predicates and coordinate
formulas tying those fields to a covariant four-curvature tensor.
-/

namespace RicciFlower
namespace Realized

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A possibly nonsmooth tangent field, matching the input type of mathlib's
bundled covariant derivative. -/
abbrev TangentField :=
  (x : M) -> TangentSpace I x

/-- A pointwise covariant four-curvature field.

The slot order is the coordinate convention used below:
`Riemann04 t x A B C D` has components `R_{A B C D}`.  With this convention
the Ricci contraction is `Ric_{ij} = g^{kl} R_{k i j l}`. -/
abbrev RealizedFourTensorField (Time : Type*) :=
  Time -> (x : M) -> TangentSpace I x -> TangentSpace I x ->
    TangentSpace I x -> TangentSpace I x -> Real

/-- Coordinate inverse metric coefficients in a local frame. -/
abbrev InverseMetricComponents
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (Time Idx : Type*) :=
  Time -> M -> Idx -> Idx -> Real

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

Ricci and scalar are intentionally not forced here; use the trace predicates
below to state the chosen contraction layer explicitly. -/
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

section MetricTrace

variable {Idx : Type*} [Fintype Idx]

/-- Predicate saying `gInv` is a two-sided inverse to the metric matrix in the
chosen frame.

This is intentionally a coordinate predicate rather than a field of the metric
family.  Later code can supply it from an actual local frame and the positive
definite metric matrix. -/
def InverseMetricComponentsInFrame [DecidableEq Idx]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall (t : Time) (x : M) (i j : Idx),
    (∑ k : Idx, gInv t x i k * (G.metric t).inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, (G.metric t).inner x (frame i x) (frame k x) * gInv t x k j) =
        (if i = j then 1 else 0)

/-- Ricci curvature obtained by metric-tracing a covariant four-curvature tensor
in a frame:

`Ric(X,Y) = ∑_{k,l} g^{kl} R(e_k, X, Y, e_l)`. -/
noncomputable def ricciFromRiemann04TraceInFrame
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    RealizedTwoTensorField (I := I) (M := M) Time :=
  fun t x X Y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv t x k l * Riemann04 t x (frame k x) X Y (frame l x)

@[simp] theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame t x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l * Riemann04 t x (frame k x) X Y (frame l x) := by
  rfl

/-- Coordinate form of the Ricci contraction:
`Ric_ij = g^{kl} R_{k i j l}`. -/
theorem ricciFromRiemann04TraceInFrame_component_eq_gInv_mul_riemann04
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame
        t x (frame i x) (frame j x) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Riemann04 t x (frame k x) (frame i x) (frame j x) (frame l x) := by
  rfl

/-- Interface saying the supplied Ricci field is the frame metric trace of the
supplied covariant four-curvature tensor. -/
def RicciFieldRealizesRiemann04TraceInFrame
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  RicciFieldRealizesRiemannTrace K
    (ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame)

/-- If Ricci realizes the frame trace of `Riemann04`, then its frame components
satisfy `Ric_ij = g^{kl} R_{k i j l}`. -/
theorem ricci_component_eq_gInv_mul_riemann04_of_realizesTraceInFrame
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (Riemann04 : RealizedFourTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hK : RicciFieldRealizesRiemann04TraceInFrame
      (I := I) K Riemann04 gInv frame)
    (t : Time) (x : M) (i j : Idx) :
    K.ricci t x (frame i x) (frame j x) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Riemann04 t x (frame k x) (frame i x) (frame j x) (frame l x) := by
  exact hK t x (frame i x) (frame j x)

/-- Scalar curvature obtained by tracing Ricci in a frame:
`R = ∑_{i,j} g^{ij} Ric(e_i,e_j)`. -/
noncomputable def scalarFromRicciTraceInFrame
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, gInv t x i j * Ric t x (frame i x) (frame j x)

@[simp] theorem scalarFromRicciTraceInFrame_apply
    (Ric : RealizedTwoTensorField (I := I) (M := M) Time)
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * Ric t x (frame i x) (frame j x) := by
  rfl

/-- Interface saying the scalar field is the frame metric trace of Ricci. -/
def ScalarFieldRealizesRicciTraceInFrame
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ScalarFieldRealizesRicciTrace K
    (scalarFromRicciTraceInFrame (I := I) K.ricci gInv frame)

/-- If scalar curvature realizes the frame trace of Ricci, then its frame
formula is `R = g^{ij} Ric_ij`. -/
theorem scalar_eq_gInv_mul_ricci_of_realizesTraceInFrame
    (K : CurvatureFields (I := I) (M := M) (Time := Time))
    (gInv : InverseMetricComponents (I := I) (M := M) Time Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hK : ScalarFieldRealizesRicciTraceInFrame (I := I) K gInv frame)
    (t : Time) (x : M) :
    K.scalar t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * K.ricci t x (frame i x) (frame j x) := by
  exact hK t x

end MetricTrace

section Interval

/-- Curvature fields over the flow-time subtype of a concrete interval. -/
abbrev CurvatureFieldsOn (D : RealTimeInterval) :=
  CurvatureFields (I := I) (M := M) (Time := RealTimeInterval.FlowTime D)

/-- Realization of interval curvature fields from the interval connection. -/
def CurvatureFieldsRealizeConnectionOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (K : CurvatureFieldsOn (I := I) (M := M) D) : Prop :=
  CurvatureFieldsRealizeConnection (G.toFlowTimeFamily) K

/-- Extract the Riemann realization equation on an interval. -/
theorem riemann_eq_connection_of_curvatureFieldsRealizeConnectionOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (K : CurvatureFieldsOn (I := I) (M := M) D)
    (hK : CurvatureFieldsRealizeConnectionOn (I := I) G K)
    (t : RealTimeInterval.FlowTime D)
    (X Y Z : TangentField (I := I) (M := M)) :
    K.riemann t X Y Z = connectionRiemannField (G.connectionAt t) X Y Z :=
  hK.riemann_eq t X Y Z

end Interval

end Realized
end RicciFlower
