import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointwise curvature components

This file records the metric-free, pointwise component layer used by curvature
calculations.  A tangent `Module.Basis` at one point is the primitive coordinate
object; local-frame statements are thin wrappers through `hframe.toBasisAt hx`.

No Christoffel or derivative curvature formula is stated here: those formulas
need either structure coefficients for a general frame or a holonomic-frame
hypothesis.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

/-- Two tensor slots encoded as a `Fin 2` index function. -/
def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun a => if a = 0 then i else j

/-- Four tensor slots encoded as a `Fin 4` index function. -/
def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun a => if a = 0 then i else if a = 1 then j else if a = 2 then k else l

/-- Pointwise Ricci component in a tangent basis. -/
def ricciCompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) : Real :=
  component0S (I := I) basis Ric (slots2 i j)

/-- Pointwise lowered Riemann component in a tangent basis. -/
def rm04CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) : Real :=
  component0S (I := I) basis Rm04 (slots4 i j k l)

@[simp]
theorem ricciCompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      Ric (vec2 (basis i) (basis j)) := by
  unfold ricciCompAt component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp

@[simp]
theorem rm04CompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) :
    rm04CompAt (I := I) basis Rm04 i j k l =
      Rm04 (vec4 (basis i) (basis j) (basis k) (basis l)) := by
  unfold rm04CompAt component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp

private theorem basisTensor0S_empty_eq_scalarOne
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (slots : Fin 0 -> Idx) :
    basisTensor0S (I := I) basis slots = scalarOne0S (I := I) x := by
  ext v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]
  have hcomp := basisTensor0S_component (I := I) basis slots slots
  have harg : (fun a : Fin 0 => basis (slots a)) = Fin.elim0 := Subsingleton.elim _ _
  change (basisTensor0S (I := I) basis slots) (fun a : Fin 0 => basis (slots a)) = 1
    at hcomp
  rw [harg] at hcomp
  simpa [scalarOne0S] using hcomp

/-- Components of the symbolically defined Ricci tensor are the components of
the tensor trace contraction of the `(1,3)` curvature tensor. -/
theorem ricciCompAt_eq_contractTrace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        Fin.elim0 (slots2 i j) := by
  unfold ricciCompAt componentRS ricciFromRm13At component0S
  rw [basisTensor0S_empty_eq_scalarOne (I := I) basis Fin.elim0]

theorem ricciCompAt_eq_contractTrace_of_realizes
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x (Rm13 x))
        Fin.elim0 (slots2 i j) := by
  rw [hRic x]
  exact ricciCompAt_eq_contractTrace (I := I) basis (Rm13 x) i j

/-- Pointwise trace realization of Ricci from a lowered Riemann tensor in a
tangent basis. -/
def RicciRealizesRm04TraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall X Y : TangentSpace I x,
    Ric (vec2 X Y) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) X Y (basis l))

/-- Pointwise trace realization of scalar curvature from a Ricci tensor in a
tangent basis. -/
def ScalarRealizesRicciTraceAt
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  scalar =
    ∑ i : Idx, ∑ j : Idx, gInv i j * Ric (vec2 (basis i) (basis j))

theorem ricciComp_eq_trace_rm04
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hRic : RicciRealizesRm04TraceAt (I := I) Ric Rm04 gInv basis)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * rm04CompAt (I := I) basis Rm04 k i j l := by
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hRic (basis i) (basis j)

theorem scalar_eq_trace_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric gInv basis) :
    scalar =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ricciCompAt (I := I) basis Ric i j := by
  rw [hScalar]
  simp_rw [ricciCompAt_apply]

section LocalFrame

variable {u : Set M}

theorem ricciCompAt_eq_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ricciComp (I := I) Ric frame x i j := by
  unfold ricciCompAt ricciComp component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem rm04CompAt_eq_frame
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j k l : Idx) :
    rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j k l =
      rm04Comp (I := I) Rm04 frame x i j k l := by
  unfold rm04CompAt rm04Comp component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem ricciTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04TraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro X Y
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    IsLocalFrameOn.toBasisAt_coe] using hRic x X Y

theorem scalarTraceAt_of_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    ScalarRealizesRicciTraceAt (I := I) (scalar x) (Ric x) (gInv x)
      (hframe.toBasisAt hx) := by
  simpa [ScalarRealizesRicciTraceAt, ScalarSectionRealizesRicciTraceInFrame,
    tensor02ToField, IsLocalFrameOn.toBasisAt_coe] using hScalar x

theorem ricciComp_eq_trace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  exact ricciComp_eq_trace_rm04 (I := I) (hframe.toBasisAt hx) (Ric x) (Rm04 x)
    (gInv x) (ricciTraceAt_of_frame (I := I) Ric Rm04 gInv frame hframe hRic hx) i j

theorem scalar_eq_trace_ricci_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j := by
  exact scalar_eq_trace_ricci (I := I) (hframe.toBasisAt hx) (scalar x) (Ric x)
    (gInv x) (scalarTraceAt_of_frame (I := I) scalar Ric gInv frame hframe hScalar hx)

end LocalFrame

end Realized
end RicciFlower
