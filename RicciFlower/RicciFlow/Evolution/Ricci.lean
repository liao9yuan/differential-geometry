import RicciFlower.RicciFlow.Evolution.Connection
import RicciFlower.VectorBundle.PartialMfderiv
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Ricci Evolution by Tracing Riemann Evolution

This file contains the realized interval trace step for Lemma 6.3.  The
Riemann evolution calculation itself is represented by the component predicate
`RiemannEvolutionEquationInFrameOn`; once that is supplied, this file proves
that tracing through the inverse metric gives the existing
`RicciEvolutionEquationInFrame` predicate from `RicciFlow.Basic`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- A time-indexed Ricci tensor realizes the lowered Riemann trace in a fixed
frame at every time. -/
def RicciTensorRealizesRm04TraceInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    Realized.RicciTensorRealizesRm04TraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame

theorem ricciCompInFrame_eq_rm04_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (htrace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          Realized.rm04Comp (I := I) (Rm04 t) frame x k i j l := by
  simpa [ricciCompInFrame] using
    Realized.ricciComp_eq_trace (I := I)
      (S.ricci t) (Rm04 t) (gInv t) frame (htrace t) x i j

/-- Component form of a lowered Riemann evolution equation.  The future
producer is the realized analogue of synthetic `RiemannVariation.lean` plus
`RiemannEvolution.lean`. -/
def RiemannEvolutionEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (a i j l : Idx),
    HasDerivWithinAt
      (fun s : Real => Realized.rm04Comp (I := I) (Rm04 s) frame x a i j l)
      (rm04Dt (t : Real) x a i j l)
      D.carrier
      (t : Real)

/-! ## Ricci variation route for Lemma 6.3 -/

/-- Trace of the covariant derivative of the infinitesimal connection
variation:
`∇_k A^k_ij - ∇_i A^k_kj`.

Here `nablaGammaDt t x d k i j` denotes the fixed-frame component
`(∇_d A)^k_ij`, where `A^k_ij = ∂_t Γ^k_ij`. -/
def ricciVariationFromConnectionRHSInFrame
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, nablaGammaDt t x k k i j) -
    (∑ k : Idx, nablaGammaDt t x i k k j)

/-- Ricci variation formula in a fixed frame:
`∂_t Ric_ij = ∇_k A^k_ij - ∇_i A^k_kj`.

This is the realized component target obtained by differentiating the
curvature trace of the connection using the current `(1,3)` convention
`Ric(e_i,e_j) = trace (e_k ↦ R(e_k,e_i)e_j)`. -/
def RicciVariationFormulaInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- `(1,3)` Riemann variation induced by the covariant derivative of the
connection variation:
`δR^a_bcd = (∇_b A)^a_cd - (∇_c A)^a_bd`. -/
def riemann13VariationFromConnectionRHSInFrame
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  nablaA t x b a c d - nablaA t x c a b d

/-- `(1,3)` Riemann variation formula in a fixed global frame. -/
def Riemann13VariationFormulaInFrameOn
    {D : Realized.RealTimeInterval}
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame Set.univ)
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (a b c d : Idx),
    HasDerivWithinAt
      (fun s : Real => Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a b c d)
      (riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
        (t : Real) x a b c d)
      D.carrier
      (t : Real)

/-- Local version of the Ricci variation formula in a fixed frame domain. -/
def RicciVariationFormulaInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
          (t : Real) x i j)
        D.carrier
        (t : Real)

/-- Local version of Lemma 6.3's Ricci evolution equation in a fixed frame
domain. -/
def RicciEvolutionEquationInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)

/-- Local version of the `(1,3)` Riemann variation formula in a frame domain. -/
def Riemann13VariationFormulaInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall (a b c d : Idx),
      HasDerivWithinAt
        (fun s : Real => Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a b c d)
        (riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
          (t : Real) x a b c d)
        D.carrier
        (t : Real)

theorem ricciVariationFormulaInFrameOn_of_local_univ
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hlocal : RicciVariationFormulaInFrameOnLocal
      (I := I) S frame Set.univ nablaGammaDt) :
    RicciVariationFormulaInFrameOn (I := I) S frame nablaGammaDt := by
  intro t x i j
  exact hlocal t x (Set.mem_univ x) i j

theorem riemann13VariationFormulaInFrameOn_of_local_univ
    {D : Realized.RealTimeInterval}
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame Set.univ)
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hlocal : Riemann13VariationFormulaInFrameOnLocal
      (I := I) (D := D) Rm13 frame hframe nablaA) :
    Riemann13VariationFormulaInFrameOn
      (I := I) (D := D) Rm13 frame hframe nablaA := by
  intro t x a b c d
  exact hlocal t x (Set.mem_univ x) a b c d

theorem ricciCompInFrame_eq_rm13_trace_local
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (t : Real) {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ a : Idx, Realized.rm13Comp (I := I) (Rm13 t) frame hframe x a a i j := by
  unfold ricciCompInFrame
  rw [htrace t x]
  rw [Realized.ricciFromRm13At_apply_basis_trace
    (I := I) (basis := hframe.toBasisAt hx) (Rm13 := Rm13 t x)
    (Y := frame i x) (Z := frame j x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Realized.rm13Comp, RicciFlower.Curvature.rm13Comp,
    IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

theorem ricciCompInFrame_eq_rm13_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame Set.univ)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ a : Idx, Realized.rm13Comp (I := I) (Rm13 t) frame hframe x a a i j := by
  classical
  have hx : x ∈ (Set.univ : Set M) := Set.mem_univ x
  unfold ricciCompInFrame
  rw [htrace t x]
  rw [Realized.ricciFromRm13At_apply_basis_trace
    (I := I) (basis := hframe.toBasisAt hx) (Rm13 := Rm13 t x)
    (Y := frame i x) (Z := frame j x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Realized.rm13Comp, RicciFlower.Curvature.rm13Comp,
    IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- Trace a supplied `(1,3)` Riemann variation formula to the Ricci variation
formula, using the current `Rm13` convention
`Ric(e_i,e_j) = trace (e_k ↦ R(e_k,e_i)e_j)`. -/
theorem ricciVariationFormulaInFrameOn_of_riemann13Variation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame Set.univ)
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (hRm : Riemann13VariationFormulaInFrameOn
      (I := I) (D := D) Rm13 frame hframe nablaA) :
    RicciVariationFormulaInFrameOn (I := I) S frame nablaA := by
  classical
  intro t x i j
  let traceComp : Real -> Real :=
    fun s => ∑ a : Idx, Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a a i j
  have htraceDeriv :
      HasDerivWithinAt traceComp
        (∑ a : Idx,
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        D.carrier
        (t : Real) := by
    simpa [traceComp, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a a i j)
        (A' := fun a =>
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        (s := D.carrier) (x := (t : Real))
        (fun a _ha => hRm t x a a i j))
  have hricci :
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (∑ a : Idx,
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        D.carrier
        (t : Real) := by
    refine htraceDeriv.congr ?_ ?_
    · intro s _hs
      exact ricciCompInFrame_eq_rm13_trace
        (I := I) S Rm13 frame hframe htrace s x i j
    · exact ricciCompInFrame_eq_rm13_trace
        (I := I) S Rm13 frame hframe htrace (t : Real) x i j
  exact hricci.congr_deriv (by
    simp [ricciVariationFromConnectionRHSInFrame,
      riemann13VariationFromConnectionRHSInFrame, Finset.sum_sub_distrib])

/-- Trace a local supplied `(1,3)` Riemann variation formula to the local
Ricci variation formula. -/
theorem ricciVariationFormulaInFrameOnLocal_of_riemann13Variation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (nablaA : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (hRm : Riemann13VariationFormulaInFrameOnLocal
      (I := I) (D := D) Rm13 frame hframe nablaA) :
    RicciVariationFormulaInFrameOnLocal (I := I) S frame u nablaA := by
  classical
  intro t x hx i j
  let traceComp : Real -> Real :=
    fun s => ∑ a : Idx, Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a a i j
  have htraceDeriv :
      HasDerivWithinAt traceComp
        (∑ a : Idx,
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        D.carrier
        (t : Real) := by
    simpa [traceComp, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          Realized.rm13Comp (I := I) (Rm13 s) frame hframe x a a i j)
        (A' := fun a =>
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        (s := D.carrier) (x := (t : Real))
        (fun a _ha => hRm t x hx a a i j))
  have hricci :
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (∑ a : Idx,
          riemann13VariationFromConnectionRHSInFrame (M := M) nablaA
            (t : Real) x a a i j)
        D.carrier
        (t : Real) := by
    refine htraceDeriv.congr ?_ ?_
    · intro s _hs
      exact ricciCompInFrame_eq_rm13_trace_local
        (I := I) S Rm13 frame hframe htrace s hx i j
    · exact ricciCompInFrame_eq_rm13_trace_local
        (I := I) S Rm13 frame hframe htrace (t : Real) hx i j
  exact hricci.congr_deriv (by
    simp [ricciVariationFromConnectionRHSInFrame,
      riemann13VariationFromConnectionRHSInFrame, Finset.sum_sub_distrib])

/-- The covariant derivative of the Ricci-flow connection variation after
substituting
`A^k_ij = -g^{kl} nabla_i Ric_jl - g^{kl} nabla_j Ric_il
  + g^{kl} nabla_l Ric_ij`.

Here `nabla2Ric t x d a i j` denotes `(nabla_d nabla_a Ric)_ij`.  Metric
compatibility is already reflected in this component expression: no derivative
falls on `gInv`. -/
def nablaGammaDtFromNabla2RicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d k i j : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x d i j l -
        nabla2Ric t x d j i l +
        nabla2Ric t x d l i j)

section CoordinateRiemannVariation

open RicciFlower.Coordinates

/-- Spatial derivative of a supplied Christoffel-variation component in the
chart-induced coordinate frame. -/
def christoffelVariationCoordDerivAt
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (dir i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (fun x : M => gammaDt t x i j k) x₀
    (coordinateFrameAt (I := I) x₀ dir x₀)

/-- Fixed-base mixed derivative regularity for Christoffel coordinate
coefficients in the chart-induced coordinate frame.

This is the honest extra regularity needed after the pointwise Christoffel
evolution equation: differentiating the spatial exterior derivative in time
requires a mixed-partial hypothesis, not just the coefficient ODE. -/
def ChristoffelCoordMixedDerivativeInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M) (timeSet : Set Real) (u : Set M) : Prop :=
  ∀ i j k : CoordinateIdx (𝕜 := Real) E,
    FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u
      (fun s x =>
        Realized.christoffelCoordFun (I := I) (S.family.connection s) x₀ i j k x)
      (fun t x =>
        christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k)

/-- Coordinate covariant derivative of a Christoffel-variation tensor
`A^k_ij` in the chart-induced coordinate frame. -/
def christoffelVariationCovDerivCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (dir k i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelVariationCoordDerivAt (I := I) gammaDt t x₀ dir i j k +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir a k *
        gammaDt t x₀ i j a) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir i a *
        gammaDt t x₀ a j k) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      Realized.christoffelCoordAt (I := I) cov x₀ dir j a *
        gammaDt t x₀ i a k)

/-- Raw time variation of the Christoffel-coordinate curvature coefficient,
before regrouping it as `∇A - ∇A`. -/
def christoffelCurvCoeffVariationRawAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (i k j m : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelVariationCoordDerivAt (I := I) gammaDt t x₀ i k j m -
    christoffelVariationCoordDerivAt (I := I) gammaDt t x₀ k i j m +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      (gammaDt t x₀ k j a *
          Realized.christoffelCoordAt (I := I) cov x₀ i a m +
        Realized.christoffelCoordAt (I := I) cov x₀ k j a *
          gammaDt t x₀ i a m)) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      (gammaDt t x₀ i j a *
          Realized.christoffelCoordAt (I := I) cov x₀ k a m +
        Realized.christoffelCoordAt (I := I) cov x₀ i j a *
          gammaDt t x₀ k a m))

/-- Coordinate frame restricted to the singleton base point.  This is the
honest domain for the pointwise Christoffel curvature expansion currently
available in the coordinate layer. -/
def coordinateFrameAt_isLocalFrame_singleton (x₀ : M) :
    IsLocalFrameOn I E ∞ (coordinateFrameAt (I := I) x₀)
      ({x₀} : Set M) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).mono (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact coordinateFrameAt_mem (I := I) x₀)

private theorem rm13Comp_coordinateFrame_singleton_eq_christoffelCurvCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Realized.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hRm : Realized.Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : Realized.ConnectionCurvatureCoordAt (I := I) cov x₀)
    (a b c d : CoordinateIdx (𝕜 := Real) E) :
    Realized.rm13Comp (I := I) Rm13 (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀) x₀ a b c d =
      Realized.christoffelCurvCoeffAt (I := I) cov x₀ b c d a := by
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hEval := Realized.rm13_eval_eq_christoffelCurvCoord
    (I := I) cov Rm13 x₀
    (dualToCotangent (I := I)
      ((coordinateFrameAt_isLocalFrame_singleton (I := I) x₀).coeff a x₀))
    hRm hcurv b c d
  dsimp [Realized.rm13Comp, RicciFlower.Curvature.rm13Comp]
  rw [hEval]
  let hsingle := coordinateFrameAt_isLocalFrame_singleton (I := I) x₀
  have hx : x₀ ∈ ({x₀} : Set M) := by simp
  have hrepr (m : CoordinateIdx (𝕜 := Real) E) :
      (hsingle.toBasisAt hx).repr (coordinateFrameAt (I := I) x₀ m x₀) a =
        if m = a then 1 else 0 := by
    rw [← IsLocalFrameOn.toBasisAt_coe hsingle hx m]
    by_cases hma : m = a
    · subst m
      have hself := congrArg (fun f => f a) ((hsingle.toBasisAt hx).repr_self a)
      simpa using hself
    · have hself := congrArg (fun f => f a) ((hsingle.toBasisAt hx).repr_self m)
      simpa [Finsupp.single_apply, hma] using hself
  have hcoeff (m : CoordinateIdx (𝕜 := Real) E) :
      (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀).coeff a x₀
          (coordinateFrameAt (I := I) x₀ m x₀) =
        if m = a then 1 else 0 := by
    dsimp [coordinateFrameAt_isLocalFrame_singleton, hsingle, IsLocalFrameOn.coeff]
    rw [dif_pos hx]
    exact hrepr m
  simp only [dualToCotangent_apply]
  calc
    (∑ x : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCurvCoeffAt (I := I) cov x₀ b c d x *
          (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀).coeff a x₀
            (coordinateFrameAt (I := I) x₀ x x₀))
        =
      ∑ x : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCurvCoeffAt (I := I) cov x₀ b c d x *
          (if x = a then 1 else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hcoeff x]
    _ = Realized.christoffelCurvCoeffAt (I := I) cov x₀ b c d a := by
          simp

private theorem christoffelCoordAt_symm_of_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (htf : LeviCivita.IsTorsionFree (I := I) cov)
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    Realized.christoffelCoordAt (I := I) cov x₀ i j k =
      Realized.christoffelCoordAt (I := I) cov x₀ j i k := by
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hi : MDiffAt (T% (frame i)) x₀ :=
    coordinateFrameAt_mdifferentiableAt (I := I) x₀ i
  have hj : MDiffAt (T% (frame j)) x₀ :=
    coordinateFrameAt_mdifferentiableAt (I := I) x₀ j
  have hcoeff := torsion_coeff_eq_christoffel_skew
    (I := I) (x := x₀) cov frame hframe i j k hi hj
  have htors :
      hframe.coeff k x₀ (cov.torsion x₀ (frame i x₀) (frame j x₀)) = 0 := by
    rw [htf x₀]
    simp
  have hbracket :
      hframe.coeff k x₀ (VectorField.mlieBracket I (frame i) (frame j) x₀) = 0 := by
    rw [coordinateFrameAt_bracket_zero (I := I) x₀ i j]
    simp
  have h :
      (0 : Real) =
        Realized.christoffelCoordAt (I := I) cov x₀ i j k -
          Realized.christoffelCoordAt (I := I) cov x₀ j i k := by
    simpa [Realized.christoffelCoordAt, frame, hframe, htors, hbracket] using hcoeff
  exact sub_eq_zero.mp h.symm

/-- Mixed time/spatial derivative frontier for Christoffel symbols.

This is the precise analytic-regularity point needed to turn the already
proved Christoffel time evolution into the time variation of the coordinate
curvature formula. -/
theorem christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (_hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hmixed : ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M))
    (t : Realized.RealTimeInterval.RegularTime D)
    (dir i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCoordDerivAt (I := I) (S.family.connection s)
          x₀ dir i j k)
      (christoffelVariationCoordDerivAt (I := I)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ dir i j k)
      D.carrier
      (t : Real) := by
  have hx : x₀ ∈ ({x₀} : Set M) := by
    simp
  have h :=
    fixedBaseExtDerivTimeDerivativeOn_apply (I := I)
      (h := hmixed i j k) (t := (t : Real)) (x := x₀) hx
      (coordinateFrameAt (I := I) x₀ dir x₀)
  simpa [Realized.christoffelCoordDerivAt, christoffelVariationCoordDerivAt] using h

private theorem christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hmixed : ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M))
    (t : Realized.RealTimeInterval.RegularTime D)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        Realized.christoffelCurvCoeffAt (I := I) (S.family.connection s) x₀ i k j m)
      (christoffelCurvCoeffVariationRawAt (I := I) (S.family.connection (t : Real))
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ i k j m)
      D.carrier
      (t : Real) := by
  classical
  let gammaDt :=
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
  have hderiv_i :
      HasDerivWithinAt
        (fun s : Real =>
          Realized.christoffelCoordDerivAt (I := I) (S.family.connection s)
            x₀ i k j m)
        (christoffelVariationCoordDerivAt (I := I) gammaDt
          (t : Real) x₀ i k j m)
        D.carrier
        (t : Real) := by
    simpa [gammaDt] using
      christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelEvolution
        (I := I) S gInv nablaRic x₀ hEvol hmixed t i k j m
  have hderiv_k :
      HasDerivWithinAt
        (fun s : Real =>
          Realized.christoffelCoordDerivAt (I := I) (S.family.connection s)
            x₀ k i j m)
        (christoffelVariationCoordDerivAt (I := I) gammaDt
          (t : Real) x₀ k i j m)
        D.carrier
        (t : Real) := by
    simpa [gammaDt] using
      christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelEvolution
        (I := I) S gInv nablaRic x₀ hEvol hmixed t k i j m
  have hprod_pos :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ k j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ i a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDt (t : Real) x₀ k j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ i a m +
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ k j a *
              gammaDt (t : Real) x₀ i a m))
        D.carrier
        (t : Real) := by
    simpa [gammaDt, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (A := fun a s =>
          Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ k j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ i a m)
        (A' := fun a =>
          (gammaDt (t : Real) x₀ k j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ i a m +
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ k j a *
              gammaDt (t : Real) x₀ i a m))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha => by
          have h₁ :
              HasDerivWithinAt
                (fun s : Real =>
                  Realized.christoffelCoordAt (I := I) (S.family.connection s)
                    x₀ k j a)
                (gammaDt (t : Real) x₀ k j a)
                D.carrier
                (t : Real) := by
            simpa [Realized.christoffelCoordAt, gammaDt] using
              hEvol t x₀ (coordinateFrameAt_mem (I := I) x₀) k j a
          have h₂ :
              HasDerivWithinAt
                (fun s : Real =>
                  Realized.christoffelCoordAt (I := I) (S.family.connection s)
                    x₀ i a m)
                (gammaDt (t : Real) x₀ i a m)
                D.carrier
                (t : Real) := by
            simpa [Realized.christoffelCoordAt, gammaDt] using
              hEvol t x₀ (coordinateFrameAt_mem (I := I) x₀) i a m
          simpa [Pi.mul_apply, mul_add, add_comm, add_left_comm, add_assoc] using h₁.mul h₂))
  have hprod_neg :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ i j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ k a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDt (t : Real) x₀ i j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ k a m +
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ i j a *
              gammaDt (t : Real) x₀ k a m))
        D.carrier
        (t : Real) := by
    simpa [gammaDt, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (A := fun a s =>
          Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ i j a *
            Realized.christoffelCoordAt (I := I) (S.family.connection s) x₀ k a m)
        (A' := fun a =>
          (gammaDt (t : Real) x₀ i j a *
              Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ k a m +
            Realized.christoffelCoordAt (I := I) (S.family.connection (t : Real))
                x₀ i j a *
              gammaDt (t : Real) x₀ k a m))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha => by
          have h₁ :
              HasDerivWithinAt
                (fun s : Real =>
                  Realized.christoffelCoordAt (I := I) (S.family.connection s)
                    x₀ i j a)
                (gammaDt (t : Real) x₀ i j a)
                D.carrier
                (t : Real) := by
            simpa [Realized.christoffelCoordAt, gammaDt] using
              hEvol t x₀ (coordinateFrameAt_mem (I := I) x₀) i j a
          have h₂ :
              HasDerivWithinAt
                (fun s : Real =>
                  Realized.christoffelCoordAt (I := I) (S.family.connection s)
                    x₀ k a m)
                (gammaDt (t : Real) x₀ k a m)
                D.carrier
                (t : Real) := by
            simpa [Realized.christoffelCoordAt, gammaDt] using
              hEvol t x₀ (coordinateFrameAt_mem (I := I) x₀) k a m
          simpa [Pi.mul_apply, mul_add, add_comm, add_left_comm, add_assoc] using h₁.mul h₂))
  have hraw := (hderiv_i.sub hderiv_k).add hprod_pos
  exact (hraw.sub hprod_neg).congr_deriv (by
    simp [christoffelCurvCoeffVariationRawAt, gammaDt])

private theorem christoffelCurvCoeffVariationRawAt_eq_riemann13VariationFromConnectionRHSInFrame
    (covFam : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (htf : LeviCivita.IsTorsionFree (I := I) (covFam t))
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    christoffelCurvCoeffVariationRawAt (I := I) (covFam t) gammaDt t x₀ i k j m =
      riemann13VariationFromConnectionRHSInFrame (M := M)
        (fun τ x d out l₁ l₂ =>
          christoffelVariationCovDerivCoordAt (I := I)
            (covFam τ) gammaDt τ x d out l₁ l₂)
        t x₀ m i k j := by
  have hsymm (a : CoordinateIdx (𝕜 := Real) E) :
      Realized.christoffelCoordAt (I := I) (covFam t) x₀ k i a =
        Realized.christoffelCoordAt (I := I) (covFam t) x₀ i k a :=
    christoffelCoordAt_symm_of_torsionFree (I := I) (covFam t) htf x₀ k i a
  have hmul₁ :
      (∑ x : CoordinateIdx (𝕜 := Real) E,
        gammaDt t x₀ k j x * Realized.christoffelCoordAt (I := I) (covFam t) x₀ i x m) =
      (∑ x : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) (covFam t) x₀ i x m * gammaDt t x₀ k j x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hmul₂ :
      (∑ x : CoordinateIdx (𝕜 := Real) E,
        gammaDt t x₀ i j x * Realized.christoffelCoordAt (I := I) (covFam t) x₀ k x m) =
      (∑ x : CoordinateIdx (𝕜 := Real) E,
        Realized.christoffelCoordAt (I := I) (covFam t) x₀ k x m * gammaDt t x₀ i j x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp [riemann13VariationFromConnectionRHSInFrame,
    christoffelVariationCovDerivCoordAt, christoffelCurvCoeffVariationRawAt,
    hsymm, hmul₁, hmul₂, sub_eq_add_neg, Finset.sum_add_distrib]
  ring_nf

/-- Pointwise coordinate-frame producer for the local `(1,3)` Riemann variation
formula from Christoffel evolution.

The local domain is the singleton `{x₀}` because the current Christoffel
curvature expansion is proved for the coordinate frame at its base point. -/
theorem riemann13VariationFormulaInFrameOnLocal_of_christoffelEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hRm : ∀ t : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection t) (Rm13 t))
    (hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞))
    (htf : ∀ t : Realized.RealTimeInterval.RegularTime D,
      LeviCivita.IsTorsionFree (I := I) (S.family.connection (t : Real)))
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hmixed : ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M)) :
    Riemann13VariationFormulaInFrameOnLocal
      (I := I) (D := D) Rm13 (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀)
      (fun τ x d out l₁ l₂ =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ)
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          τ x d out l₁ l₂) := by
  unfold Riemann13VariationFormulaInFrameOnLocal
  intro t x hx a b c d
  rw [Set.mem_singleton_iff] at hx
  subst x
  have hcurvDeriv :=
    christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelEvolution
      (I := I) S gInv nablaRic x₀ hEvol hmixed t b c d a
  have hcurvEq (s : Real) :
      Realized.rm13Comp (I := I) (Rm13 s) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀) x₀ a b c d =
        Realized.christoffelCurvCoeffAt (I := I) (S.family.connection s) x₀ b c d a := by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact rm13Comp_coordinateFrame_singleton_eq_christoffelCurvCoeffAt
      (I := I) (S.family.connection s) (Rm13 s) x₀ (hRm s)
      (Realized.connection_curvature_coord_of_christoffel
        (I := I) (S.family.connection s) (hcov s) x₀)
      a b c d
  exact
    ((hcurvDeriv.congr
      (fun s _hs => hcurvEq s)
      (hcurvEq (t : Real))).congr_deriv
        (christoffelCurvCoeffVariationRawAt_eq_riemann13VariationFromConnectionRHSInFrame
          (I := I) S.family.connection
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ (htf t) b c d a))

/-- Pointwise coordinate-frame Ricci variation producer obtained by composing
the local Riemann13 variation from Christoffel evolution with the local trace
formula for the current `Rm13` convention. -/
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (hRm : ∀ t : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection t) (Rm13 t))
    (hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞))
    (htf : ∀ t : Realized.RealTimeInterval.RegularTime D,
      LeviCivita.IsTorsionFree (I := I) (S.family.connection (t : Real)))
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hmixed : ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M)) :
    RicciVariationFormulaInFrameOnLocal
      (I := I) S (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (fun τ x d out l₁ l₂ =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ)
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          τ x d out l₁ l₂) :=
  ricciVariationFormulaInFrameOnLocal_of_riemann13Variation
    (I := I) S Rm13 (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_singleton (I := I) x₀)
    (fun τ x d out l₁ l₂ =>
      christoffelVariationCovDerivCoordAt (I := I)
        (S.family.connection τ)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        τ x d out l₁ l₂)
    htrace
    (riemann13VariationFormulaInFrameOnLocal_of_christoffelEvolution
      (I := I) S Rm13 gInv nablaRic x₀ hRm hcov htf hEvol hmixed)

/-- Covariantly differentiating the Ricci-flow Christoffel variation and using
`nabla g^{-1} = 0` turns the actual Christoffel-variation tensor into the
book expression with second Ricci derivatives.

This is the precise component product-rule calculation for
`nabla_d (g^{kl} B_ijl) = g^{kl} nabla_d B_ijl`. -/
theorem christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (_hinv : InverseMetricComponentsInFrameOn (I := I) S gInv
      (coordinateFrameAt (I := I) x₀))
    (_hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀) nablaRic)
    (_hnabla2 :
      Nabla2RicciComponentsByConnectionInFrameOn
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D)
    (_hmc : RicciFlower.Connection.IsMetricCompatible (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)))
    (d k i j : CoordinateIdx (𝕜 := Real) E) :
    christoffelVariationCovDerivCoordAt (I := I)
        (S.family.connection (t : Real))
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ d k i j =
      nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x₀ d k i j := by
  classical
  /-
  `Metric.lean` now proves the coordinate identity `nabla_d gInv^{kl} = 0`.
  The remaining work here is to thread the regularity needed by the product
  rule: fixed-time differentiability of the supplied `gInv` components and
  differentiability of the supplied first Ricci-derivative components
  `nablaRic t · a i j`.
  -/
  sorry

/-- Local coordinate-frame Ricci variation producer after substituting
`nabla A` by the second Ricci derivative expression. -/
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> Realized.Tensor13Section (I := I) (M := M))
    (gInv :
      Real -> Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (htrace : ∀ t : Real,
      Realized.RicciTensorRealizesRm13Trace (I := I) (S.ricci t) (Rm13 t))
    (hRm : ∀ t : Real,
      Realized.Rm13RealizesConnection (I := I) (S.family.connection t) (Rm13 t))
    (hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞))
    (htf : ∀ t : Realized.RealTimeInterval.RegularTime D,
      LeviCivita.IsTorsionFree (I := I) (S.family.connection (t : Real)))
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hmixed : ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M))
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv
      (coordinateFrameAt (I := I) x₀))
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀) nablaRic)
    (hnabla2 :
      Nabla2RicciComponentsByConnectionInFrameOn
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric) :
    RicciVariationFormulaInFrameOnLocal
      (I := I) S (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric) := by
  classical
  have hA :
      RicciVariationFormulaInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
        (fun τ x d out l₁ l₂ =>
          christoffelVariationCovDerivCoordAt (I := I)
            (S.family.connection τ)
            (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
            τ x d out l₁ l₂) :=
    ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution
      (I := I) S Rm13 gInv nablaRic x₀ htrace hRm hcov htf hEvol hmixed
  intro t x hx i j
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact (hA t x₀ (by simp) i j).congr_deriv (by
    unfold ricciVariationFromConnectionRHSInFrame
    simp [christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
      (I := I) S gInv nablaRic nabla2Ric x₀ hinv hnabla hnabla2 t
      (Realized.RealizedMetricFamilyOn.metricCompatibleAt_regular
        (I := I) S.family t)])

end CoordinateRiemannVariation

/-- The rough Laplacian component `g^{ab} (nabla_a nabla_b Ric)_ij`. -/
def roughLapRicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x a b * nabla2Ric t x a b i j

/-- A component family realizes a supplied second covariant derivative tensor
of Ricci when it is obtained by evaluating a `(0,4)` tensor section on the
frame vectors.  The geometric assertion that this tensor is `∇∇Ric` is kept
separate from the component bookkeeping. -/
def Nabla2RicciTensorComponentsInFrameOn
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2RicTensor : Real -> Realized.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x d a i j,
    nabla2Ric t x d a i j =
      Realized.rm04Comp (I := I) (nabla2RicTensor t) frame x d a i j

/-- The Ricci variation RHS after substituting the Ricci-flow Christoffel
variation and expanding the trace
`nabla_k A^k_ij - nabla_i A^k_kj`.

This is the expression before the contracted-Bianchi/gauge cancellation and
the curvature-commutator simplification. -/
def ricciVariationExpandedRHSInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x k i j l -
        nabla2Ric t x k j i l +
        nabla2Ric t x k l i j)) -
    (∑ k : Idx, ∑ l : Idx,
      gInv t x k l *
        (-nabla2Ric t x i k j l -
          nabla2Ric t x i j k l +
          nabla2Ric t x i l k j))

/-- Algebraic substitution of the Ricci-flow connection variation into the
Ricci variation formula. -/
theorem ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationFromConnectionRHSInFrame (M := M)
        (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
        t x i j =
      ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j := by
  simp [ricciVariationFromConnectionRHSInFrame,
    nablaGammaDtFromNabla2RicInFrame, ricciVariationExpandedRHSInFrame]

/-- Final Lemma 6.3 reduction after expanding the Ricci variation formula.

This is exactly the textbook contracted-Bianchi plus covariant-derivative
commutator calculation: the gauge/scalar-Hessian terms cancel, and the
remaining commutator terms become
`2 R_ikjl Ric^kl - 2 Ric_i^k Ric_kj`. -/
def RicciVariationExpandedRHS_eq_evolutionRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (t : Real) x i j

/-- The term `∇^k ∇_i Ric_jk` in the proof of Lemma 6.3. -/
def contractedNabla2RicLeftInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k i j l

/-- The term `∇^k ∇_j Ric_ik` in the proof of Lemma 6.3. -/
def contractedNabla2RicRightInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k j i l

/-- The scalar-Hessian trace `∇_i ∇_j R` as it appears before the Hessian
cancellation in the component proof. -/
def scalarHessianFromNabla2RicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i j k l

/-- The divergence trace term `∇_i ∇^k Ric_jk`. -/
def contractedNabla2RicTraceAInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i k j l

/-- The divergence trace term `∇_i ∇^l Ric_lj`. -/
def contractedNabla2RicTraceBInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i l k j

/-- The two contracted commutator identities used in Lemma 6.3:
both second-derivative contractions equal
`1/2 Hess R - R_ikjl Ric^kl + Ric_i^k Ric_kj`, and the two divergence trace
terms in `∇_i A^k_kj` cancel for a symmetric Ricci tensor. -/
def RicciContractedCommutatorsInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j -
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j -
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j

private theorem ricciVariationExpandedRHSInFrame_eq_decomposed
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j =
      roughLapRicInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j +
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j +
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j := by
  let left : Real :=
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j
  let right : Real :=
    contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j
  let rough : Real :=
    roughLapRicInFrame (M := M) gInv nabla2Ric t x i j
  let hess : Real :=
    scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j
  let traceA : Real :=
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j
  let traceB : Real :=
    contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j
  have hfirst :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j)) =
        -left - right + rough := by
    dsimp [left, right, rough, contractedNabla2RicLeftInFrame,
      contractedNabla2RicRightInFrame, roughLapRicInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x k i j l) -
            gInv t x k l * nabla2Ric t x k j i l +
            gInv t x k l * nabla2Ric t x k l i j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k i j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k j i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k l i j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  have hsecond :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j)) =
        -traceA - hess + traceB := by
    dsimp [hess, traceA, traceB, scalarHessianFromNabla2RicInFrame,
      contractedNabla2RicTraceAInFrame, contractedNabla2RicTraceBInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x i k j l) -
            gInv t x k l * nabla2Ric t x i j k l +
            gInv t x k l * nabla2Ric t x i l k j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i k j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i j k l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i l k j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  unfold ricciVariationExpandedRHSInFrame
  rw [hfirst, hsecond]
  dsimp [left, right, rough, hess, traceA, traceB]
  ring

/-- The Lemma 6.3 expanded Ricci-variation RHS reduces to the Hamilton RHS
once the contracted commutator identities are supplied. -/
theorem ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (_hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hcomm t x i j).1
  have hright := (hcomm t x i j).2.1
  have htrace := (hcomm t x i j).2.2
  rw [ricciVariationExpandedRHSInFrame_eq_decomposed
    (M := M) gInv nabla2Ric (t : Real) x i j]
  rw [hleft, hright, htrace]
  simp [ricciEvolutionRHSInFrame]
  ring

/-- Contracted second Bianchi in fixed-frame components:
`∇^k Ric_ik = (1/2) ∇_i R`. -/
def contractedBianchiInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gradScalar : Real -> M -> Idx -> Real) : Prop :=
  forall t x i,
    (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l i k) =
      (1 / 2 : Real) * gradScalar t x i

/-- Commutator step for the second derivatives appearing after substituting
the Ricci-flow Christoffel variation into the Ricci variation formula. -/
def ricciSecondDerivativeCommute
    (secondDerivRic commutedSecondDerivRic :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x a b i j,
    secondDerivRic t x a b i j = commutedSecondDerivRic t x a b i j

/-- Gauge cancellation after contracted Bianchi:
the Hessian/scalar-divergence terms in the Ricci variation formula cancel. -/
def ricciVariationGaugeTerms_cancel
    (gaugeTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j, gaugeTerms t x i j = 0

/-- Curvature commutator reduction in Lemma 6.3:
the remaining commutator terms are exactly
`2 R_ikjℓ Ric^{kℓ} - 2 Ric_i^k Ric_kj`. -/
def ricciCurvatureTerms_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (curvatureTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j,
    curvatureTerms t x i j =
      2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

/-- Lemma 6.3 producer from the Ricci variation formula after substituting the
Ricci-flow Christoffel variation.  The remaining hypothesis is the precise
contracted-Bianchi plus commutator reduction. -/
theorem ricciEvolutionEquationInFrame_of_variation_expanded
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x i j
  exact (h_var t x i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))

/-- Local Lemma 6.3 producer from the local Ricci variation formula after
substituting the Ricci-flow Christoffel variation. -/
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x hx i j
  exact (h_var t x hx i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))

/-- Lemma 6.3 producer from the Ricci variation formula and the two contracted
commutator identities in the textbook proof. -/
theorem ricciEvolution_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrame_of_variation_expanded
    (I := I) S Rm04 gInv frame nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hInv hcomm)

/-- Local Lemma 6.3 producer from the local Ricci variation formula and the
contracted commutator identities in the textbook proof. -/
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    (I := I) S Rm04 gInv frame u nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hInv hcomm)

/-- LaTeX Lemma 6.3, `lem:evol-ricci`, in fixed-frame component display form,
assuming the Ricci variation formula and the contracted commutator reduction. -/
theorem evol_ricci_inFrame_of_variation_commutators
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x i j +
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have h :=
    ricciEvolutionEquationInFrame_apply
      (I := I)
      (h :=
        ricciEvolution_of_variation_commutators
          (I := I) S Rm04 gInv frame nabla2Ric hInv h_var hcomm)
      t x i j
  simpa [ricciEvolutionRHSInFrame] using h

/-- Product-rule derivative of the Ricci trace
`Ric_ij = g^{kl} Rm04_kijl`. -/
def ricciTraceDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x k l *
      Realized.rm04Comp (I := I) (Rm04 t) frame x k i j l +
    gInv t x k l * rm04Dt t x k i j l)

/-- The finite trace simplification that turns traced Riemann evolution into
Lemma 6.3's Ricci RHS.  This is the realized counterpart of the synthetic
`RicciFromRiemann.lean` trace algebra. -/
def RicciTraceDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j

/-- Trace a supplied lowered-Riemann evolution equation to the Ricci evolution
equation in the existing Section 6.2 component API. -/
theorem ricciEvolutionEquationInFrame_of_riemann_trace
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_trace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (h_rm : RiemannEvolutionEquationInFrameOn (I := I) (D := D) Rm04 frame rm04Dt)
    (h_simplify : RicciTraceDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapRic) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  let traceComp : Real -> Real :=
    fun s => ∑ k : Idx, ∑ l : Idx,
      gInv s x k l *
        Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l
  have htraceDeriv :
      HasDerivWithinAt traceComp
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    dsimp [traceComp, ricciTraceDerivRHSInFrame]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s =>
          ∑ l : Idx,
            gInv s x k l *
              Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l)
        (A' := fun k =>
          ∑ l : Idx,
            (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x k l *
              Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
            gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l))
        (s := D.carrier) (x := (t : Real))
        (fun k _hk =>
          by
            simpa [Finset.sum_apply] using
              (HasDerivWithinAt.fun_sum
                (u := (Finset.univ : Finset Idx))
                (A := fun l s =>
                  gInv s x k l *
                    Realized.rm04Comp (I := I) (Rm04 s) frame x k i j l)
                (A' := fun l =>
                  inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x k l *
                    Realized.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
                  gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l)
                (s := D.carrier) (x := (t : Real))
                (fun l _hl =>
                  by
                    exact (h_inv t x k l).mul (h_rm t x k i j l)))))
  have hricci :
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    refine htraceDeriv.congr ?_ ?_
    · intro s _hs
      exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace s x i j
    · exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace (t : Real) x i j
  exact hricci.congr_deriv (h_simplify t x i j)

/-! ## Corollary 6.5: Lichnerowicz form -/

/-- Raise the second index of a fixed-frame `(0,2)` tensor component family. -/
def tensorOneUpCompInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * h t x i a

/-- Left Ricci action on a `(0,2)` tensor: `Ric_i^k h_kj`. -/
def ricciLeftActionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      h t x k j

/-- Right Ricci action on a `(0,2)` tensor: `Ric_j^k h_ki`. -/
def ricciRightActionCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x j k *
      h t x k i

/-- Ricci-specialized Lichnerowicz RHS in fixed-frame components:
`Δ h_ij + 2 R_ikjℓ h^{kℓ} - Ric_i^k h_kj - Ric_j^k h_ki`.

For Corollary 6.5, `h` is the Ricci tensor. -/
def lichnerowiczRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapH h hRaised : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapH t x i j +
    2 * (∑ k : Idx, ∑ l : Idx,
      Realized.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        hRaised t x k l) -
    ricciLeftActionCompInFrame (I := I) S gInv frame h t x i j -
    ricciRightActionCompInFrame (I := I) S gInv frame h t x i j

/-- Component equation `∂t Ric = Δ_L Ric`. -/
def RicciLichnerowiczEquationInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j)
      D.carrier
      (t : Real)

/-- The finite component specialization of the Lichnerowicz RHS to `h = Ric`.
For a realized Levi-Civita Ricci tensor this follows from Ricci symmetry and
inverse-metric symmetry; it is kept explicit here as the small algebra frontier
for Corollary 6.5. -/
def RicciLichnerowiczSpecializesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j

/-- Fixed-frame symmetry of the Ricci tensor. -/
def RicciSymmetricInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    ricciCompInFrame (I := I) S frame t x i j =
      ricciCompInFrame (I := I) S frame t x j i

/-- The left Ricci action on `Ric` is definitionally the quadratic term from
Lemma 6.3. -/
theorem ricciLeftActionCompInFrame_eq_quadratic
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciLeftActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl

/-- The right Ricci action on `Ric` is the same quadratic term, using Ricci
symmetry and inverse-metric symmetry. -/
theorem ricciRightActionCompInFrame_eq_quadratic_of_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (t : Real) (x : M) (i j : Idx) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic t x j a, hRic t x k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv t x k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl

/-- Constructor for the Lichnerowicz specialization from the two Ricci-action
identities `Ric_i^k Ric_kj = Ric_i^k Ric_kj` and
`Ric_j^k Ric_ki = Ric_i^k Ric_kj`. -/
theorem ricciLichnerowiczSpecializesInFrame_of_actions
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_left : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciLeftActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j)
    (h_right : forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciRightActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  simp [lichnerowiczRHSInFrame,
    ricciEvolutionRHSInFrame, rmRicciContractionCompInFrame,
    h_left t x i j, h_right t x i j]
  ring

/-- Lichnerowicz specialization for `h = Ric`, produced from Ricci symmetry
and inverse-metric symmetry. -/
theorem ricciLichnerowiczSpecializesInFrame_of_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczSpecializesInFrame_of_actions
    (I := I) S Rm04 gInv frame roughLapRic
    (fun t x i j =>
      ricciLeftActionCompInFrame_eq_quadratic
        (I := I) S gInv frame (t : Real) x i j)
    (fun t x i j =>
      ricciRightActionCompInFrame_eq_quadratic_of_symm
        (I := I) S gInv frame hRic hInv (t : Real) x i j)

/-- Corollary 6.5: Lemma 6.3 implies the Ricci tensor evolves by the
Lichnerowicz heat equation. -/
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_spec : RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  exact (h_ricci t x i j).congr_deriv (h_spec t x i j).symm

/-- Corollary 6.5 with the standard symmetry inputs: Lemma 6.3 plus Ricci
symmetry and inverse-metric symmetry imply the Ricci-specialized
Lichnerowicz heat equation. -/
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczEquationInFrame_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic h_ricci
    (ricciLichnerowiczSpecializesInFrame_of_symm
      (I := I) S Rm04 gInv frame roughLapRic hRic hInv)

end Components

end RicciFlow
end RicciFlower
