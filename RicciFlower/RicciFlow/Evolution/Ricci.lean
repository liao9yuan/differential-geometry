import RicciFlower.RicciFlow.Evolution.Connection
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

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

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

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
`∇_k A^k_ij - ∇_j A^k_ik`.

Here `nablaGammaDt t x d k i j` denotes the fixed-frame component
`(∇_d A)^k_ij`, where `A^k_ij = ∂_t Γ^k_ij`. -/
def ricciVariationFromConnectionRHSInFrame
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, nablaGammaDt t x k k i j) -
    (∑ k : Idx, nablaGammaDt t x j k i k)

/-- Ricci variation formula in a fixed frame:
`∂_t Ric_ij = ∇_k A^k_ij - ∇_j A^k_ik`.

This is the realized component target obtained by differentiating the
curvature trace of the connection. -/
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
`nabla_k A^k_ij - nabla_j A^k_ik`.

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
        (-nabla2Ric t x j i k l -
          nabla2Ric t x j k i l +
          nabla2Ric t x j l i k))

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

/-- The scalar-Hessian trace `∇_j ∇_i R` as it appears before the Hessian
cancellation in the component proof. -/
def scalarHessianFromNabla2RicInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x j i k l

/-- The dummy-index cancellation term `∇_j ∇^k Ric_ik`. -/
def contractedNabla2RicTraceAInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x j k i l

/-- The dummy-index cancellation term `∇_j ∇^l Ric_il`. -/
def contractedNabla2RicTraceBInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x j l i k

/-- The two contracted commutator identities used in Lemma 6.3:
both second-derivative contractions equal
`1/2 Hess R - R_ikjl Ric^kl + Ric_i^k Ric_kj`. -/
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
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j

private theorem contractedNabla2Ric_trace_swap
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (t : Real) (x : M) (i j : Idx) :
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j := by
  unfold contractedNabla2RicTraceAInFrame contractedNabla2RicTraceBInFrame
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l * nabla2Ric t x j k i l)
        = ∑ l : Idx, ∑ k : Idx,
            gInv t x k l * nabla2Ric t x j k i l := by
            rw [Finset.sum_comm]
    _ = ∑ l : Idx, ∑ k : Idx,
            gInv t x l k * nabla2Ric t x j k i l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hInv t x k l]
    _ = ∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x j l i k := by
            rw [Finset.sum_comm]

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
          (-nabla2Ric t x j i k l -
            nabla2Ric t x j k i l +
            nabla2Ric t x j l i k)) =
        -hess - traceA + traceB := by
    dsimp [hess, traceA, traceB, scalarHessianFromNabla2RicInFrame,
      contractedNabla2RicTraceAInFrame, contractedNabla2RicTraceBInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x j i k l -
            nabla2Ric t x j k i l +
            nabla2Ric t x j l i k))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x j i k l) -
            gInv t x k l * nabla2Ric t x j k i l +
            gInv t x k l * nabla2Ric t x j l i k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x j i k l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x j k i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x j l i k) := by
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
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hcomm t x i j).1
  have hright := (hcomm t x i j).2
  have hswap := contractedNabla2Ric_trace_swap
    (M := M) gInv nabla2Ric hInv (t : Real) x i j
  rw [ricciVariationExpandedRHSInFrame_eq_decomposed
    (M := M) gInv nabla2Ric (t : Real) x i j]
  rw [hleft, hright, hswap]
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
