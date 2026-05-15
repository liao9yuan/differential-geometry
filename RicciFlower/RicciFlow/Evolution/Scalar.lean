/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Curvature Evolution

This file records the scalar-curvature simplification in MSM110 Chapter 6,
Section 1.  The full geometric inputs are kept explicit: one hypothesis is the
pre-Bianchi Ricci-flow scalar evolution, and the second is the contracted
Bianchi reduction that turns it into the heat-type scalar equation.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- MSM110 Chapter 6, Section 1, equation
`eq:scalar_curvature_ricci_flow_one`.

This is the scalar-curvature evolution immediately after substituting
`∂t g = -2 Ric`, before applying the contracted Bianchi identity:
`∂t R = 2 ΔR - 2 Q + 2 |Ric|²`, where `Q` denotes the contracted second
derivative term `g^{jk} g^{pq} ∇_q ∇_j R_{kp}`. -/
def ScalarPreBianchiEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x +
        2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-- The contracted-Bianchi simplification used in MSM110 Chapter 6, Section 1:
`2 ΔR - 2 Q = ΔR`. -/
def ScalarContractedBianchiReductionOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x =
      scalarLap (t : Real) x

/-- Contracted second-Bianchi identity in the scalar-curvature calculation:
the twice-contracted Ricci Hessian term is half the scalar Laplacian. -/
def ScalarSecondDerivativeContractedBianchiOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    contractedRicciHessian (t : Real) x =
      (1 / 2 : Real) * scalarLap (t : Real) x

/-- The scalar contracted-Bianchi identity supplies the algebraic reduction
`2 ΔR - 2 Q = ΔR` used in MSM110 Chapter 6.1. -/
theorem scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian := by
  intro t x
  rw [hbianchi t x]
  ring

/-- MSM110 Chapter 6, Section 1, equation `eq:scalar_curv_evolu`.

The scalar curvature heat equation follows from the pre-Bianchi scalar
evolution and the contracted-Bianchi reduction. -/
theorem scalarEvolutionEquationOn_of_contractedBianchi
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq := by
  intro t x
  exact (hpre t x).congr_deriv (by
    rw [hbianchi t x])

/-- Book-facing name for MSM110 Chapter 6, Section 1,
`eq:scalar_curv_evolu`. -/
theorem msm110_ch6_1_scalar_curvature_evolution
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  scalarEvolutionEquationOn_of_contractedBianchi
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi

section TraceRoute

variable {Idx : Type*} [Fintype Idx]

/-- Scalar curvature as the metric trace of the Ricci tensor in a fixed frame:
`R = g^{ij} Ric_ij`. -/
def scalarTraceInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      gInv t x i j * ricciCompInFrame (I := I) S frame t x i j

@[simp] theorem scalarTraceInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        gInv t x i j * ricciCompInFrame (I := I) S frame t x i j := by
  rfl

/-- Product-rule RHS for differentiating the scalar trace
`g^{ij} Ric_ij`. -/
def scalarTraceDerivRHSInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j +
      gInv t x i j *
        ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)

/-- The supplied scalar Laplacian is the metric trace of the rough Laplacian
of Ricci in the chosen frame. -/
def ScalarLaplacianTraceInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real) : Prop :=
  ∀ t x,
    scalarLap t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j

/-- Finite-sum contraction package needed after tracing Lemma 6.3.

For Ricci-flow applications this is the convention algebra saying that the
inverse-metric variation contributes `2 |Ric|^2`, while the traced curvature
and quadratic terms in Lemma 6.3 cancel. -/
def ScalarTraceDerivativeSimplifiesInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x

/-- The three finite-sum trace contractions used after substituting Lemma 6.3
into the derivative of `R = g^{ij} Ric_ij`. -/
def ScalarTraceAlgebraInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    (∑ i : Idx, ∑ j : Idx,
      inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
        ricciCompInFrame (I := I) S frame (t : Real) x i j) =
      2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x ∧
    (∑ i : Idx, ∑ j : Idx,
      gInv (t : Real) x i j *
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j) =
      -ricciNormSqInFrame (I := I) S gInv frame (t : Real) x ∧
    (∑ i : Idx, ∑ j : Idx,
      gInv (t : Real) x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) =
      ricciNormSqInFrame (I := I) S gInv frame (t : Real) x

/-- The trace algebra and scalar-Laplacian trace identify the derivative RHS
of `g^{ij} Ric_ij` with `Delta R + 2 |Ric|^2`. -/
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (h_alg : ScalarTraceAlgebraInFrame (I := I) S Rm04 gInv frame)
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt := (h_alg t x).1
  have hrm := (h_alg t x).2.1
  have hquad := (h_alg t x).2.2
  unfold scalarTraceDerivRHSInFrame
  rw [h_lap (t : Real) x]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j +
          gInv (t : Real) x i j *
            ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
              (t : Real) x i j)) =
        (∑ i : Idx, ∑ j : Idx,
          inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j) +
        (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j * roughLapRic (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
              (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) := by
    simp [ricciEvolutionRHSInFrame, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_mul]
    ring_nf
  rw [hsplit, hdt, hrm, hquad]
  ring

/-- Producer for the scalar trace simplification from the finite-sum trace
algebra package. -/
theorem ScalarTraceDerivativeSimplifiesInFrame.of_traceAlgebra
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (h_alg : ScalarTraceAlgebraInFrame (I := I) S Rm04 gInv frame) :
    ScalarTraceDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic scalarLap := by
  intro t x
  exact scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
    (I := I) S Rm04 gInv frame roughLapRic scalarLap h_lap h_alg t x

/-- Product-rule derivative of the scalar trace `g^{ij} Ric_ij`. -/
theorem scalarTraceInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x)
      (scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [scalarTraceInFrame, scalarTraceDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i j *
              ricciCompInFrame (I := I) S frame (t : Real) x i j +
            gInv (t : Real) x i j *
              ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
              (A' := fun j =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i j *
                    ricciCompInFrame (I := I) S frame (t : Real) x i j +
                  gInv (t : Real) x i j *
                    ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hInv := h_inv t x i j
                  have hRic := h_ricci t x i j
                  exact hInv.mul hRic))))

/-- Lemma 6.6 from Lemma 6.3 by tracing the Ricci equation. -/
theorem scalarEvolutionEquationOn_of_ricciEvolution
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (scalar scalarLap : Real -> M -> Real)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hScalar : ∀ t x,
      scalar t x = scalarTraceInFrame (I := I) S gInv frame t x)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_simplify : ScalarTraceDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic scalarLap) :
    ScalarEvolutionEquationOn (D := D)
      scalar scalarLap (ricciNormSqInFrame (I := I) S gInv frame) := by
  intro t x
  have htrace :=
    scalarTraceInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  have hscalar :
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x)
        D.carrier
        (t : Real) :=
    htrace.congr
      (fun s _hs => hScalar s x)
      (hScalar (t : Real) x)
  exact hscalar.congr_deriv (h_simplify t x)

/-- Lemma 6.6 from Lemma 6.3, using the scalar-Laplacian trace and the
finite-sum trace algebra package directly. -/
theorem scalarEvolutionEquationOn_of_ricciEvolution_and_traceAlgebra
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (scalar scalarLap : Real -> M -> Real)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hScalar : ∀ t x,
      scalar t x = scalarTraceInFrame (I := I) S gInv frame t x)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (h_alg : ScalarTraceAlgebraInFrame (I := I) S Rm04 gInv frame) :
    ScalarEvolutionEquationOn (D := D)
      scalar scalarLap (ricciNormSqInFrame (I := I) S gInv frame) :=
  scalarEvolutionEquationOn_of_ricciEvolution
    (I := I) S scalar scalarLap Rm04 gInv frame roughLapRic hScalar
    h_inv h_ricci
    (ScalarTraceDerivativeSimplifiesInFrame.of_traceAlgebra
      (I := I) S Rm04 gInv frame roughLapRic scalarLap h_lap h_alg)

end TraceRoute

end RicciFlow
end RicciFlower
