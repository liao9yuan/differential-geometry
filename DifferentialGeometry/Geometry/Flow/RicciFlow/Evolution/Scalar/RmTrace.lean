import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section TraceRoute

variable {Idx : Type*} [Fintype Idx]

def ScalarRmRicciTraceInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    (∑ i : Idx, ∑ j : Idx,
      gInv (t : Real) x i j *
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j) =
      -ricciNormSqInFrame (I := I) S gInv frame (t : Real) x

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j) =
      2 * ricciNormSqInFrame (I := I) S gInv frame t x := by
  unfold inverseMetricEvolutionRHSInFrame ricciNormSqInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j)
        =
      ∑ i : Idx, ∑ j : Idx,
        2 * (ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          simp [Finset.mul_sum]

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j) =
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  unfold ricciQuadraticCompInFrame ricciOneUpCompInFrame
    ricciNormSqInFrame DifferentialGeometry.Integral.Connection.ricciNormSqInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame ricciTwoTensorField
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx,
          (∑ a : Idx,
            gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
              gInv t x i j * gInv t x k a *
                ricciCompInFrame (I := I) S frame t x i a *
                ricciCompInFrame (I := I) S frame t x k j)
                =
              ∑ j : Idx, ∑ a : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          gInv t x i j * gInv t x a k *
          ricciCompInFrame (I := I) S frame t x j k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInvSym t x k a, hRicSym t x k j]
          ring
    _ =
      ∑ i : Idx, ∑ a : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          (∑ j : Idx, ∑ k : Idx,
            gInv t x i j * gInv t x a k *
              ricciCompInFrame (I := I) S frame t x j k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hInvSym : forall i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j) =
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  unfold ricciQuadraticCompInFrame ricciOneUpCompInFrame
    ricciNormSqInFrame DifferentialGeometry.Integral.Connection.ricciNormSqInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame ricciTwoTensorField
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx,
          (∑ a : Idx,
            gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
              gInv t x i j * gInv t x k a *
                ricciCompInFrame (I := I) S frame t x i a *
                ricciCompInFrame (I := I) S frame t x k j)
                =
              ∑ j : Idx, ∑ a : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          gInv t x i j * gInv t x a k *
          ricciCompInFrame (I := I) S frame t x j k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInvSym k a, hRicSym k j]
          ring
    _ =
      ∑ i : Idx, ∑ a : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          (∑ j : Idx, ∑ k : Idx,
            gInv t x i j * gInv t x a k *
              ricciCompInFrame (I := I) S frame t x j k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x
  have hrm := hRmTrace t x
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
      (I := I) S gInv frame hInvSym hRicSym (t : Real) x
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

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (hInvSym : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      x i j,
      gInv (t : Real) x i j = gInv (t : Real) x j i)
    (hRicSym : RicciSymmetricInFrameOnRegular (I := I) S frame)
    (hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x
  have hrm := hRmTrace t x
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
      (I := I) S gInv frame (t : Real) x (hInvSym t x) (hRicSym t x)
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

end TraceRoute

end DifferentialGeometry.PDE.RicciFlow
