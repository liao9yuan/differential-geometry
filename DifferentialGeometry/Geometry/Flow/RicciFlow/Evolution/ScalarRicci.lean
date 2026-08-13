import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

private theorem sum_swap_four
    {R : Type*} [AddCommMonoid R]
    (F : Idx -> Idx -> Idx -> Idx -> R) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l) =
                ∑ i : Idx, ∑ l : Idx, ∑ j : Idx, F i j k l := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ = ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
                  rw [Finset.sum_comm]

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j) =
      scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric) t x := by
  classical
  unfold scalarHessianFromNabla2RicInFrame scalarLaplacianTraceInFrame
    roughLapRicInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx, ∑ l : Idx, gInv t x k l * nabla2Ric t x i j k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) := by
          simp [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) :=
          sum_swap_four
            (Idx := Idx)
            (fun i j k l =>
              gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l))
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x k l i j) := by
          simp [mul_left_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            (∑ k : Idx, ∑ l : Idx,
              gInv t x k l * nabla2Ric t x k l i j) := by
          simp [Finset.mul_sum]

end DifferentialGeometry.PDE.RicciFlow
