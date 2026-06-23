import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option linter.unusedSectionVars false in
theorem endoCov_iteratedCovGrad_diagonalProductGrid_le (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (W : SmoothCcTensor g 0 (s + 1)) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + j) x
        ((iteratedCovGrad (I := I) g 0 (s + 1) j
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g s Λ) W)).toSection x) ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g (s + 1) ((s + 1) + i) x
              ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
                (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + l) x
                ((iteratedCovGrad (I := I) g 0 (s + 1) l W).toSection x) :=
  appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g (s + 1) (s + 1)
    (slotInsertEndoCc (I := I) (M := M) g s Λ) W j x

end Connection
end Integral
end DifferentialGeometry

end
