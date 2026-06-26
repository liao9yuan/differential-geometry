import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem tensorL2Inner_appCc_nonsquare_covGrad_covGrad_eq_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ) W).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (appCc (I := I) (M := M) g r s Φ W)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g r s Φ W
    (covGrad (I := I) (M := M) g 0 s S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) S
  rw [hgreen] at hsplit
  linarith [hsplit]

end Connection
end Integral
end DifferentialGeometry

end
