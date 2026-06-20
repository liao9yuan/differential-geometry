import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS

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

theorem tensorL2Inner_covGrad_appCc_eq_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (T : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (appCc (I := I) (M := M) g r s Φ W)).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) W).toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun T.toFun := by
  classical
  set A1 : SmoothCcTensor g 0 (s + 1) :=
    appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W with hA1
  set A2 : SmoothCcTensor g 0 (s + 1) :=
    appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
      (covGrad (I := I) (M := M) g 0 r W) with hA2
  have hB : covGrad (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) = A1 + A2 :=
    covGrad_appCc_eq (I := I) (M := M) g r s Φ W
  have hstep := congrArg
    (fun Z : SmoothCcTensor g 0 (s + 1) =>
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Z.toFun T.toFun) hB
  simp only at hstep
  rw [hstep, SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    A1.toFun A2.toFun T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A1 T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A2 T)

theorem tensorL2Inner_appCc_covGrad_covGrad_eq_neg (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Φ : SmoothCcTensor g s s) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s Φ) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (appCc (I := I) (M := M) g s s Φ S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s Φ)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s Φ S
    (covGrad (I := I) (M := M) g 0 s S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g s s Φ S) S
  rw [hgreen] at hsplit
  linarith [hsplit]

end Connection
end Integral
end DifferentialGeometry

end
