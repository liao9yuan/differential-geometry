import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Data.Real.Sqrt

noncomputable section

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def tensorInnerPointwise_0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (x : M) →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ → ℝ
  | 0, _g, _x, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, x, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))

lemma tensorInnerPointwise_0s_zero_arity
    (g : SmoothRiemannianMetric I M) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) 0 g x S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma tensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) := rfl

noncomputable def tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) : ℝ :=
  tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
    (lowerAllUpperIndices (I := I) (M := M) g r s x S)
    (lowerAllUpperIndices (I := I) (M := M) g r s x T)

noncomputable def tensorPointwiseNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s x S S)

end L2
end Integral
end DifferentialGeometry

end
