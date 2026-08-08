import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.HeatOutputRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Tensor.RSTensor.RankZero
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma real_inner_eq_mul' (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  change RCLike.re ⟪a, b⟫_ℝ = a * b
  have h := RCLike.inner_apply a b
  have hrw : RCLike.re ⟪a, b⟫_ℝ = RCLike.re (b * (starRingEnd ℝ) a) := congrArg RCLike.re h
  rw [hrw]
  simp
  ring

omit [NeZero (Module.finrank ℝ E)] in
/-- The scalar `L²` inner product of two smooth scalars equals the integral
of their pointwise product. -/
theorem smoothToLp_inner_eq_integral_mul
    (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ⟪smoothToLp (I := I) (M := M) g f, smoothToLp (I := I) (M := M) g h⟫_ℝ =
      ∫ x, f.toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) f.memLp_two,
    MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) h.memLp_two] with x hx₁ hx₂
  rw [smoothToLp_apply, smoothToLp_apply]
  rw [hx₁, hx₂]
  exact real_inner_eq_mul' (f.toFun x) (h.toFun x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
lemma tensorEval_zero_zero_scalar0
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) Fin.elim0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x := by
  unfold TensorRSField.scalar0 TensorRSField.rs0
  simp only [SmoothCcTensor.toFun_apply, Tensor0SField.toScalarField]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
lemma separableForm_zero_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v : Fin 0 → E) (w : Fin 0 → E) :
    (separableFormAt (I := I) (M := M) g x 0) v w = 1 := by
  rw [separableFormAt_apply]
  simp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
/-- Pointwise identity for the smooth rank-(0,0) tensor inner product. -/
lemma tensorInnerPointwise_smooth_zero_zero
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x (S.toFun x) (T.toFun x) =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x := by
  unfold tensorInnerPointwise
  rw [tensorInnerPointwise_0s_zero_arity]
  rw [lowerAllUpperIndices_apply]
  rw [lowerAllUpperIndices_apply]
  have hS : (separableFormAt (I := I) (M := M) g x 0
        (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro w
    exact separableForm_zero_apply (I := I) (M := M) g x
      (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i)) w
  rw [hS]
  change ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) Fin.elim0 *
      ((T.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) Fin.elim0 =
    TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g S x]
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g T x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
/-- The tensor L² inner product of rank-(0,0) smooth tensors equals the
scalar L² inner product of their scalar evaluations. -/
theorem tensorL2Inner_zero_zero_eq_integral_scalar0_mul
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    tensorL2Inner (I := I) (M := M) g 0 0 S.toFun T.toFun =
      ∫ x,
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  apply integral_congr_ae
  filter_upwards with x
  exact tensorInnerPointwise_smooth_zero_zero (I := I) (M := M) g S T x

end HeatEquation
end Analysis
end DifferentialGeometry

end
