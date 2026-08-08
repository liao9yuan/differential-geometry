import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.HeatOutputRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
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

abbrev TensorEigenIdx00 (g : SmoothRiemannianMetric I M) :=
  Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 0

/-- The rank-(0,0) smooth eigenvector is the corresponding Hilbert basis
element of the tensor `L²` space. -/
theorem eigenvectorSmooth00_eq_basis
    (g : SmoothRiemannianMetric I M) (j : TensorEigenIdx00 g) :
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) =
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j := by
  calc
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
        = tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
    _ = tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j).symm

/-- The tensor `L²` coefficient of the rank-(0,0) smooth eigenvector is the
Kronecker delta. -/
theorem tensorL2Coeff_eigenvectorSmooth00
    (g : SmoothRiemannianMetric I M) [DecidableEq (TensorEigenIdx00 g)]
    (i j : TensorEigenIdx00 g) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        ((eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)) i =
      (if i = j then (1 : ℝ) else 0) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  change (b.repr (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) i) =
    if i = j then (1 : ℝ) else 0
  have hbj : (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) = b j := by
    calc
      (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
          = tensorResolventEigenbasisVec (I := I) (M := M) hc j :=
        eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
      _ = b j := by
        rw [hb_def]
        exact (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M) hc j).symm
  rw [hbj]
  rw [HilbertBasis.repr_apply_apply]
  rw [real_inner_comm]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    simpa using horth j j
  · have hne : i ≠ j := fun hij => hji hij.symm
    rw [if_neg hne]
    exact Orthonormal.inner_eq_zero b.orthonormal hji

/-- The rank-(0,0) rough Laplacian of a smooth eigenvector is the eigenvalue
times the eigenvector. -/
theorem tensorEigen00_rawLap_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i)) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  apply b.repr.injective
  ext j
  change tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i))) j =
    tensorL2Coeff (I := I) (M := M) hc
      ((- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j
  rw [rawLap_coeff (I := I) (M := M) g 0 hc (eigenvectorSmooth g 0 0 i) j]
  rw [tensorL2Coeff_smul (I := I) (M := M) hc
    (- TensorEigenIdx.lambda (I := I) (M := M) i)
    (SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j]
  haveI : DecidableEq (TensorEigenIdx00 g) := Classical.decEq _
  have hcoeff := tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
  rw [← SmoothCcTensor.toL2_apply] at hcoeff
  rw [hcoeff]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

omit [CompactSpace M] in
/-- The rank-(0,0) rough Laplacian of a smooth tensor section equals the
`toRS0` lift of the scalar Laplacian of its scalar evaluation. -/
lemma rawLapSection_eq_toRS0 (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (x : M) :
    rawTensorConnLap g 0 0 (fun y : M => S.toSection y) x =
      ((Tensor0SNabla.tensor0Iso I M x).symm (laplacian (LeviCivita g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) x)).toRS0 := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  have hraw := rawLap_scalar (I := I) (M := M) g hf x
  have hlift := TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  rw [hlift] at hraw
  exact hraw

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] in
/-- The scalar Laplacian of the scalar evaluation is smooth. -/
lemma laplacian_scalar0_smooth (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (I := I) (LeviCivita (I := I) g) g
      (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection)) := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  refine (Δ_g_contMDiff (I := I) g hf).congr ?_
  intro x
  exact laplacian_levi_eq (I := I) g hf x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
/-- The fiber-model equivalence recovers the scalar value of a scalar field. -/
lemma tensor0Iso_fromScalarField
    (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    Tensor0SNabla.tensor0Iso I M y (Tensor0SField.fromScalarField ∞ f hf y) = f y := by
  unfold Tensor0SField.fromScalarField Tensor0SNabla.tensor0Iso
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      (Tensor0SSpace.toModel (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I y) (f y))) = f y
  rfl

end HeatEquation
end Analysis
end DifferentialGeometry

end
