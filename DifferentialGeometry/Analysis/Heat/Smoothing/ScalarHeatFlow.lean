import DifferentialGeometry.Analysis.Heat.Smoothing.SpectralBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ScalarWeyl
import DifferentialGeometry.Analysis.Heat.Semigroup.Mass
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent

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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def scalarHeatCoeff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) : ℝ :=
  Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i

noncomputable def scalarHeatFlow
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g) : ℝ → M → ℝ :=
  fun t x => scalarSpecSum (I := I) (M := M) g
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x

noncomputable def scalar0Cc
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) : SmoothScalar g :=
  ⟨TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection,
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection⟩

noncomputable def scalar0CcLinear
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 0 →ₗ[ℝ] SmoothScalar g where
  toFun := scalar0Cc g
  map_add' := by
    intro S T
    apply SmoothScalar.ext
    funext x
    simp [scalar0Cc]
  map_smul' := by
    intro c S
    apply SmoothScalar.ext
    funext x
    simp [scalar0Cc]

noncomputable def scalar0ToLpLin
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 0 →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothToLp (I := I) (M := M) g).toLinearMap.comp (scalar0CcLinear g)

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar0ToLpLin_inner_eq_toL2_inner
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    ⟪scalar0ToLpLin (I := I) (M := M) g S, scalar0ToLpLin (I := I) (M := M) g T⟫_ℝ =
      ⟪SmoothCcTensor.toL2 S, SmoothCcTensor.toL2 T⟫_ℝ := by
  calc
    ⟪scalar0ToLpLin (I := I) (M := M) g S, scalar0ToLpLin (I := I) (M := M) g T⟫_ℝ
        = ⟪smoothToLp (I := I) (M := M) g (scalar0Cc g S),
            smoothToLp (I := I) (M := M) g (scalar0Cc g T)⟫_ℝ := rfl
    _ = ∫ x, (scalar0Cc g S).toFun x * (scalar0Cc g T).toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        smoothToLp_inner_eq_integral_mul (I := I) (M := M) g (scalar0Cc g S) (scalar0Cc g T)
    _ = ∫ x,
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
            TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl
    _ = tensorL2Inner (I := I) (M := M) g 0 0 S.toFun T.toFun :=
        (tensorL2Inner_zero_zero_eq_integral_scalar0_mul (I := I) (M := M) g S T).symm
    _ = ⟪S, T⟫_ℝ := rfl
    _ = ⟪SmoothCcTensor.toL2 S, SmoothCcTensor.toL2 T⟫_ℝ :=
        (Integral.L2.SmoothCcTensor.inner_toL2 S T).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar0ToLpLin_norm_eq
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) :
    ‖scalar0ToLpLin (I := I) (M := M) g S‖ = ‖S‖ := by
  have hsq : ‖scalar0ToLpLin (I := I) (M := M) g S‖ ^ 2 = ‖S‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (scalar0ToLpLin (I := I) (M := M) g S),
      ← real_inner_self_eq_norm_sq S]
    rw [← (Integral.L2.SmoothCcTensor.inner_toL2 S S)]
    exact scalar0ToLpLin_inner_eq_toL2_inner (I := I) (M := M) g S S
  have hnorm : |‖scalar0ToLpLin (I := I) (M := M) g S‖| = |‖S‖| :=
    (sq_eq_sq_iff_abs_eq_abs ‖scalar0ToLpLin (I := I) (M := M) g S‖ ‖S‖).mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hnorm
  exact hnorm

noncomputable def scalar0ToLp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 0 →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (scalar0ToLpLin (I := I) (M := M) g).mkContinuous 1 (fun S => by
    rw [scalar0ToLpLin_norm_eq (I := I) (M := M) g S]
    simp)

noncomputable def tensor00ToScalarL2
    (g : SmoothRiemannianMetric I M) : TensorL2 0 0 g →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  UniformSpace.Completion.extension
    (fun S : SmoothCcTensor g 0 0 => scalar0ToLp (I := I) (M := M) g S)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_toL2
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) :
    tensor00ToScalarL2 g (SmoothCcTensor.toL2 S) =
      scalar0ToLp (I := I) (M := M) g S := by
  unfold tensor00ToScalarL2
  exact UniformSpace.Completion.extension_coe
    (f := fun S : SmoothCcTensor g 0 0 => scalar0ToLp (I := I) (M := M) g S)
    (scalar0ToLp (I := I) (M := M) g).uniformContinuous S

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_add
    (g : SmoothRiemannianMetric I M) (x y : TensorL2 0 0 g) :
    tensor00ToScalarL2 g (x + y) =
      tensor00ToScalarL2 g x + tensor00ToScalarL2 g y := by
  have hcont : Continuous (tensor00ToScalarL2 g) :=
    UniformSpace.Completion.continuous_extension
      (f := fun S : SmoothCcTensor g 0 0 => scalar0ToLp (I := I) (M := M) g S)
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g 0 0)
    (p := fun z : TensorL2 0 0 g =>
      tensor00ToScalarL2 g (z + y) = tensor00ToScalarL2 g z + tensor00ToScalarL2 g y)
    x ?_ ?_
  · have hcont_lhs : Continuous (fun x : TensorL2 0 0 g =>
        tensor00ToScalarL2 g (x + y)) :=
      hcont.comp (continuous_add_const y)
    have hcont_rhs : Continuous (fun x : TensorL2 0 0 g =>
        tensor00ToScalarL2 g x + tensor00ToScalarL2 g y) :=
      hcont.add continuous_const
    exact isClosed_eq hcont_lhs hcont_rhs
  · intro S
    refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g 0 0)
      (p := fun w : TensorL2 0 0 g =>
        tensor00ToScalarL2 g (SmoothCcTensor.toL2 S + w) =
          tensor00ToScalarL2 g (SmoothCcTensor.toL2 S) + tensor00ToScalarL2 g w)
      y ?_ ?_
    · have hcont_lhs : Continuous (fun y : TensorL2 0 0 g =>
          tensor00ToScalarL2 g (SmoothCcTensor.toL2 S + y)) :=
        hcont.comp ((continuous_const : Continuous
          fun _ : TensorL2 0 0 g => SmoothCcTensor.toL2 S).add continuous_id)
      have hcont_rhs : Continuous (fun y : TensorL2 0 0 g =>
          tensor00ToScalarL2 g (SmoothCcTensor.toL2 S) + tensor00ToScalarL2 g y) :=
        hcont.const_add (tensor00ToScalarL2 g (SmoothCcTensor.toL2 S))
      exact isClosed_eq hcont_lhs hcont_rhs
    · intro T
      change tensor00ToScalarL2 g (SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T) =
        tensor00ToScalarL2 g (SmoothCcTensor.toL2 S) + tensor00ToScalarL2 g (SmoothCcTensor.toL2 T)
      rw [← (SmoothCcTensor.toL2 : SmoothCcTensor g 0 0 →L[ℝ] TensorL2 0 0 g).map_add S T]
      rw [tensor00ToScalarL2_toL2, tensor00ToScalarL2_toL2, tensor00ToScalarL2_toL2]
      exact (scalar0ToLp (I := I) (M := M) g).map_add S T

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : TensorL2 0 0 g) :
    tensor00ToScalarL2 g (c • x) = c • tensor00ToScalarL2 g x := by
  have hcont : Continuous (tensor00ToScalarL2 g) :=
    UniformSpace.Completion.continuous_extension
      (f := fun S : SmoothCcTensor g 0 0 => scalar0ToLp (I := I) (M := M) g S)
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g 0 0)
    (p := fun z : TensorL2 0 0 g =>
      tensor00ToScalarL2 g (c • z) = c • tensor00ToScalarL2 g z)
    x ?_ ?_
  · have hcont_lhs : Continuous (fun x : TensorL2 0 0 g =>
        tensor00ToScalarL2 g (c • x)) :=
      hcont.comp (continuous_const_smul c)
    have hcont_rhs : Continuous (fun x : TensorL2 0 0 g =>
        c • tensor00ToScalarL2 g x) :=
      hcont.const_smul c
    exact isClosed_eq hcont_lhs hcont_rhs
  · intro S
    change tensor00ToScalarL2 g (c • SmoothCcTensor.toL2 S) =
      c • tensor00ToScalarL2 g (SmoothCcTensor.toL2 S)
    rw [← (SmoothCcTensor.toL2 : SmoothCcTensor g 0 0 →L[ℝ] TensorL2 0 0 g).map_smul c S]
    rw [tensor00ToScalarL2_toL2, tensor00ToScalarL2_toL2]
    exact (scalar0ToLp (I := I) (M := M) g).map_smul c S

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_norm
    (g : SmoothRiemannianMetric I M) (x : TensorL2 0 0 g) :
    ‖tensor00ToScalarL2 g x‖ = ‖x‖ := by
  have hcont : Continuous (tensor00ToScalarL2 g) :=
    UniformSpace.Completion.continuous_extension
      (f := fun S : SmoothCcTensor g 0 0 => scalar0ToLp (I := I) (M := M) g S)
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g 0 0)
    (p := fun z : TensorL2 0 0 g => ‖tensor00ToScalarL2 g z‖ = ‖z‖)
    x ?_ ?_
  · have hcont_lhs : Continuous (fun x : TensorL2 0 0 g =>
        ‖tensor00ToScalarL2 g x‖) :=
      hcont.norm
    have hcont_rhs : Continuous (fun x : TensorL2 0 0 g => ‖x‖) := continuous_norm
    exact isClosed_eq hcont_lhs hcont_rhs
  · intro S
    change ‖tensor00ToScalarL2 g (SmoothCcTensor.toL2 S)‖ = ‖SmoothCcTensor.toL2 S‖
    rw [tensor00ToScalarL2_toL2]
    simpa [Integral.L2.SmoothCcTensor.norm_toL2]
      using (scalar0ToLpLin_norm_eq (I := I) (M := M) g S)

noncomputable def tensor00ToScalarL2LI
    (g : SmoothRiemannianMetric I M) : TensorL2 0 0 g →ₗᵢ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun := tensor00ToScalarL2 g
  map_add' := tensor00ToScalarL2_add g
  map_smul' := tensor00ToScalarL2_smul g
  norm_map' := tensor00ToScalarL2_norm g

noncomputable def scalarCcLift
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) : SmoothCcTensor g 0 0 where
  toSection := (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f.toFun f.smooth).toTensorRSField ∞
  hasCompactSupport := IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem scalar0Cc_scalarCcLift
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    scalar0Cc g (scalarCcLift g f) = f := by
  apply SmoothScalar.ext
  funext x
  have h : TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
      ((Tensor0SField.fromScalarField ∞ f.toFun f.smooth).toTensorRSField ∞) =
      f.toFun := by
    unfold TensorRSField.scalar0
    rw [TensorRSField.rs0_toRS0]
    exact Tensor0SField.toScalarField_fromScalarField ∞ f.toFun f.smooth
  exact congrFun h x

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar0ToLp_scalarCcLift
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    scalar0ToLp (I := I) (M := M) g (scalarCcLift g f) =
      smoothToLp (I := I) (M := M) g f := by
  change scalar0ToLpLin (I := I) (M := M) g (scalarCcLift g f) =
    smoothToLp (I := I) (M := M) g f
  change smoothToLp (I := I) (M := M) g (scalar0Cc g (scalarCcLift g f)) =
    smoothToLp (I := I) (M := M) g f
  rw [scalar0Cc_scalarCcLift]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_denseRange
    (g : SmoothRiemannianMetric I M) :
    DenseRange (tensor00ToScalarL2 g) := by
  have hsub : Set.range (smoothToLp (I := I) (M := M) g) ⊆
      Set.range (tensor00ToScalarL2 g) := by
    rintro y ⟨f, rfl⟩
    refine ⟨SmoothCcTensor.toL2 (scalarCcLift g f), ?_⟩
    rw [tensor00ToScalarL2_toL2]
    exact scalar0ToLp_scalarCcLift (I := I) (M := M) g f
  exact Dense.mono hsub (denseRange_smoothToLp (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor00ToScalarL2_surjective
    (g : SmoothRiemannianMetric I M) :
    Function.Surjective (tensor00ToScalarL2 g) := by
  have hclosed : IsClosed (Set.range (tensor00ToScalarL2 g)) :=
    (tensor00ToScalarL2LI g).isometry.isUniformInducing.isComplete_range.isClosed
  have hrange : Set.range (tensor00ToScalarL2 g) = Set.univ := by
    apply subset_antisymm (subset_univ _)
    intro y hy
    have hcl : closure (Set.range (tensor00ToScalarL2 g)) = Set.univ :=
      (tensor00ToScalarL2_denseRange (I := I) (M := M) g).closure_eq
    have hycl : y ∈ closure (Set.range (tensor00ToScalarL2 g)) := by
      rw [hcl]
      trivial
    rwa [hclosed.closure_eq] at hycl
  intro y
  have hy : y ∈ Set.range (tensor00ToScalarL2 g) := by
    rw [hrange]
    trivial
  exact hy

noncomputable def tensor00ScalarL2Equiv
    (g : SmoothRiemannianMetric I M) :
    TensorL2 0 0 g ≃ₗᵢ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  LinearIsometryEquiv.ofSurjective (tensor00ToScalarL2LI g)
    (tensor00ToScalarL2_surjective g)

noncomputable def scalarEigenFunction
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) : SmoothScalar g :=
  scalar0Cc g (eigenvectorSmooth g 0 0 i)

noncomputable def scalarEigenFunctionLp
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothToLp (I := I) (M := M) g (scalarEigenFunction g i)

theorem scalarEigenFunction_laplacian_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    (scalarEigenFunction g i).laplacian =
      (-TensorEigenIdx.lambda (I := I) (M := M) i) • scalarEigenFunction g i := by
  apply SmoothScalar.ext
  funext x
  rw [SmoothScalar.laplacian_toFun]
  rw [← laplacian_levi_eq (I := I) g (scalarEigenFunction g i).smooth x]
  exact scalarEigen00_laplacian_eq (I := I) (M := M) g i x

theorem laplacianOp_scalarEigenFunctionLp
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g i),
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (scalarEigenFunction g i)⟩ =
      (-TensorEigenIdx.lambda (I := I) (M := M) i) • scalarEigenFunctionLp g i := by
  rw [laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian]
  rw [scalarEigenFunction_laplacian_eq]
  rfl

theorem scalarEigenFunctionLp_eq_tensorBasis
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    scalarEigenFunctionLp g i =
      tensor00ScalarL2Equiv g (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) := by
  unfold scalarEigenFunctionLp scalarEigenFunction
  change smoothToLp (I := I) (M := M) g (scalar0Cc g (eigenvectorSmooth g 0 0 i)) =
    tensor00ToScalarL2 g (SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i))
  rw [tensor00ToScalarL2_toL2]
  rfl

theorem heatSemigroup_apply_scalarEigenFunctionLp
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g)
    {t : ℝ} (ht : 0 ≤ t) :
    heatSemigroup (I := I) (M := M) g t (scalarEigenFunctionLp g i) =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
        scalarEigenFunctionLp g i := by
  classical
  set w := scalarEigenFunctionLp g i
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  let hw_h : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g i),
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (scalarEigenFunction g i)⟩
  have hH1 : H1ComplToLp (I := I) (M := M) g (hw_h : H1Compl g) = w := by
    change H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g i)) = w
    rw [H1ComplToLp_smoothToH1Compl]
    rfl
  have hcoeff (j : EigenIdx (I := I) (M := M) g) :
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) * ⟪b j, w⟫_ℝ =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b j, w⟫_ℝ := by
    by_cases hj : EigenIdx.lambda (I := I) (M := M) j =
        TensorEigenIdx.lambda (I := I) (M := M) i
    · rw [hj]
    · have hzero : ⟪b j, w⟫_ℝ = 0 := by
        have hinner_lap := laplacianOp_inner_eigenbasis (I := I) (M := M) g hw_h j
        have h1 : ⟪b j, laplacianOp (I := I) (M := M) g hw_h⟫_ℝ =
            -EigenIdx.lambda (I := I) (M := M) j * ⟪b j, w⟫_ℝ := by
          rw [hinner_lap, hH1]
        have h2 : ⟪b j, laplacianOp (I := I) (M := M) g hw_h⟫_ℝ =
            -TensorEigenIdx.lambda (I := I) (M := M) i * ⟪b j, w⟫_ℝ := by
          change ⟪b j, laplacianOp (I := I) (M := M) g
              ⟨smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g i),
                smoothToH1Compl_mem_laplacianDomain (I := I) (M := M)
                  (scalarEigenFunction g i)⟩⟫_ℝ =
            -TensorEigenIdx.lambda (I := I) (M := M) i * ⟪b j, w⟫_ℝ
          rw [laplacianOp_scalarEigenFunctionLp (I := I) (M := M) g i]
          simp [inner_smul_right, w]
        have hsub : (EigenIdx.lambda (I := I) (M := M) j -
            TensorEigenIdx.lambda (I := I) (M := M) i) * ⟪b j, w⟫_ℝ = 0 := by
          nlinarith [h1, h2]
        exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hj)
      simp [hzero]
  calc
    heatSemigroup (I := I) (M := M) g t w
        = ∑' j, Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
            ⟪b j, w⟫_ℝ • b j :=
          heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht w
    _ = ∑' j, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b j, w⟫_ℝ • b j := by
          apply tsum_congr
          intro j
          rw [smul_smul, smul_smul]
          congr 1
          exact hcoeff j
    _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
          ∑' j, ⟪b j, w⟫_ℝ • b j := by
          have hsum_repr :
              (∑' j, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                  (b.repr w j • b j)) =
                Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                  (∑' j, b.repr w j • b j) :=
                Summable.tsum_const_smul
                  (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t))
                  (b.hasSum_repr w).summable
          calc
            (∑' j, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                (⟪b j, w⟫_ℝ • b j))
                = (∑' j, Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                    (b.repr w j • b j)) := by
                  apply tsum_congr
                  intro j
                  congr 1
                  congr 1
                  exact (HilbertBasis.repr_apply_apply b w j).symm
            _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                  (∑' j, b.repr w j • b j) := hsum_repr
            _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) •
                  (∑' j, ⟪b j, w⟫_ℝ • b j) := by
                  congr 1
                  apply tsum_congr
                  intro j
                  congr 1
                  exact HilbertBasis.repr_apply_apply b w j
    _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) • w := by
          rw [show (∑' j, ⟪b j, w⟫_ℝ • b j) = w from
            by simpa [HilbertBasis.repr_apply_apply] using (b.hasSum_repr w).tsum_eq]

theorem hasSum_scalarEigenFunctionLp_repr
    (g : SmoothRiemannianMetric I M)
    (v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, v⟫_ℝ • scalarEigenFunctionLp g i) v := by
  classical
  set L := tensor00ScalarL2Equiv g
  set b' := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
  have hb' : HasSum (fun i : TensorEigenIdx00 g =>
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)).repr (L.symm v) i •
        (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i)
      (L.symm v) :=
    (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)).hasSum_repr (L.symm v)
  have hmap : HasSum (fun i : TensorEigenIdx00 g =>
      L ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)).repr (L.symm v) i •
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i))
      (L (L.symm v)) :=
    (L : TensorL2 0 0 g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)).hasSum
      hb'
  have hL : L (L.symm v) = v := by simp
  have hLb (i : TensorEigenIdx00 g) :
      L ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i) =
          scalarEigenFunctionLp g i := by
    apply (tensor00ScalarL2Equiv g).symm.injective
    calc
      (tensor00ScalarL2Equiv g).symm
          (L ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i))
          = (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i := by
            simp [L]
      _ = (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) :=
            (eigenvectorSmooth00_eq_basis (I := I) (M := M) g i).symm
      _ = (tensor00ScalarL2Equiv g).symm (scalarEigenFunctionLp g i) := by
            have hφ := scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i
            rw [hφ]
            simp
  have hsummand (i : TensorEigenIdx00 g) :
      L ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)).repr (L.symm v) i •
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i) =
        ⟪scalarEigenFunctionLp g i, v⟫_ℝ • scalarEigenFunctionLp g i := by
    rw [L.map_smul]
    have hc : (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)).repr (L.symm v) i =
        ⟪scalarEigenFunctionLp g i, v⟫_ℝ := by
      rw [HilbertBasis.repr_apply_apply]
      have hbv : ⟪(tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i, L.symm v⟫_ℝ =
          ⟪L ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i), v⟫_ℝ := by
        have h := (L.toLinearIsometry).inner_map_map
          ((tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)) i) (L.symm v)
        exact h.symm.trans (by simp [L.apply_symm_apply])
      rw [hbv, hLb i]
    rw [hc]
    congr 2
    exact hLb i
  simpa [hL] using (HasSum.congr_fun hmap (fun i => (hsummand i).symm))

theorem tensor00ScalarL2Equiv_tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t) (U : TensorL2 0 0 g) :
    tensor00ScalarL2Equiv g (tensorHeatSemigroup g 0 0 t U) =
      heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g U) := by
  classical
  set L := tensor00ScalarL2Equiv g
  set v := L U
  have hadj (x : TensorL2 0 0 g) (y : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
      ⟪L x, y⟫_ℝ = ⟪x, L.symm y⟫_ℝ := by
    have h := (L.toLinearIsometry).inner_map_map x (L.symm y)
    simpa [L.apply_symm_apply] using h
  have hcoeff (i : TensorEigenIdx00 g) :
      ⟪scalarEigenFunctionLp g i, L (tensorHeatSemigroup g 0 0 t U)⟫_ℝ =
        ⟪scalarEigenFunctionLp g i, heatSemigroup (I := I) (M := M) g t v⟫_ℝ := by
    have hφ : scalarEigenFunctionLp g i =
        L (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) :=
      scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i
    calc
      ⟪scalarEigenFunctionLp g i, L (tensorHeatSemigroup g 0 0 t U)⟫_ℝ
          = ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g),
              tensorHeatSemigroup g 0 0 t U⟫_ℝ := by
              rw [hφ]
              exact (hadj (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)
                  (L (tensorHeatSemigroup g 0 0 t U))).trans (by simp [L])
      _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g), U⟫_ℝ := by
              have hc1 : ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g),
                    tensorHeatSemigroup g 0 0 t U⟫_ℝ =
                  tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
                    (tensorHeatSemigroup g 0 0 t U) i := by
                rw [tensorL2Coeff_eq_inner]
                congr 1
                exact eigenvectorSmooth00_eq_basis (I := I) (M := M) g i
              rw [hc1]
              rw [tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact (I := I) (M := M) g 0 0 ht U i]
              have hc2 : tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) U i =
                  ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g), U⟫_ℝ := by
                rw [tensorL2Coeff_eq_inner]
                congr 1
                exact (eigenvectorSmooth00_eq_basis (I := I) (M := M) g i).symm
              rw [← hc2]
      _ = ⟪scalarEigenFunctionLp g i, heatSemigroup (I := I) (M := M) g t v⟫_ℝ := by
              have hcv : ⟪scalarEigenFunctionLp g i, v⟫_ℝ =
                  ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g), U⟫_ℝ := by
                rw [hφ]
                dsimp [v]
                exact (hadj (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) (L U)).trans
                  (by simp [L])
              rw [← hcv]
              have hself := heatSemigroup_isSelfAdjoint (I := I) (M := M) g ht
              have hsymm := IsSelfAdjoint.isSymmetric hself
              have hadj' : ⟪scalarEigenFunctionLp g i, heatSemigroup (I := I) (M := M) g t v⟫_ℝ =
                  ⟪heatSemigroup (I := I) (M := M) g t (scalarEigenFunctionLp g i), v⟫_ℝ := by
                exact (hsymm (scalarEigenFunctionLp g i) v).symm
              rw [hadj']
              rw [heatSemigroup_apply_scalarEigenFunctionLp (I := I) (M := M) g i ht]
              simp [real_inner_smul_left]
  have hw1 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, L (tensorHeatSemigroup g 0 0 t U)⟫_ℝ •
        scalarEigenFunctionLp g i) (L (tensorHeatSemigroup g 0 0 t U)) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g (L (tensorHeatSemigroup g 0 0 t U))
  have hw2 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, heatSemigroup (I := I) (M := M) g t v⟫_ℝ •
        scalarEigenFunctionLp g i) (heatSemigroup (I := I) (M := M) g t v) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g (heatSemigroup (I := I) (M := M) g t v)
  have hsame : (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, L (tensorHeatSemigroup g 0 0 t U)⟫_ℝ •
        scalarEigenFunctionLp g i) =
      (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, heatSemigroup (I := I) (M := M) g t v⟫_ℝ •
        scalarEigenFunctionLp g i) := by
    funext i
    rw [hcoeff i]
  exact hw1.unique (by simpa [hsame] using hw2)

theorem scalarHeatCoeff_iteratedDeriv
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      (-TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
  let lam : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  let d : ℝ := tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i
  have hfun : (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) =
      fun s : ℝ => Real.exp ((-lam) * s) * d := by
    funext s
    rfl
  have hmain : iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      (-lam) ^ j * (Real.exp ((-lam) * t) * d) := by
    rw [hfun]
    rw [iteratedDeriv_mul_const_field]
    rw [iteratedDeriv_exp_const_mul]
    ring
  simpa [scalarHeatCoeff] using hmain

theorem scalarHeatCoeff_deriv
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) :
    deriv (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
  have h1 : deriv (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      iteratedDeriv 1 (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t :=
    congrFun (iteratedDeriv_one (f := fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)).symm t
  have h2 : iteratedDeriv 1 (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
      -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t := by
    simpa using scalarHeatCoeff_iteratedDeriv (I := I) (M := M) g u₀ i t 1
  exact h1.trans h2

theorem scalarHeatCoeff_hasDerivAt
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
      (-TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t) t := by
  have hcd : ContDiff ℝ ∞ (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) := by
    dsimp [scalarHeatCoeff]
    exact (Real.contDiff_exp.comp
      ((contDiff_const.mul contDiff_id) : ContDiff ℝ ∞
        (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i * s))).mul
      contDiff_const
  exact ((hcd.differentiable (by norm_num) t).hasDerivAt).congr_deriv
    (scalarHeatCoeff_deriv (I := I) (M := M) g u₀ i t)

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_mul_exp_neg_bddAbove (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-x) ≤ M := by
  classical
  let f : ℝ → ℝ := fun x => x ^ n * Real.exp (-x)
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hzero : Tendsto f atTop (𝓝 0) := by
    dsimp [f]
    exact Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hev : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ x → f x ≤ 1 := by
    have h := (hzero.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one))
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h
    have hR0 : 0 ≤ max R 0 := le_max_right _ _
    refine ⟨max R 0, hR0, ?_⟩
    intro x hx
    have hxR : R ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : 0 ≤ x := le_trans hR0 hx
    have hdist : |f x - 0| < 1 := hR x hxR
    have hnonneg : 0 ≤ f x := by
      dsimp [f]
      exact mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le
    have hlt : f x < 1 := (abs_lt.mp (by simpa using hdist)).2
    exact hlt.le
  obtain ⟨R, hR0, hR⟩ := hev
  let K : Set ℝ := Set.Icc 0 R
  have hK : IsCompact K := isCompact_Icc
  have hKbdd : BddAbove (f '' K) := by
    exact (hK.image hcont).bddAbove
  obtain ⟨M₁, hM₁⟩ := hKbdd
  refine ⟨max M₁ 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro x hx0
  by_cases hxR : x ≤ R
  · have hxK : x ∈ K := ⟨hx0, hxR⟩
    have hy : f x ∈ f '' K := ⟨x, hxK, rfl⟩
    exact le_trans (hM₁ hy) (le_max_left _ _)
  · have hRx : R ≤ x := le_of_not_ge hxR
    exact le_trans (hR x hRx) (le_max_right _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-(2 * a * x)) ≤ M := by
  classical
  obtain ⟨M₀, hM₀, hbdd⟩ := exists_pow_mul_exp_neg_bddAbove n
  have h2a : 0 < 2 * a := mul_pos zero_lt_two ha
  refine ⟨((2 * a) ^ n)⁻¹ * M₀, mul_nonneg (inv_nonneg.mpr (pow_nonneg h2a.le _)) hM₀, ?_⟩
  intro x hx0
  have hy : 0 ≤ 2 * a * x := mul_nonneg h2a.le hx0
  have hb := hbdd (2 * a * x) hy
  have hne : (2 * a) ^ n ≠ 0 := pow_ne_zero _ h2a.ne'
  calc
    x ^ n * Real.exp (-(2 * a * x))
        = ((2 * a) ^ n)⁻¹ * ((2 * a * x) ^ n * Real.exp (-(2 * a * x))) := by
          rw [show (2 * a * x) ^ n = (2 * a) ^ n * x ^ n by ring]
          field_simp [hne]
    _ ≤ ((2 * a) ^ n)⁻¹ * M₀ := by
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg h2a.le _))

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pow_add_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ M := by
  classical
  obtain ⟨M₀, hM₀, hbdd⟩ := exists_pow_mul_exp_neg_mul_bddAbove a ha n
  refine ⟨max ((2 ^ n : ℝ) * M₀) (2 ^ n),
    le_trans (mul_nonneg (by positivity) hM₀) (le_max_left _ _), ?_⟩
  intro x hx0
  by_cases hx1 : x ≤ 1
  · have hle : (1 + x) ^ n ≤ 2 ^ n := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) n
    calc
      (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ 2 ^ n * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ 2 ^ n := by
        rw [mul_comm]
        exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith))
      _ ≤ max ((2 ^ n : ℝ) * M₀) (2 ^ n) := le_max_right _ _
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    have hle : (1 + x) ^ n ≤ (2 * x) ^ n := by
      exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) n
    calc
      (1 + x) ^ n * Real.exp (-(2 * a * x)) ≤ (2 * x) ^ n * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ (2 ^ n : ℝ) * M₀ := by
        have h := hbdd x hx0
        have hm : 0 ≤ (2 ^ n : ℝ) := pow_nonneg (by norm_num) n
        calc
          (2 * x) ^ n * Real.exp (-(2 * a * x))
              = (2 ^ n : ℝ) * (x ^ n * Real.exp (-(2 * a * x))) := by
                rw [show (2 * x) ^ n = (2 ^ n : ℝ) * x ^ n by ring]
                ring
          _ ≤ (2 ^ n : ℝ) * M₀ := mul_le_mul_of_nonneg_left h hm
      _ ≤ max ((2 ^ n : ℝ) * M₀) (2 ^ n) := le_max_left _ _

lemma scalarHeatCoeff_deriv_sq
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (t : ℝ) (j : ℕ) :
    (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 =
      TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i) ^ 2 := by
  classical
  set lam : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  set d : ℝ := tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) u₀ i
  have hfun : (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) =
      fun s : ℝ => Real.exp ((-lam) * s) * d := by
    funext s
    rfl
  have hpow : ((-lam) ^ j) ^ 2 = lam ^ (2 * j) := by
    rw [show ((-lam) ^ j) ^ 2 = (-lam) ^ (2 * j) by
      rw [← pow_mul]
      ring_nf]
    rw [show (-lam) ^ (2 * j) = ((-lam) ^ 2) ^ j by
      rw [pow_mul]]
    rw [neg_sq]
    rw [← pow_mul]
  have hmain :
      (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 =
        lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2 := by
    rw [hfun]
    rw [iteratedDeriv_mul_const_field]
    rw [iteratedDeriv_exp_const_mul]
    change ((-lam) ^ j * Real.exp ((-lam) * t) * d) ^ 2 =
        lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2
    have hexp : (Real.exp ((-lam) * t)) ^ 2 = Real.exp (-(2 * lam * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      ((-lam) ^ j * Real.exp ((-lam) * t) * d) ^ 2
          = ((-lam) ^ j) ^ 2 * (Real.exp ((-lam) * t)) ^ 2 * d ^ 2 := by
              rw [mul_pow, mul_pow]
      _ = lam ^ (2 * j) * (Real.exp ((-lam) * t)) ^ 2 * d ^ 2 := by
              rw [hpow]
      _ = lam ^ (2 * j) * Real.exp (-(2 * lam * t)) * d ^ 2 := by
              rw [hexp]
  simp [hmain]

lemma scalarHeatCoeff_weighted_deriv_sq_le
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    {a : ℝ} (ha : 0 < a) (j m : ℕ) :
    ∃ C : TensorEigenIdx00 g → ℝ, Summable C ∧
      ∀ i t, t ∈ Set.Icc a b →
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 ≤
          C i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let N : ℕ := m + 2 * j
  obtain ⟨CM, hCM0, hbdd⟩ := exists_pow_add_mul_exp_neg_mul_bddAbove a ha N
  refine ⟨fun i => CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2, ?_, ?_⟩
  · exact Summable.mul_left CM (tensorL2Coeff_summable_sq hc u₀)
  · intro i t ht
    have hlam0 : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have ht_le : a ≤ t := (Set.mem_Icc.mp ht).1
    have hexp : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hb := hbdd (TensorEigenIdx.lambda (I := I) (M := M) i) hlam0
    have hbase_pos : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [hlam0]
    have hb2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) *
          Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) ≤ CM := by
      simpa [Real.rpow_natCast] using hb
    have hle0 : TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) ≤
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) := by
      exact pow_le_pow_left₀ hlam0 (by linarith) (2 * j)
    have hw : tensorSobolevWeight (I := I) (M := M) i (m : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) := rfl
    have hprod :
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) := by
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) (2 * j)]
      rw [← Real.rpow_add hbase_pos]
      congr 1
      norm_num [N]
    have hd2 : 0 ≤ (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := sq_nonneg _
    have hw0 : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ)
    have hexp_arg : -(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a) =
        -(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i) := by ring
    have hmain :
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
              Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) ≤
          CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
      calc
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
              Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2)
            ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
              have h1 :
                  TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 ≤
                    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hle0 (Real.exp_pos _).le) hd2
              exact mul_le_mul_of_nonneg_left h1 hw0
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
              have h02 : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                  (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by positivity
              have hleq :
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                    Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                    (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 ≤
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                    Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                    (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
                calc
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2
                      = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                            (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by ring
                  _ ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                            (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right hexp hd2) (by positivity)
                  _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) *
                          Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                          (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by ring
              exact mul_le_mul_of_nonneg_left hleq hw0
        _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) *
              Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
              (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              rw [hw]
              have hx :
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
                    (((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j)) *
                      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) =
                  ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (m : ℝ) *
                    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j)) *
                    (Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) *
                      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by ring
              rw [hx, hprod]
              have heqexp : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * a)) =
                  Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) := by
                rw [hexp_arg]
              rw [heqexp]
              ring_nf
        _ ≤ CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              exact mul_le_mul_of_nonneg_right hb2 hd2
    calc
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
              (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
                Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2) := by
            rw [scalarHeatCoeff_deriv_sq]
      _ ≤ CM * (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2 := by
              exact hmain
theorem scalarHeatCoeff_contDiff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (i : TensorEigenIdx00 g) (N : ℕ∞) :
    ContDiff ℝ N (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) := by
  have hlin : ContDiff ℝ N
      (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i * s) :=
    contDiff_const.mul contDiff_id
  have hexp : ContDiff ℝ N
      (fun s : ℝ => Real.exp (-TensorEigenIdx.lambda (I := I) (M := M) i * s)) :=
    Real.contDiff_exp.comp hlin
  dsimp [scalarHeatCoeff]
  exact hexp.mul contDiff_const

theorem scalarHeatFlow_contMDiffOn
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (N : ℕ)
      (fun q : ℝ × M => scalarHeatFlow g u₀ q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  simpa using (scalar_path_recon (I := I) (M := M) g htail hab N
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
    (U := Set.univ) (by exact isOpen_univ) (by intro t ht; trivial)
    (fun i => (scalarHeatCoeff_contDiff (I := I) (M := M) g u₀ i (N : ℕ∞)).contDiffOn)
    (fun j hj m => scalarHeatCoeff_weighted_deriv_sq_le (I := I) (M := M) g u₀ ha j m))

theorem scalarHeatFlow_contMDiffOn_top
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlow g u₀ q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  rw [contMDiffOn_infty]
  intro n
  exact scalarHeatFlow_contMDiffOn (I := I) (M := M) g u₀ htail hab ha n

lemma eigenvectorSmooth_hs_norm
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (i : TensorEigenIdx00 g) :
    ‖ccTensorToHs (I := I) (M := M) g 0 σ (eigenvectorSmooth g 0 0 i)‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
  classical
  have hsq : ‖ccTensorToHs (I := I) (M := M) g 0 σ (eigenvectorSmooth g 0 0 i)‖ ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ := by
    rw [tensorHs.norm_sq_eq_tsum]
    have hcoeff (j : TensorEigenIdx00 g) :
        (ccTensorToHs (I := I) (M := M) g 0 σ (eigenvectorSmooth g 0 0 i)).coeff j =
          if j = i then (1 : ℝ) else 0 := by
      rw [ccTensorToHs_coeff]
      exact tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
    rw [show (fun j : TensorEigenIdx00 g =>
          tensorSobolevWeight (I := I) (M := M) j σ *
            ((ccTensorToHs (I := I) (M := M) g 0 σ (eigenvectorSmooth g 0 0 i)).coeff j) ^ 2) =
        (fun j => if j = i then tensorSobolevWeight (I := I) (M := M) i σ else 0) by
      funext j
      rw [hcoeff j]
      by_cases hji : j = i
      · simp [hji]
      · simp [hji]]
    rw [tsum_ite_eq]
  rw [← hsq]
  rw [Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (norm_nonneg _)).symm

theorem scalarEigenFunction_abs_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx00 g) (x : M),
      |(scalarEigenFunction g i).toFun x| ≤
        C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
          (((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) / 2) := by
  classical
  set σ : ℝ := ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)
  obtain ⟨C, hC, hb⟩ := scalar0_abs_le_hs (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro i x
  have h1 := hb (eigenvectorSmooth g 0 0 i) x
  have hφ : (scalarEigenFunction g i).toFun x =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (eigenvectorSmooth g 0 0 i).toSection x := rfl
  have hnorm := eigenvectorSmooth_hs_norm (I := I) (M := M) g σ i
  rw [hnorm] at h1
  have hsqrt : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) := by
    unfold tensorSobolevWeight
    have hnonneg : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [tensor_lambda_nonneg (I := I) (M := M) i]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hnonneg]
    congr 1
    ring
  rw [hsqrt] at h1
  simpa [hφ] using h1

omit [NeZero (Module.finrank ℝ E)] in
lemma exp_sq_eq (a : ℝ) : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
  rw [← Real.exp_nat_mul a 2]
  congr 1

omit [NeZero (Module.finrank ℝ E)] in
lemma rpow_sq_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (2 * y) := by
  rw [← Real.rpow_natCast (x ^ y) 2]
  exact (Real.rpow_mul hx y (2 : ℝ)).symm.trans (by
    congr 1
    ring)

theorem scalarHeatFlow_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => scalarHeatFlow g u₀ t x) := by
  classical
  let a' : ℝ := a / 2
  let b' : ℝ := b + 1
  have ha' : 0 < a' := by
    dsimp [a']
    positivity
  have hab' : a' < b' := by
    dsimp [a', b']
    linarith
  have ht_int : t ∈ Set.Ioo a' b' := by
    have ht1 : a ≤ t := (Set.mem_Icc.mp ht).1
    have ht2 : t ≤ b := (Set.mem_Icc.mp ht).2
    dsimp [a', b']
    constructor <;> linarith
  have hjoint := scalarHeatFlow_contMDiffOn_top (I := I) (M := M) g u₀ htail hab' ha'
  have hjoint' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlow g u₀ q.1 q.2)
      (Set.Ioo a' b' ×ˢ Set.univ) :=
    hjoint.mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  intro x
  have hq : (t, x) ∈ interior (Set.Ioo a' b' ×ˢ Set.univ) := by
    rw [(isOpen_Ioo.prod isOpen_univ).interior_eq]
    exact ⟨ht_int, Set.mem_univ x⟩
  have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlow g u₀ q.1 q.2) (t, x) :=
    hjoint'.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht_int, Set.mem_univ x⟩)
  have hslice_map : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) x := by
    exact ContMDiffAt.prodMk (contMDiffAt_const (c := t) (x := x)) (contMDiffAt_id (x := x))
  exact ContMDiffAt.comp (x := x)
    (f := fun y : M => (t, y))
    (g := fun q : ℝ × M => scalarHeatFlow g u₀ q.1 q.2)
    (hg := hat) (hf := hslice_map)

noncomputable def scalarHeatFlowSlice
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : SmoothScalar g :=
  ⟨fun x => scalarHeatFlow g u₀ t x,
    scalarHeatFlow_slice_contMDiff (I := I) (M := M) g u₀ htail hab ha ht⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma nat_add_neg_self (N q : ℕ) : (((N + q : ℕ) : ℝ) + (-(q : ℝ))) = (N : ℝ) := by
  push_cast
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma summable_exp_mul_pow
    (g : SmoothRiemannianMetric I M) (htail : EigenvalueTailSummable g 0 0) (N : ℕ)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Summable (fun i : TensorEigenIdx00 g =>
      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N) := by
  classical
  obtain ⟨p, hp, htail_s⟩ := htail
  set q : ℕ := Nat.ceil p
  have hp_le : p ≤ (q : ℝ) := by
    dsimp [q]
    exact_mod_cast Nat.le_ceil p
  have htail_q : Summable (fun i : TensorEigenIdx00 g =>
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (fun i => Real.rpow_nonneg
        (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (-(q : ℝ))) ?_ htail_s
    intro i
    exact Real.rpow_le_rpow_of_exponent_le
      (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (neg_le_neg hp_le)
  obtain ⟨C, hC0, hbdd⟩ := exists_pow_add_mul_exp_neg_mul_bddAbove a ha (N + q)
  have hnonneg : ∀ i : TensorEigenIdx00 g,
      0 ≤ Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N :=
    fun i => mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) N)
  have hle : ∀ i : TensorEigenIdx00 g,
      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N ≤
        C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) := by
    intro i
    have hlam0 : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hb := hbdd (TensorEigenIdx.lambda (I := I) (M := M) i) hlam0
    have hpos1 : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith
    have hexp_le : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤
        Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hpow : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N := by
      have hExp : (-(q : ℝ) + ((N + q : ℕ) : ℝ)) = (N : ℝ) := by
        push_cast
        ring
      calc
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) := by
          rw [mul_comm]
        _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
              (-(q : ℝ) + ((N + q : ℕ) : ℝ)) := by
          rw [← Real.rpow_add_natCast (ne_of_gt hpos1) (-(q : ℝ)) (N + q)]
        _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N : ℝ) := by
          rw [hExp]
        _ = (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N := by
          rw [Real.rpow_natCast]
    have hstep1 :
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N ≤
          Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N := by
      exact mul_le_mul_of_nonneg_right hexp_le (pow_nonneg (by linarith) N)
    have hstep2 :
        Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N =
          Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ))) := by
      rw [hpow]
    have hstep3 :
        Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i)) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ))) =
          ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
            Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i))) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) := by
      ring
    have hstep4 :
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (N + q) *
            Real.exp (-(2 * a * TensorEigenIdx.lambda (I := I) (M := M) i))) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hb
        (Real.rpow_nonneg (by linarith) (-(q : ℝ)))
    exact le_trans hstep1 (le_trans hstep2.le (le_trans hstep3.le hstep4))
  have hsum_maj : Summable (fun i : TensorEigenIdx00 g =>
      C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(q : ℝ))) :=
    htail_q.mul_left C
  exact Summable.of_norm_bounded hsum_maj (fun i => by
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (hnonneg i)]
      exact hle i)

end HeatEquation
end Analysis
end DifferentialGeometry

end
