import DifferentialGeometry.Analysis.Heat.Smoothing.SpectralBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ScalarWeyl
import DifferentialGeometry.Analysis.Heat.Semigroup.Mass
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Scalar.EigenIdx
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Comparison
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HeatPotentialStrong
import DifferentialGeometry.Analysis.Heat.Smoothing.MildSolution
import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYauHarnack

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

noncomputable def scalarHeatFlowTensor
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g) : ℝ → M → ℝ :=
  fun t x => scalarSpecSum (I := I) (M := M) g
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x

noncomputable def scalar0Cc
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) : SmoothScalar g :=
  ⟨TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection,
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection⟩

private noncomputable def scalar0CcLinear
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

noncomputable def scalarHeatFlow
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : ℝ → M → ℝ :=
  scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm u₀)

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
  exact hw1.unique (by
    rw [hsame]
    exact hw2)

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
private lemma exists_pow_mul_exp_neg_bddAbove (n : ℕ) :
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
private lemma exists_pow_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
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
private lemma exists_pow_add_mul_exp_neg_mul_bddAbove (a : ℝ) (ha : 0 < a) (n : ℕ) :
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

private lemma scalarHeatCoeff_deriv_sq
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

private lemma scalarHeatCoeff_weighted_deriv_sq_le
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    {a b : ℝ} (ha : 0 < a) (j m : ℕ) :
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

theorem scalarHeatFlowTensor_contMDiffOn
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (N : ℕ)
      (fun q : ℝ × M => scalarHeatFlowTensor g u₀ q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  simpa using (scalar_path_recon (I := I) (M := M) g htail hab N
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
    (U := Set.univ) (by exact isOpen_univ) (by intro t ht; trivial)
    (fun i => (scalarHeatCoeff_contDiff (I := I) (M := M) g u₀ i (N : ℕ∞)).contDiffOn)
    (fun j hj m => scalarHeatCoeff_weighted_deriv_sq_le (I := I) (M := M) g u₀ ha j m))

theorem scalarHeatFlowTensor_contMDiffOn_top
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlowTensor g u₀ q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  rw [contMDiffOn_infty]
  intro n
  exact scalarHeatFlowTensor_contMDiffOn (I := I) (M := M) g u₀ htail hab ha n

private lemma eigenvectorSmooth_hs_norm
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
private lemma exp_sq_eq (a : ℝ) : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
  rw [← Real.exp_nat_mul a 2]
  congr 1

omit [NeZero (Module.finrank ℝ E)] in
private lemma rpow_sq_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (2 * y) := by
  rw [← Real.rpow_natCast (x ^ y) 2]
  exact (Real.rpow_mul hx y (2 : ℝ)).symm.trans (by
    congr 1
    ring)

theorem scalarHeatFlowTensor_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => scalarHeatFlowTensor g u₀ t x) := by
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
  have hjoint := scalarHeatFlowTensor_contMDiffOn_top (I := I) (M := M) g u₀ htail hab' ha'
  have hjoint' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlowTensor g u₀ q.1 q.2)
      (Set.Ioo a' b' ×ˢ Set.univ) :=
    hjoint.mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  intro x
  have hq : (t, x) ∈ interior (Set.Ioo a' b' ×ˢ Set.univ) := by
    rw [(isOpen_Ioo.prod isOpen_univ).interior_eq]
    exact ⟨ht_int, Set.mem_univ x⟩
  have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlowTensor g u₀ q.1 q.2) (t, x) :=
    hjoint'.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht_int, Set.mem_univ x⟩)
  have hslice_map : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) x := by
    exact ContMDiffAt.prodMk (contMDiffAt_const (c := t) (x := x)) (contMDiffAt_id (x := x))
  exact ContMDiffAt.comp (x := x)
    (f := fun y : M => (t, y))
    (g := fun q : ℝ × M => scalarHeatFlowTensor g u₀ q.1 q.2)
    (hg := hat) (hf := hslice_map)

noncomputable def scalarHeatFlowSliceTensor
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : SmoothScalar g :=
  ⟨fun x => scalarHeatFlowTensor g u₀ t x,
    scalarHeatFlowTensor_slice_contMDiff (I := I) (M := M) g u₀ htail hab ha ht⟩

noncomputable def scalarHeatFlowSlice
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : SmoothScalar g :=
  scalarHeatFlowSliceTensor g ((tensor00ScalarL2Equiv g).symm u₀)
    (scalar_eigen_tail (I := I) (M := M) g) hab ha ht

omit [NeZero (Module.finrank ℝ E)] in
private lemma nat_add_neg_self (N q : ℕ) : (((N + q : ℕ) : ℝ) + (-(q : ℝ))) = (N : ℝ) := by
  push_cast
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma summable_exp_mul_pow
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

private lemma summable_abs_scalarHeatCoeff_mul_hsWeight
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Summable (fun i : TensorEigenIdx00 g =>
      |scalarHeatCoeff (I := I) (M := M) g u₀ i t| *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
          (((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) / 2)) := by
  classical
  let N₀ : ℕ := Module.finrank ℝ E / 2 + 1
  let σ : ℝ := (N₀ : ℝ)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let d : TensorEigenIdx00 g → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M) hc u₀ i
  let w : TensorEigenIdx00 g → ℝ := fun i =>
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)
  have hw2_sq (i : TensorEigenIdx00 g) : (w i) ^ 2 =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ := by
    dsimp [w]
    rw [rpow_sq_eq (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)]
    congr 1
    ring
  have hd2 : Summable (fun i : TensorEigenIdx00 g => (d i) ^ 2) := by
    change Summable (fun i : TensorEigenIdx00 g =>
      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2)
    exact tensorL2Coeff_summable_sq (I := I) (M := M) hc u₀
  have hw2 : Summable (fun i : TensorEigenIdx00 g =>
      Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) * (w i) ^ 2) := by
    have hsum := summable_exp_mul_pow (I := I) (M := M) g htail N₀ ha hat
    exact Summable.congr hsum (fun i => by
      rw [hw2_sq i]
      congr 1
      dsimp [σ]
      rw [Real.rpow_natCast])
  have hsum2 : Summable (fun i : TensorEigenIdx00 g =>
      ((d i) ^ 2 + Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
        (w i) ^ 2) / 2) :=
    (hd2.add hw2).div_const 2
  have hAMGM (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hc_abs (i : TensorEigenIdx00 g) :
      |scalarHeatCoeff (I := I) (M := M) g u₀ i t| =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * |d i| := by
    unfold scalarHeatCoeff
    rw [abs_mul]
    rw [abs_of_nonneg (Real.exp_pos _).le]
  have hmain (i : TensorEigenIdx00 g) :
      |scalarHeatCoeff (I := I) (M := M) g u₀ i t| * w i ≤
        ((d i) ^ 2 + Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
          (w i) ^ 2) / 2 := by
    calc
      |scalarHeatCoeff (I := I) (M := M) g u₀ i t| * w i
          = (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * |d i|) * w i := by
            rw [hc_abs]
      _ = |d i| * (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * w i) := by
            ring
      _ ≤ (|d i| ^ 2 +
            (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * w i) ^ 2) / 2 := by
            exact hAMGM |d i| (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * w i)
      _ = ((d i) ^ 2 + Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
            (w i) ^ 2) / 2 := by
            congr 1
            rw [sq_abs]
            rw [mul_pow, exp_sq_eq]
            congr 1
            ring_nf
  exact Summable.of_nonneg_of_le
    (fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg
      (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)))
    hmain hsum2

theorem scalarHeatCoeff_eq_inner_slice
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (j : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g j,
        smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht)⟫_ℝ =
      scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
  classical
  let c : TensorEigenIdx00 g → ℝ := fun i => scalarHeatCoeff (I := I) (M := M) g u₀ i t
  let σ : ℝ := ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)
  let slice : SmoothScalar g := scalarHeatFlowSliceTensor g u₀ htail hab ha ht
  let φj : SmoothScalar g := scalarEigenFunction g j
  set μ := riemannianVolumeMeasure (I := I) (M := M) g
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hslice (x : M) : slice.toFun x =
      ∑' i : TensorEigenIdx00 g, c i * (scalarEigenFunction g i).toFun x := by
    dsimp [slice, scalarHeatFlowSliceTensor, scalarHeatFlowTensor, c]
    unfold scalarSpecSum
    rfl
  let F : TensorEigenIdx00 g → M → ℝ := fun i x =>
    c i * (φj.toFun x * (scalarEigenFunction g i).toFun x)
  have hF_cont (i : TensorEigenIdx00 g) : Continuous (F i) := by
    dsimp [F]
    exact continuous_const.mul (φj.smooth.continuous.mul
      (scalarEigenFunction g i).smooth.continuous)
  have hF_int (i : TensorEigenIdx00 g) : Integrable (F i) μ := by
    exact Continuous.integrable_of_hasCompactSupport (hF_cont i)
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C0, hC0, hφbdd⟩ := scalarEigenFunction_abs_le (I := I) (M := M) g
  have hw_nonneg (i : TensorEigenIdx00 g) :
      0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) :=
    Real.rpow_nonneg (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)
  have hCj : 0 ≤ C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2) :=
    mul_nonneg hC0 (hw_nonneg j)
  have hpt (i : TensorEigenIdx00 g) (x : M) :
      ‖F i x‖ ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
        (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by
    dsimp [F]
    calc
      |c i * (φj.toFun x * (scalarEigenFunction g i).toFun x)|
          = |c i| * |φj.toFun x| * |(scalarEigenFunction g i).toFun x| := by
            rw [abs_mul, abs_mul]
            ring
      _ ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
            (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by
            exact mul_le_mul
              (mul_le_mul (le_rfl) (hφbdd j x) (abs_nonneg _) (abs_nonneg _))
              (hφbdd i x) (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) hCj)
  have hconst_int (i : TensorEigenIdx00 g) :
      ∫ x : M, |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) ∂μ =
        |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
          (μ Set.univ).toReal := by
    rw [MeasureTheory.integral_const]
    simp [Measure.real, smul_eq_mul]
    ring
  have hinteg_bdd (i : TensorEigenIdx00 g) :
      ∫ x : M, ‖F i x‖ ∂μ ≤
        |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
          (μ Set.univ).toReal := by
    calc
      ∫ x : M, ‖F i x‖ ∂μ
          ≤ ∫ x : M, |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
              (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) ∂μ := by
            exact MeasureTheory.integral_mono (hF_int i).norm (integrable_const _)
              (fun x => hpt i x)
      _ = |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
            (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
            (μ Set.univ).toReal := hconst_int i
  have hsum_norm : Summable (fun i : TensorEigenIdx00 g =>
      ∫ x : M, ‖F i x‖ ∂μ) := by
    let K : ℝ := C0 * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
      (μ Set.univ).toReal
    let B : TensorEigenIdx00 g → ℝ := fun i =>
      K * (|c i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2))
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hB0 : ∀ i : TensorEigenIdx00 g, 0 ≤ B i := by
      intro i
      dsimp [B]
      exact mul_nonneg hK (mul_nonneg (abs_nonneg _) (hw_nonneg i))
    have hle : ∀ i : TensorEigenIdx00 g, ∫ x : M, ‖F i x‖ ∂μ ≤ B i := by
      intro i
      calc
        ∫ x : M, ‖F i x‖ ∂μ
            ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
                (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
                (μ Set.univ).toReal := hinteg_bdd i
        _ = B i := by
              dsimp [B, K]
              ring
    have hBsum : Summable B := by
      have hS := summable_abs_scalarHeatCoeff_mul_hsWeight (I := I) (M := M) g u₀ htail ha
          (Set.mem_Icc.mp ht).1
      exact Summable.mul_left K (by
        change Summable (fun i : TensorEigenIdx00 g =>
          |scalarHeatCoeff (I := I) (M := M) g u₀ i t| *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2))
        exact hS)
    have hg0 : ∀ i : TensorEigenIdx00 g, 0 ≤ ∫ x : M, ‖F i x‖ ∂μ := by
      intro i
      exact MeasureTheory.integral_nonneg (fun x => norm_nonneg (F i x))
    exact Summable.of_nonneg_of_le hg0 hle hBsum
  have hinter :
      (∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ) =
        ∫ x : M, (∑' i : TensorEigenIdx00 g, F i x) ∂μ :=
    by
    haveI : Countable (TensorEigenIdx00 g) :=
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
        (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    exact MeasureTheory.integral_tsum_of_summable_integral_norm (F := F) hF_int hsum_norm
  have horth (i : TensorEigenIdx00 g) :
      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ =
        if i = j then (1 : ℝ) else 0 := by
    calc
      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ
          = ⟪scalarEigenFunctionLp g j, scalarEigenFunctionLp g i⟫_ℝ := by
            rw [← smoothToLp_inner_eq_integral_mul (I := I) (M := M) g φj
              (scalarEigenFunction g i)]
            rfl
      _ = ⟪(eigenvectorSmooth g 0 0 j : TensorL2 0 0 g),
            (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)⟫_ℝ := by
            rw [scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g j,
              scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i]
            have h := (tensor00ScalarL2Equiv g).toLinearIsometry.inner_map_map
              (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
              (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)
            exact h
      _ = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
            ((eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)) j := by
            rw [tensorL2Coeff_eq_inner]
            congr 1
            exact eigenvectorSmooth00_eq_basis (I := I) (M := M) g j
      _ = if i = j then (1 : ℝ) else 0 := by
            simpa [eq_comm] using tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
  have hmain : ∫ x : M, φj.toFun x * slice.toFun x ∂μ = c j := by
    calc
      ∫ x : M, φj.toFun x * slice.toFun x ∂μ
          = ∫ x : M, φj.toFun x *
              (∑' i : TensorEigenIdx00 g, c i * (scalarEigenFunction g i).toFun x) ∂μ := by
            apply congrArg (MeasureTheory.integral (μ := μ))
            funext x
            rw [hslice x]
      _ = ∫ x : M, (∑' i : TensorEigenIdx00 g, F i x) ∂μ := by
            congr 1
            funext x
            dsimp [F]
            rw [← tsum_mul_left]
            apply tsum_congr
            intro i
            ring
      _ = ∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ := hinter.symm
      _ = c j := by
            calc
              (∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ)
                  = ∑' i : TensorEigenIdx00 g, c i *
                      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ := by
                    apply tsum_congr
                    intro i
                    dsimp [F]
                    rw [MeasureTheory.integral_const_mul]
              _ = ∑' i : TensorEigenIdx00 g, c i * (if i = j then (1 : ℝ) else 0) := by
                    apply tsum_congr
                    intro i
                    rw [horth i]
              _ = c j := by
                    rw [show (fun i : TensorEigenIdx00 g =>
                        c i * (if i = j then (1 : ℝ) else 0)) =
                      fun i : TensorEigenIdx00 g => if i = j then c j else (0 : ℝ) by
                      funext i
                      by_cases hij : i = j
                      · subst hij
                        simp
                      · simp [hij]]
                    exact tsum_ite_eq j (fun _ => c j)
  calc
    ⟪scalarEigenFunctionLp g j,
        smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht)⟫_ℝ
        = ∫ x : M, φj.toFun x * slice.toFun x ∂μ := by
          rw [← smoothToLp_inner_eq_integral_mul (I := I) (M := M) g φj slice]
          rfl
    _ = c j := hmain
    _ = scalarHeatCoeff (I := I) (M := M) g u₀ j t := rfl

theorem scalarHeatCoeff_eq_inner_heatSemigroup
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    {t : ℝ} (ht : 0 ≤ t) (j : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g j,
        heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀)⟫_ℝ =
      scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
  classical
  set L := tensor00ScalarL2Equiv g
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  have hL : L (tensorHeatSemigroup g 0 0 t u₀) =
      heatSemigroup (I := I) (M := M) g t (L u₀) :=
    tensor00ScalarL2Equiv_tensorHeatSemigroup (I := I) (M := M) g ht u₀
  calc
    ⟪scalarEigenFunctionLp g j,
        heatSemigroup (I := I) (M := M) g t (L u₀)⟫_ℝ
        = ⟪L (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g),
            L (tensorHeatSemigroup g 0 0 t u₀)⟫_ℝ := by
          rw [scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g j]
          rw [← hL]
    _ = ⟪(eigenvectorSmooth g 0 0 j : TensorL2 0 0 g),
          tensorHeatSemigroup g 0 0 t u₀⟫_ℝ := by
          exact (tensor00ScalarL2Equiv g).toLinearIsometry.inner_map_map
            (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) (tensorHeatSemigroup g 0 0 t u₀)
    _ = tensorL2Coeff (I := I) (M := M) hc (tensorHeatSemigroup g 0 0 t u₀) j := by
          rw [tensorL2Coeff_eq_inner]
          congr 1
          exact eigenvectorSmooth00_eq_basis (I := I) (M := M) g j
    _ = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) *
          tensorL2Coeff (I := I) (M := M) hc u₀ j := by
          exact tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact
            (I := I) (M := M) g 0 0 ht u₀ j
    _ = scalarHeatCoeff (I := I) (M := M) g u₀ j t := rfl

theorem scalarHeatFlowSliceTensor_toL2_eq_heatSemigroup
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht) =
      heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀) := by
  classical
  have ht0 : 0 ≤ t := le_trans (le_of_lt ha) (Set.mem_Icc.mp ht).1
  have hw1 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht)⟫_ℝ •
        scalarEigenFunctionLp g i)
      (smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht)) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht))
  have hw2 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀)⟫_ℝ •
        scalarEigenFunctionLp g i)
      (heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀)) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g
      (heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀))
  have hsame : (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          smoothToLp (I := I) (M := M) g (scalarHeatFlowSliceTensor g u₀ htail hab ha ht)⟫_ℝ •
        scalarEigenFunctionLp g i) =
      (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀)⟫_ℝ •
        scalarEigenFunctionLp g i) := by
    funext i
    rw [scalarHeatCoeff_eq_inner_slice (I := I) (M := M) g u₀ htail hab ha ht i,
      scalarHeatCoeff_eq_inner_heatSemigroup (I := I) (M := M) g u₀ ht0 i]
  exact hw1.unique (by
    rw [hsame]
    exact hw2)

theorem scalarHeatFlowTensor_hasDerivAt
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : M) :
    HasDerivAt (fun s : ℝ => scalarHeatFlowTensor g u₀ s x)
      (scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x) t := by
  classical
  have htIcc : t ∈ Set.Icc a b :=
    Set.mem_Icc.mpr ⟨(Set.mem_Ioo.mp ht).1.le, (Set.mem_Ioo.mp ht).2.le⟩
  have hU : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    exact lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1
  have hc (i : TensorEigenIdx00 g) :
      ContDiffOn ℝ (1 : ℕ) (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
        (Set.Ioi (0 : ℝ)) := by
    exact (scalarHeatCoeff_contDiff (I := I) (M := M) g u₀ i (1 : ℕ∞)).contDiffOn
  have hmass : ∀ j : ℕ, j ≤ 1 → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx00 g → ℝ, Summable Cm ∧
        ∀ i t', t' ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t') ^ 2 ≤
              Cm i := by
    intro j hj m
    exact scalarHeatCoeff_weighted_deriv_sq_le (I := I) (M := M) g u₀ ha j m
  have hd1 := scalarSpec_d1 (I := I) (M := M) g htail hab
    (fun i s => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
    (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))) (U := Set.Ioi (0 : ℝ)) hU
    hc hmass x htIcc
  have hd1' : HasDerivWithinAt (fun s : ℝ => scalarHeatFlowTensor g u₀ s x)
      (scalarSpecSum (I := I) (M := M) g
        (fun i s => deriv (fun r : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i r) s) t x)
      (Set.Icc a b) t := by
    simpa [scalarHeatFlowTensor] using hd1
  have hderiv_sum :
      scalarSpecSum (I := I) (M := M) g
        (fun i s => deriv (fun r : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i r) s) t x =
      scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x := by
    unfold scalarSpecSum
    apply tsum_congr
    intro i
    congr 1
    exact scalarHeatCoeff_deriv (I := I) (M := M) g u₀ i t
  have hd2 : HasDerivWithinAt (fun s : ℝ => scalarHeatFlowTensor g u₀ s x)
      (scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x)
      (Set.Icc a b) t := by
    simpa [hderiv_sum] using hd1'
  exact hd2.hasDerivAt (Icc_mem_nhds (Set.mem_Ioo.mp ht).1 (Set.mem_Ioo.mp ht).2)

private lemma summable_abs_scalarHeatCoeff_lambda_mul_hsWeight
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Summable (fun i : TensorEigenIdx00 g =>
      |TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t| *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
          (((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) / 2)) := by
  classical
  let N₀ : ℕ := Module.finrank ℝ E / 2 + 1
  let σ : ℝ := (N₀ : ℝ)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let d : TensorEigenIdx00 g → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M) hc u₀ i
  let w : TensorEigenIdx00 g → ℝ := fun i =>
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)
  let A : TensorEigenIdx00 g → ℝ := fun i =>
    TensorEigenIdx.lambda (I := I) (M := M) i *
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) * |d i|
  let B : TensorEigenIdx00 g → ℝ := fun i =>
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) * w i
  have htpos : 0 < t := lt_of_lt_of_le ha hat
  have hhalf : 0 < t / 2 := half_pos htpos
  have hhat : t / 2 ≤ t := by linarith
  have hw2_sq (i : TensorEigenIdx00 g) : (w i) ^ 2 =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ := by
    dsimp [w]
    rw [rpow_sq_eq (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)]
    congr 1
    ring
  have hd2 : Summable (fun i : TensorEigenIdx00 g => (d i) ^ 2) := by
    change Summable (fun i : TensorEigenIdx00 g =>
      (tensorL2Coeff (I := I) (M := M) hc u₀ i) ^ 2)
    exact tensorL2Coeff_summable_sq (I := I) (M := M) hc u₀
  have hsumB2 : Summable (fun i : TensorEigenIdx00 g => (B i) ^ 2) := by
    have hsum := summable_exp_mul_pow (I := I) (M := M) g htail N₀ hhalf
      (le_rfl : t / 2 ≤ t / 2)
    exact Summable.congr hsum (fun i => by
      dsimp [B]
      calc
        Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * (t / 2))) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ N₀
            = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t)) *
                (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ := by
              congr 1
              · congr 1
                ring
              · dsimp [σ]
                rw [Real.rpow_natCast]
        _ = (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) * w i) ^ 2 := by
              rw [mul_pow, exp_sq_eq, hw2_sq i]
              congr 1
              · congr 1
                ring
              )
  obtain ⟨Md, hMd0, hlambdabdd⟩ := exists_pow_mul_exp_neg_mul_bddAbove (t / 2) hhalf 2
  have hlami2 (i : TensorEigenIdx00 g) :
      TensorEigenIdx.lambda (I := I) (M := M) i ^ 2 *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤ Md := by
    have h := hlambdabdd (TensorEigenIdx.lambda (I := I) (M := M) i)
      (tensor_lambda_nonneg (I := I) (M := M) i)
    calc
      TensorEigenIdx.lambda (I := I) (M := M) i ^ 2 *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t))
          = TensorEigenIdx.lambda (I := I) (M := M) i ^ 2 *
              Real.exp (-(2 * (t / 2) * TensorEigenIdx.lambda (I := I) (M := M) i)) := by
            congr 1
            congr 1
            ring
      _ ≤ Md := h
  have hsumA2 : Summable (fun i : TensorEigenIdx00 g => (A i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_ (hd2.mul_left Md)
    intro i
    calc
      (A i) ^ 2
          = TensorEigenIdx.lambda (I := I) (M := M) i ^ 2 *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t)) * (d i) ^ 2 := by
            dsimp [A]
            rw [mul_pow, mul_pow, sq_abs]
            rw [exp_sq_eq]
            congr 1
            ring_nf
      _ ≤ Md * (d i) ^ 2 := by
            exact mul_le_mul (hlami2 i) (le_rfl)
              (sq_nonneg _) hMd0
  have hAMGM (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hc_abs_lambda (i : TensorEigenIdx00 g) :
      |TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i t| =
        TensorEigenIdx.lambda (I := I) (M := M) i *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * |d i| := by
    unfold scalarHeatCoeff
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (tensor_lambda_nonneg (I := I) (M := M) i)]
    rw [abs_of_nonneg (Real.exp_pos _).le]
    dsimp [d]
    ring
  have hprod (i : TensorEigenIdx00 g) :
      |TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i t| * w i = A i * B i := by
    calc
      |TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i t| * w i
          = (TensorEigenIdx.lambda (I := I) (M := M) i *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * |d i|) * w i := by
            rw [hc_abs_lambda]
      _ = TensorEigenIdx.lambda (I := I) (M := M) i *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) * |d i| *
            (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) * w i) := by
            have hsplit : Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) =
                Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) *
                  Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i * t) / 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [hsplit]
            ring
      _ = A i * B i := rfl
  have hsum2 : Summable (fun i : TensorEigenIdx00 g =>
      ((A i) ^ 2 + (B i) ^ 2) / 2) :=
    (hsumA2.add hsumB2).div_const 2
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg
      (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)))
    ?_ hsum2
  intro i
  calc
    |TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i t| * w i
        = A i * B i := hprod i
    _ ≤ ((A i) ^ 2 + (B i) ^ 2) / 2 := hAMGM (A i) (B i)
    _ = ((A i) ^ 2 + (B i) ^ 2) / 2 := rfl

theorem scalarHeatFlowTensorTimeDeriv_contMDiffOn
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (N : ℕ)
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  classical
  have hU : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    exact lt_of_lt_of_le ha (Set.mem_Icc.mp hs).1
  have hc (i : TensorEigenIdx00 g) :
      ContDiffOn ℝ (N : ℕ) (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i s) (Set.Ioi (0 : ℝ)) := by
    exact (contDiff_const.mul
      (scalarHeatCoeff_contDiff (I := I) (M := M) g u₀ i (N : ℕ∞))).contDiffOn
  have hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx00 g → ℝ, Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i *
              scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 ≤ Cm i := by
    intro j hj m
    obtain ⟨Cm, hCm, hCm_le⟩ :=
      scalarHeatCoeff_weighted_deriv_sq_le (I := I) (M := M) g u₀ ha (j + 1) m
    refine ⟨Cm, hCm, ?_⟩
    intro i t ht'
    have hder :
        iteratedDeriv j (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i *
            scalarHeatCoeff (I := I) (M := M) g u₀ i s) t =
          -TensorEigenIdx.lambda (I := I) (M := M) i *
            iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t := by
      convert (iteratedDeriv_mul_const_field
          (f := fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s)
          (c := -TensorEigenIdx.lambda (I := I) (M := M) i) (n := j) (x := t)) using 1
      · ring_nf
      · ring_nf
    have h1 := scalarHeatCoeff_iteratedDeriv (I := I) (M := M) g u₀ i t j
    have h2 := scalarHeatCoeff_iteratedDeriv (I := I) (M := M) g u₀ i t (j + 1)
    calc
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (iteratedDeriv j (fun s : ℝ => -TensorEigenIdx.lambda (I := I) (M := M) i *
            scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
              (-TensorEigenIdx.lambda (I := I) (M := M) i *
                iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 := by
            rw [hder]
      _ = tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv (j + 1) (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g u₀ i s) t) ^ 2 := by
            congr 1
            rw [h1, h2]
            rw [pow_succ']
            ring_nf
      _ ≤ Cm i := hCm_le i t ht'
  simpa using (scalar_path_recon (I := I) (M := M) g htail hab N
    (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
      scalarHeatCoeff (I := I) (M := M) g u₀ i s)
    (U := Set.Ioi (0 : ℝ)) (by exact isOpen_Ioi) hU hc hmass)

theorem scalarHeatFlowTensorTimeDeriv_contMDiffOn_top
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) q.1 q.2)
      (Set.Icc a b ×ˢ Set.univ) := by
  rw [contMDiffOn_infty]
  intro n
  exact scalarHeatFlowTensorTimeDeriv_contMDiffOn (I := I) (M := M) g u₀ htail hab ha n

theorem scalarHeatFlowTensorTimeDeriv_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x) := by
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
  have hjoint := scalarHeatFlowTensorTimeDeriv_contMDiffOn_top (I := I) (M := M) g u₀ htail hab' ha'
  have hjoint' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) q.1 q.2)
      (Set.Ioo a' b' ×ˢ Set.univ) :=
    hjoint.mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  intro x
  have hq : (t, x) ∈ interior (Set.Ioo a' b' ×ˢ Set.univ) := by
    rw [(isOpen_Ioo.prod isOpen_univ).interior_eq]
    exact ⟨ht_int, Set.mem_univ x⟩
  have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) q.1 q.2) (t, x) :=
    hjoint'.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht_int, Set.mem_univ x⟩)
  have hslice_map : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) x := by
    exact ContMDiffAt.prodMk (contMDiffAt_const (c := t) (x := x)) (contMDiffAt_id (x := x))
  exact ContMDiffAt.comp (x := x)
    (f := fun y : M => (t, y))
    (g := fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g
      (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i s) q.1 q.2)
    (hg := hat) (hf := hslice_map)

noncomputable def scalarHeatFlowTimeDerivSliceTensor
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : SmoothScalar g :=
  ⟨fun x => scalarSpecSum (I := I) (M := M) g
      (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
        scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x,
    scalarHeatFlowTensorTimeDeriv_slice_contMDiff (I := I) (M := M) g u₀ htail hab ha ht⟩

theorem scalarHeatCoeff_lambda_eq_inner_slice
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (j : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g j,
        smoothToLp (I := I) (M := M) g
          (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht)⟫_ℝ =
      -TensorEigenIdx.lambda (I := I) (M := M) j *
        scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
  classical
  let c : TensorEigenIdx00 g → ℝ := fun i =>
    -(TensorEigenIdx.lambda (I := I) (M := M) i *
      scalarHeatCoeff (I := I) (M := M) g u₀ i t)
  let σ : ℝ := ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)
  let slice : SmoothScalar g :=
    scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht
  let φj : SmoothScalar g := scalarEigenFunction g j
  set μ := riemannianVolumeMeasure (I := I) (M := M) g
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hslice (x : M) : slice.toFun x =
      ∑' i : TensorEigenIdx00 g, c i * (scalarEigenFunction g i).toFun x := by
    dsimp [slice, c]
    unfold scalarHeatFlowTimeDerivSliceTensor scalarSpecSum
    apply tsum_congr
    intro i
    congr 1
    ring
  let F : TensorEigenIdx00 g → M → ℝ := fun i x =>
    c i * (φj.toFun x * (scalarEigenFunction g i).toFun x)
  have hF_cont (i : TensorEigenIdx00 g) : Continuous (F i) := by
    dsimp [F]
    exact continuous_const.mul (φj.smooth.continuous.mul
      (scalarEigenFunction g i).smooth.continuous)
  have hF_int (i : TensorEigenIdx00 g) : Integrable (F i) μ := by
    exact Continuous.integrable_of_hasCompactSupport (hF_cont i)
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C0, hC0, hφbdd⟩ := scalarEigenFunction_abs_le (I := I) (M := M) g
  have hw_nonneg (i : TensorEigenIdx00 g) :
      0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) :=
    Real.rpow_nonneg (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)
  have hCj : 0 ≤ C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2) :=
    mul_nonneg hC0 (hw_nonneg j)
  have hpt (i : TensorEigenIdx00 g) (x : M) :
      ‖F i x‖ ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
        (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by
    dsimp [F]
    calc
      |c i * (φj.toFun x * (scalarEigenFunction g i).toFun x)|
          = |c i| * |φj.toFun x| * |(scalarEigenFunction g i).toFun x| := by
            rw [abs_mul, abs_mul]
            ring
      _ ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
            (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by
            exact mul_le_mul
              (mul_le_mul (le_rfl) (hφbdd j x) (abs_nonneg _) (abs_nonneg _))
              (hφbdd i x) (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) hCj)
  have hconst_int (i : TensorEigenIdx00 g) :
      ∫ x : M, |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) ∂μ =
        |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
          (μ Set.univ).toReal := by
    rw [MeasureTheory.integral_const]
    simp [Measure.real, smul_eq_mul]
    ring
  have hinteg_bdd (i : TensorEigenIdx00 g) :
      ∫ x : M, ‖F i x‖ ∂μ ≤
        |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
          (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
          (μ Set.univ).toReal := by
    calc
      ∫ x : M, ‖F i x‖ ∂μ
          ≤ ∫ x : M, |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
              (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) ∂μ := by
            exact MeasureTheory.integral_mono (hF_int i).norm (integrable_const _)
              (fun x => hpt i x)
      _ = |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
            (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
            (μ Set.univ).toReal := hconst_int i
  have hsum_norm : Summable (fun i : TensorEigenIdx00 g =>
      ∫ x : M, ‖F i x‖ ∂μ) := by
    let K : ℝ := C0 * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
      (μ Set.univ).toReal
    let B : TensorEigenIdx00 g → ℝ := fun i =>
      K * (|c i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2))
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hB0 : ∀ i : TensorEigenIdx00 g, 0 ≤ B i := by
      intro i
      dsimp [B]
      exact mul_nonneg hK (mul_nonneg (abs_nonneg _) (hw_nonneg i))
    have hle : ∀ i : TensorEigenIdx00 g, ∫ x : M, ‖F i x‖ ∂μ ≤ B i := by
      intro i
      calc
        ∫ x : M, ‖F i x‖ ∂μ
            ≤ |c i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) j) ^ (σ / 2)) *
                (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) *
                (μ Set.univ).toReal := hinteg_bdd i
        _ = B i := by
              dsimp [B, K]
              ring
    have hBsum : Summable B := by
      have hS := summable_abs_scalarHeatCoeff_lambda_mul_hsWeight
        (I := I) (M := M) g u₀ htail ha (Set.mem_Icc.mp ht).1
      exact Summable.mul_left K (Summable.congr hS (fun i => by
        dsimp [c]
        rw [abs_neg]))
    have hg0 : ∀ i : TensorEigenIdx00 g, 0 ≤ ∫ x : M, ‖F i x‖ ∂μ := by
      intro i
      exact MeasureTheory.integral_nonneg (fun x => norm_nonneg (F i x))
    exact Summable.of_nonneg_of_le hg0 hle hBsum
  have hinter :
      (∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ) =
        ∫ x : M, (∑' i : TensorEigenIdx00 g, F i x) ∂μ :=
    by
    haveI : Countable (TensorEigenIdx00 g) :=
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
        (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    exact MeasureTheory.integral_tsum_of_summable_integral_norm (F := F) hF_int hsum_norm
  have horth (i : TensorEigenIdx00 g) :
      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ =
        if i = j then (1 : ℝ) else 0 := by
    calc
      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ
          = ⟪scalarEigenFunctionLp g j, scalarEigenFunctionLp g i⟫_ℝ := by
            rw [← smoothToLp_inner_eq_integral_mul (I := I) (M := M) g φj
              (scalarEigenFunction g i)]
            rfl
      _ = ⟪(eigenvectorSmooth g 0 0 j : TensorL2 0 0 g),
            (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)⟫_ℝ := by
            rw [scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g j,
              scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i]
            have h := (tensor00ScalarL2Equiv g).toLinearIsometry.inner_map_map
              (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
              (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)
            exact h
      _ = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
            ((eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)) j := by
            rw [tensorL2Coeff_eq_inner]
            congr 1
            exact eigenvectorSmooth00_eq_basis (I := I) (M := M) g j
      _ = if i = j then (1 : ℝ) else 0 := by
            simpa [eq_comm] using tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
  have hmain : ∫ x : M, φj.toFun x * slice.toFun x ∂μ = c j := by
    calc
      ∫ x : M, φj.toFun x * slice.toFun x ∂μ
          = ∫ x : M, φj.toFun x *
              (∑' i : TensorEigenIdx00 g, c i * (scalarEigenFunction g i).toFun x) ∂μ := by
            apply congrArg (MeasureTheory.integral (μ := μ))
            funext x
            rw [hslice x]
      _ = ∫ x : M, (∑' i : TensorEigenIdx00 g, F i x) ∂μ := by
            apply congrArg (MeasureTheory.integral (μ := μ))
            funext x
            dsimp [F]
            rw [← tsum_mul_left]
            apply tsum_congr
            intro i
            ring
      _ = ∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ := hinter.symm
      _ = c j := by
            calc
              (∑' i : TensorEigenIdx00 g, ∫ x : M, F i x ∂μ)
                  = ∑' i : TensorEigenIdx00 g, c i *
                      ∫ x : M, φj.toFun x * (scalarEigenFunction g i).toFun x ∂μ := by
                    apply tsum_congr
                    intro i
                    dsimp [F]
                    rw [MeasureTheory.integral_const_mul]
              _ = ∑' i : TensorEigenIdx00 g, c i * (if i = j then (1 : ℝ) else 0) := by
                    apply tsum_congr
                    intro i
                    rw [horth i]
              _ = c j := by
                    rw [show (fun i : TensorEigenIdx00 g =>
                        c i * (if i = j then (1 : ℝ) else 0)) =
                      fun i : TensorEigenIdx00 g => if i = j then c j else (0 : ℝ) by
                      funext i
                      by_cases hij : i = j
                      · subst hij
                        simp
                      · simp [hij]]
                    exact tsum_ite_eq j (fun _ => c j)
  calc
    ⟪scalarEigenFunctionLp g j,
        smoothToLp (I := I) (M := M) g
          (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht)⟫_ℝ
        = ∫ x : M, φj.toFun x * slice.toFun x ∂μ := by
          rw [← smoothToLp_inner_eq_integral_mul (I := I) (M := M) g φj slice]
          rfl
    _ = c j := hmain
    _ = -TensorEigenIdx.lambda (I := I) (M := M) j *
          scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
          dsimp [c]
          ring

theorem heatPower_one_inner_eq_lambda_coeff
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    {t : ℝ} (ht : 0 < t) (j : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g j,
        heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)⟫_ℝ =
      TensorEigenIdx.lambda (I := I) (M := M) j *
        scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
  classical
  set L := tensor00ScalarL2Equiv g
  set v := L u₀
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let lam : EigenIdx (I := I) (M := M) g → ℝ := fun k =>
    EigenIdx.lambda (I := I) (M := M) k
  have hdef : heatPower (I := I) (M := M) g 1 t v =
      ∑' k : EigenIdx (I := I) (M := M) g,
        (lam k ^ 1 * Real.exp (-(lam k) * t)) • (⟪b k, v⟫_ℝ • b k) := by
    unfold heatPower
    rw [dif_neg (by norm_num : (1 : ℕ) ≠ 0)]
    rw [dif_pos ht]
    rfl
  have hdef' : heatPower (I := I) (M := M) g 1 t v =
      ∑' k : EigenIdx (I := I) (M := M) g,
        (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k) := by
    rw [hdef]
    apply tsum_congr
    intro k
    congr 2
    · congr 1
      ring
  have ht0 : 0 ≤ t := ht.le
  have hhalf : 0 < t / 2 := half_pos ht
  obtain ⟨Md, hMd0, hbdd⟩ := exists_pow_mul_exp_neg_mul_bddAbove (t / 2) hhalf 1
  have hlam_bdd (k : EigenIdx (I := I) (M := M) g) :
      lam k * Real.exp (-(lam k * t)) ≤ Md := by
    have h := hbdd (lam k)
      (DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg
        (I := I) (M := M) k)
    calc
      lam k * Real.exp (-(lam k * t))
          = lam k ^ 1 * Real.exp (-(2 * (t / 2) * lam k)) := by
            rw [pow_one]
            congr 1
            congr 1
            ring
      _ ≤ Md := h
  have hsum : Summable (fun k : EigenIdx (I := I) (M := M) g =>
      (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)) := by
    have h_orthonormal : Orthonormal ℝ b := b.orthonormal
    have h_orthFam :
        OrthogonalFamily ℝ (fun _ : EigenIdx (I := I) (M := M) g => ℝ)
          (fun i => LinearIsometry.toSpanSingleton ℝ
            (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
            (h_orthonormal.1 i)) :=
      h_orthonormal.orthogonalFamily
    let f : EigenIdx (I := I) (M := M) g → ℝ := fun k =>
      lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ
    have h_sq : Summable (fun k => (f k) ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
        ((summable_basis_coeff_sq (I := I) (M := M) g v).mul_left (Md ^ 2))
      intro k
      calc
        (f k) ^ 2 = (lam k * Real.exp (-(lam k * t))) ^ 2 * (⟪b k, v⟫_ℝ) ^ 2 := by
              dsimp [f]
              rw [pow_one]
              ring
        _ ≤ Md ^ 2 * (⟪b k, v⟫_ℝ) ^ 2 := by
              have hnn : 0 ≤ lam k * Real.exp (-(lam k * t)) :=
                mul_nonneg
                  (DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx.lambda_nonneg
                    (I := I) (M := M) k)
                  (Real.exp_pos _).le
              exact mul_le_mul ((sq_le_sq₀ hnn hMd0).mpr (hlam_bdd k)) (le_rfl)
                (sq_nonneg _) (by positivity)
    have h_iff := h_orthFam.summable_iff_norm_sq_summable
      (fun k => lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ)
    have h_sq_eq : (fun k =>
        ‖(lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ)‖ ^ 2) =
        (fun k => (lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ) ^ 2) := by
      funext k
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_sq_eq] at h_iff
    have h_summable_V : Summable (fun k =>
        LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 k)
          (lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ)) :=
      h_iff.mpr (Summable.congr h_sq (fun k => by
        dsimp [f]))
    have h_map_eq : (fun k =>
        LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 k)
          (lam k ^ 1 * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ)) =
        (fun k => (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)) := by
      funext k
      rw [LinearIsometry.toSpanSingleton_apply]
      rw [mul_smul]
    rwa [h_map_eq] at h_summable_V
  have hsumHP : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
      (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k))
      (heatPower (I := I) (M := M) g 1 t v) := by
    rw [hdef']
    exact hsum.hasSum
  let hw_h : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g j),
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (scalarEigenFunction g j)⟩
  have hH1 : H1ComplToLp (I := I) (M := M) g (hw_h : H1Compl g) =
      scalarEigenFunctionLp g j := by
    change H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g j)) = _
    rw [H1ComplToLp_smoothToH1Compl]
    rfl
  have hzero_of_ne (k : EigenIdx (I := I) (M := M) g)
      (hlam : lam k ≠ TensorEigenIdx.lambda (I := I) (M := M) j) :
      ⟪b k, scalarEigenFunctionLp g j⟫_ℝ = 0 := by
    have hinner_lap := laplacianOp_inner_eigenbasis (I := I) (M := M) g hw_h k
    have h1 : ⟪b k, laplacianOp (I := I) (M := M) g hw_h⟫_ℝ =
        -lam k * ⟪b k, scalarEigenFunctionLp g j⟫_ℝ := by
      rw [hinner_lap, hH1]
    have h2 : ⟪b k, laplacianOp (I := I) (M := M) g hw_h⟫_ℝ =
        -TensorEigenIdx.lambda (I := I) (M := M) j *
          ⟪b k, scalarEigenFunctionLp g j⟫_ℝ := by
      change ⟪b k, laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g (scalarEigenFunction g j),
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M)
              (scalarEigenFunction g j)⟩⟫_ℝ =
        -TensorEigenIdx.lambda (I := I) (M := M) j *
          ⟪b k, scalarEigenFunctionLp g j⟫_ℝ
      rw [laplacianOp_scalarEigenFunctionLp (I := I) (M := M) g j]
      simp [inner_smul_right]
    have hsub : (lam k - TensorEigenIdx.lambda (I := I) (M := M) j) *
        ⟪b k, scalarEigenFunctionLp g j⟫_ℝ = 0 := by
      nlinarith [h1, h2]
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hlam)
  have hmatch (k : EigenIdx (I := I) (M := M) g) :
      lam k * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ =
        TensorEigenIdx.lambda (I := I) (M := M) j *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
          ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ := by
    by_cases hlam : lam k = TensorEigenIdx.lambda (I := I) (M := M) j
    · rw [hlam]
    · have hzero : ⟪scalarEigenFunctionLp g j, b k⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hzero_of_ne k hlam
      simp [hzero]
  have hinner_sum : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
      ⟪scalarEigenFunctionLp g j,
        (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)⟫_ℝ)
      ⟪scalarEigenFunctionLp g j, heatPower (I := I) (M := M) g 1 t v⟫_ℝ :=
    (innerSL (𝕜 := ℝ) (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (scalarEigenFunctionLp g j)).hasSum hsumHP
  have hsummand (k : EigenIdx (I := I) (M := M) g) :
      ⟪scalarEigenFunctionLp g j,
        (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)⟫_ℝ =
        lam k * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ *
          ⟪scalarEigenFunctionLp g j, b k⟫_ℝ := by
    rw [pow_one]
    rw [real_inner_smul_right, real_inner_smul_right]
    ring
  have hsummand' : (fun k : EigenIdx (I := I) (M := M) g =>
      ⟪scalarEigenFunctionLp g j,
        (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)⟫_ℝ) =
      (fun k : EigenIdx (I := I) (M := M) g =>
        TensorEigenIdx.lambda (I := I) (M := M) j *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
          ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ) := by
    funext k
    calc
      ⟪scalarEigenFunctionLp g j,
          (lam k ^ 1 * Real.exp (-(lam k * t))) • (⟪b k, v⟫_ℝ • b k)⟫_ℝ
          = lam k * Real.exp (-(lam k * t)) * ⟪b k, v⟫_ℝ *
              ⟪scalarEigenFunctionLp g j, b k⟫_ℝ := hsummand k
      _ = TensorEigenIdx.lambda (I := I) (M := M) j *
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
            ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ := hmatch k
  have hinner_sum' : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
      TensorEigenIdx.lambda (I := I) (M := M) j *
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
        ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ)
      ⟪scalarEigenFunctionLp g j, heatPower (I := I) (M := M) g 1 t v⟫_ℝ := by
    rw [hsummand'] at hinner_sum
    exact hinner_sum
  have hcv : ⟪scalarEigenFunctionLp g j, v⟫_ℝ = tensorL2Coeff (I := I) (M := M) hc u₀ j := by
    have hφ := scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g j
    calc
      ⟪scalarEigenFunctionLp g j, v⟫_ℝ
          = ⟪L (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g), L u₀⟫_ℝ := by
            rw [hφ]
      _ = ⟪(eigenvectorSmooth g 0 0 j : TensorL2 0 0 g), u₀⟫_ℝ := by
            exact (tensor00ScalarL2Equiv g).toLinearIsometry.inner_map_map
              (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) u₀
      _ = tensorL2Coeff (I := I) (M := M) hc u₀ j := by
            rw [tensorL2Coeff_eq_inner]
            congr 1
            exact eigenvectorSmooth00_eq_basis (I := I) (M := M) g j
  have hrepr : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
      ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ)
      ⟪scalarEigenFunctionLp g j, v⟫_ℝ := by
    have hb := b.hasSum_repr v
    have hb' : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
        ⟪scalarEigenFunctionLp g j, b.repr v k • b k⟫_ℝ)
        ⟪scalarEigenFunctionLp g j, v⟫_ℝ :=
      (innerSL (𝕜 := ℝ) (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        (scalarEigenFunctionLp g j)).hasSum hb
    have hsame : (fun k : EigenIdx (I := I) (M := M) g =>
        ⟪scalarEigenFunctionLp g j, b.repr v k • b k⟫_ℝ) =
        (fun k : EigenIdx (I := I) (M := M) g =>
          ⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ) := by
      funext k
      rw [HilbertBasis.repr_apply_apply]
      rw [real_inner_smul_right]
    rwa [hsame] at hb'
  let e' : ℝ := Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t))
  have hinner_sum'' : HasSum (fun k : EigenIdx (I := I) (M := M) g =>
      (⟪b k, v⟫_ℝ * ⟪scalarEigenFunctionLp g j, b k⟫_ℝ) •
        (TensorEigenIdx.lambda (I := I) (M := M) j * e'))
      ⟪scalarEigenFunctionLp g j, heatPower (I := I) (M := M) g 1 t v⟫_ℝ := by
    refine HasSum.congr_fun hinner_sum' ?_
    intro k
    simp [e', smul_eq_mul]
    ring_nf
  have htarget :
      ⟪scalarEigenFunctionLp g j, heatPower (I := I) (M := M) g 1 t v⟫_ℝ =
        ⟪scalarEigenFunctionLp g j, v⟫_ℝ •
          (TensorEigenIdx.lambda (I := I) (M := M) j * e') :=
    hinner_sum''.unique (hrepr.smul_const
      (TensorEigenIdx.lambda (I := I) (M := M) j * e'))
  calc
    ⟪scalarEigenFunctionLp g j,
        heatPower (I := I) (M := M) g 1 t (L u₀)⟫_ℝ
        = ⟪scalarEigenFunctionLp g j, v⟫_ℝ •
            (TensorEigenIdx.lambda (I := I) (M := M) j * e') := htarget
    _ = TensorEigenIdx.lambda (I := I) (M := M) j *
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
          tensorL2Coeff (I := I) (M := M) hc u₀ j := by
          rw [hcv]
          rw [smul_eq_mul]
          change tensorL2Coeff (I := I) (M := M) hc u₀ j *
              (TensorEigenIdx.lambda (I := I) (M := M) j *
                Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t))) =
            TensorEigenIdx.lambda (I := I) (M := M) j *
              Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j * t)) *
              tensorL2Coeff (I := I) (M := M) hc u₀ j
          ring_nf
    _ = TensorEigenIdx.lambda (I := I) (M := M) j *
          scalarHeatCoeff (I := I) (M := M) g u₀ j t := by
          unfold scalarHeatCoeff
          ring_nf

theorem scalarHeatFlowTimeDerivSliceTensor_toL2_eq_neg_heatPower
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    smoothToLp (I := I) (M := M) g
        (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht) =
      -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)) := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le ha (Set.mem_Icc.mp ht).1
  have hw1 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          smoothToLp (I := I) (M := M) g
            (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht)⟫_ℝ •
        scalarEigenFunctionLp g i)
      (smoothToLp (I := I) (M := M) g
        (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht)) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g
        (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht))
  have hw2 : HasSum (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀))⟫_ℝ •
        scalarEigenFunctionLp g i)
      (-(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀))) :=
    hasSum_scalarEigenFunctionLp_repr (I := I) (M := M) g
      (-(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)))
  have hsame : (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          smoothToLp (I := I) (M := M) g
            (scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht)⟫_ℝ •
        scalarEigenFunctionLp g i) =
      (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i,
          -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀))⟫_ℝ •
        scalarEigenFunctionLp g i) := by
    funext i
    rw [scalarHeatCoeff_lambda_eq_inner_slice (I := I) (M := M) g u₀ htail hab ha ht i]
    rw [inner_neg_right]
    rw [heatPower_one_inner_eq_lambda_coeff (I := I) (M := M) g u₀ ht0 i]
    ring_nf
  exact hw1.unique (by
    rw [hsame]
    exact hw2)

theorem scalarHeatFlowSliceTensor_laplacian_toL2_eq_neg_heatPower
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    smoothToLp (I := I) (M := M) g
        (scalarHeatFlowSliceTensor g u₀ htail hab ha ht).laplacian =
      -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)) := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le ha (Set.mem_Icc.mp ht).1
  let slice : SmoothScalar g := scalarHeatFlowSliceTensor g u₀ htail hab ha ht
  let u_dom : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g slice,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) slice⟩
  let heat_dom : laplacianDomain (I := I) (M := M) g :=
    ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t (tensor00ScalarL2Equiv g u₀),
      heatSemigroupExplicitLift_zero_mem_laplacianDomain
        (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀)⟩
  have hu_dom_lp : H1ComplToLp (I := I) (M := M) g (u_dom : H1Compl g) =
      heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀) := by
    change H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g slice) = _
    rw [H1ComplToLp_smoothToH1Compl]
    exact scalarHeatFlowSliceTensor_toL2_eq_heatSemigroup
      (I := I) (M := M) g u₀ htail hab ha ht
  have hheat_dom_lp : H1ComplToLp (I := I) (M := M) g (heat_dom : H1Compl g) =
      heatSemigroup (I := I) (M := M) g t (tensor00ScalarL2Equiv g u₀) := by
    exact H1ComplToLp_heatSemigroupExplicitLift
      (I := I) (M := M) g 0 ht0 (tensor00ScalarL2Equiv g u₀)
  have hdom : u_dom = heat_dom := by
    apply Subtype.ext
    exact H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g
      (hu_dom_lp.trans hheat_dom_lp.symm)
  have hu_laplacian : laplacianOp (I := I) (M := M) g u_dom =
      -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)) := by
    rw [hdom]
    exact laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
      (I := I) (M := M) g ht0 (tensor00ScalarL2Equiv g u₀)
  rw [← laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian (I := I) (M := M) slice]
  exact hu_laplacian

theorem scalarHeatFlowTensor_laplacian_eq_time_deriv
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun x => scalarHeatFlowTensor g u₀ t x) x =
      scalarSpecSum (I := I) (M := M) g
        (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
          scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x := by
  classical
  let slice : SmoothScalar g := scalarHeatFlowSliceTensor g u₀ htail hab ha ht
  let dslice : SmoothScalar g := scalarHeatFlowTimeDerivSliceTensor g u₀ htail hab ha ht
  have hlp : smoothToLp (I := I) (M := M) g slice.laplacian =
      -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)) :=
    scalarHeatFlowSliceTensor_laplacian_toL2_eq_neg_heatPower
      (I := I) (M := M) g u₀ htail hab ha ht
  have hd : smoothToLp (I := I) (M := M) g dslice =
      -(heatPower (I := I) (M := M) g 1 t (tensor00ScalarL2Equiv g u₀)) :=
    scalarHeatFlowTimeDerivSliceTensor_toL2_eq_neg_heatPower
      (I := I) (M := M) g u₀ htail hab ha ht
  have hle : slice.laplacian = dslice :=
    smoothToLp_injective (I := I) (M := M) g (hlp.trans hd.symm)
  have hx : (slice.laplacian).toFun x = dslice.toFun x :=
    congrFun (congrArg SmoothScalar.toFun hle) x
  calc
    laplacian (I := I) (LeviCivita (I := I) g) g (fun x => scalarHeatFlowTensor g u₀ t x) x
        = (slice.laplacian).toFun x := by
          change laplacian (I := I) (LeviCivita (I := I) g) g slice.toFun x =
            (slice.laplacian).toFun x
          rw [laplacian_levi_eq (I := I) g
            slice.smooth x]
          rw [← SmoothScalar.laplacian_toFun]
    _ = dslice.toFun x := hx
    _ = scalarSpecSum (I := I) (M := M) g
          (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
            scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x := rfl

theorem scalarHeatFlowTensor_isHeatOnStationary
    (g : SmoothRiemannianMetric I M) (u₀ : TensorL2 0 0 g)
    (htail : EigenvalueTailSummable g 0 0)
    {a b : ℝ} (hab : a < b) (ha : 0 < a) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed a b hab.le) g (scalarHeatFlowTensor g u₀) := by
  change DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
    (RealTimeInterval.closed a b hab.le)
    (stationaryMetricFamily g) (fun _ _ => (0 : ℝ)) (scalarHeatFlowTensor g u₀)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (scalarHeatFlowTensor_contMDiffOn_top (I := I) (M := M) g u₀ htail hab ha).mono
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  · exact (scalarHeatFlowTensor_contMDiffOn_top (I := I) (M := M) g u₀ htail hab ha).continuousOn
  · intro t ht
    exact scalarHeatFlowTensor_slice_contMDiff (I := I) (M := M) g u₀ htail hab ha ht
  · intro t ht x
    have htIcc : t ∈ Set.Icc a b :=
      Set.mem_Icc.mpr ⟨(Set.mem_Ioo.mp ht).1.le, (Set.mem_Ioo.mp ht).2.le⟩
    have hderiv := scalarHeatFlowTensor_hasDerivAt (I := I) (M := M) g u₀ htail hab ha ht x
    have hlap := scalarHeatFlowTensor_laplacian_eq_time_deriv
      (I := I) (M := M) g u₀ htail hab ha htIcc x
    refine hderiv.congr_deriv ?_
    calc
      scalarSpecSum (I := I) (M := M) g
          (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
            scalarHeatCoeff (I := I) (M := M) g u₀ i s) t x
          = laplacian (I := I) (LeviCivita (I := I) g) g
              (fun x => scalarHeatFlowTensor g u₀ t x) x := hlap.symm
      _ = laplacianAt (I := I) (stationaryMetricFamily g) t (scalarHeatFlowTensor g u₀ t) x +
            0 * scalarHeatFlowTensor g u₀ t x := by
            unfold laplacianAt stationaryMetricFamily
            simp [zero_mul, add_zero]
            rfl

theorem scalarHeatFlow_isHeatOnStationary
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {a b : ℝ} (hab : a < b) (ha : 0 < a) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed a b hab.le) g (scalarHeatFlow g u₀) := by
  have h := scalarHeatFlowTensor_isHeatOnStationary (I := I) (M := M) g
    ((tensor00ScalarL2Equiv g).symm u₀) (scalar_eigen_tail (I := I) (M := M) g) hab ha
  simpa [scalarHeatFlow] using h

theorem scalarHeatFlowSlice_toL2_eq_heatSemigroup
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    smoothToLp (I := I) (M := M) g (scalarHeatFlowSlice g u₀ hab ha ht) =
      heatSemigroup (I := I) (M := M) g t u₀ := by
  have h := scalarHeatFlowSliceTensor_toL2_eq_heatSemigroup (I := I) (M := M) g
    ((tensor00ScalarL2Equiv g).symm u₀) (scalar_eigen_tail (I := I) (M := M) g) hab ha ht
  simpa [scalarHeatFlowSlice] using h

theorem scalarHeatFlow_slice_contMDiff
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => scalarHeatFlow g u₀ t x) := by
  have h := scalarHeatFlowTensor_slice_contMDiff (I := I) (M := M) g
    ((tensor00ScalarL2Equiv g).symm u₀) (scalar_eigen_tail (I := I) (M := M) g) hab ha ht
  simpa [scalarHeatFlow] using h

theorem scalarHeatFlowTensor_zero_apply
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g) (x : M) :
    scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) 0 x = u₀.toFun x := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  calc
    scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) 0 x
        = scalarSpecSum (I := I) (M := M) g
            (fun i _ => tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i) 0 x := by
          dsimp [scalarHeatFlowTensor, scalarHeatCoeff]
          unfold scalarSpecSum
          apply tsum_congr
          intro i
          simp
    _ = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) (scalarCcLift g u₀).toSection x := by
          exact congrFun (scalarSpec_cc (I := I) (M := M) g (scalarCcLift g u₀)) x
    _ = u₀.toFun x := by
          exact congrFun (congrArg SmoothScalar.toFun
            (scalar0Cc_scalarCcLift (I := I) (M := M) g u₀)) x

private lemma summable_abs_tensorL2Coeff_mul_hsWeight_of_smooth
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0) :
    Summable (fun i : TensorEigenIdx00 g =>
      |tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i| *
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
          (((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) / 2)) := by
  classical
  let N₀ : ℕ := Module.finrank ℝ E / 2 + 1
  let σ : ℝ := (N₀ : ℝ)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let d : TensorEigenIdx00 g → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i
  obtain ⟨p, hp, htail_p⟩ := htail
  have htail_p2 : Summable (fun i : TensorEigenIdx00 g =>
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p)) := htail_p
  have hsmooth : Summable (fun i : TensorEigenIdx00 g =>
      tensorSobolevWeight (I := I) (M := M) i (σ + p) * (d i) ^ 2) := by
    let S : SmoothCcTensor g 0 0 := scalarCcLift g u₀
    let V : tensorHs (I := I) (M := M) g 0 0 (σ + p) :=
      ccTensorToHs (I := I) (M := M) g 0 (σ + p) S
    have hcoeff (i : TensorEigenIdx00 g) : (V.coeff i) = d i := by
      dsimp [V, S, d]
    exact Summable.congr V.weighted_summable (fun i => by
      rw [hcoeff i])
  have hAMGM (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hmain (i : TensorEigenIdx00 g) :
      |d i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) ≤
        (tensorSobolevWeight (I := I) (M := M) i (σ + p) * (d i) ^ 2 +
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p)) / 2 := by
    let x : ℝ := 1 + TensorEigenIdx.lambda (I := I) (M := M) i
    have hx0 : 0 < x := by
      dsimp [x]
      linarith [tensor_lambda_nonneg (I := I) (M := M) i]
    calc
      |d i| * x ^ (σ / 2)
          = (|d i| * x ^ ((σ + p) / 2)) * x ^ (-(p / 2)) := by
            rw [mul_assoc]
            congr 1
            rw [← Real.rpow_add hx0 ((σ + p) / 2) (-(p / 2))]
            congr 1
            ring_nf
      _ ≤ ((|d i| * x ^ ((σ + p) / 2)) ^ 2 + (x ^ (-(p / 2))) ^ 2) / 2 :=
            hAMGM (|d i| * x ^ ((σ + p) / 2)) (x ^ (-(p / 2)))
      _ = (x ^ (σ + p) * (d i) ^ 2 + x ^ (-p)) / 2 := by
            congr 1
            rw [mul_pow, sq_abs]
            rw [rpow_sq_eq hx0.le ((σ + p) / 2)]
            rw [rpow_sq_eq hx0.le (-(p / 2))]
            congr 1
            · ring_nf
            · ring_nf
  have hb : Summable (fun i : TensorEigenIdx00 g =>
      (tensorSobolevWeight (I := I) (M := M) i (σ + p) * (d i) ^ 2 +
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p)) / 2) :=
    (hsmooth.add htail_p2).div_const 2
  exact Summable.of_nonneg_of_le
    (fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg
      (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) (σ / 2)))
    hmain hb

theorem scalarHeatFlowTensor_smoothInitial_continuousOn_closed
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0) {T : ℝ} :
    ContinuousOn (fun q : ℝ × M =>
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) q.1 q.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set M)) := by
  classical
  let N₀ : ℕ := Module.finrank ℝ E / 2 + 1
  let σ : ℝ := (N₀ : ℝ)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let d : TensorEigenIdx00 g → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i
  obtain ⟨C0, hC0, hφbdd⟩ := scalarEigenFunction_abs_le (I := I) (M := M) g
  let u : TensorEigenIdx00 g → ℝ := fun i =>
    C0 * (|d i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2))
  have hu_sum : Summable u := by
    have hsum := summable_abs_tensorL2Coeff_mul_hsWeight_of_smooth
      (I := I) (M := M) g u₀ htail
    exact Summable.mul_left C0 (by
      change Summable (fun i : TensorEigenIdx00 g =>
        |d i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2))
      exact hsum)
  let f : TensorEigenIdx00 g → ℝ × M → ℝ := fun i q =>
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * q.1) *
      d i * (scalarEigenFunction g i).toFun q.2
  have hf_cont (i : TensorEigenIdx00 g) :
      ContinuousOn (f i) (Set.Icc 0 T ×ˢ Set.univ) := by
    dsimp [f]
    exact ((((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        continuous_const).mul
        ((scalarEigenFunction g i).smooth.continuous.comp continuous_snd))).continuousOn
  have hfu (i : TensorEigenIdx00 g) (q : ℝ × M) (hq : q ∈ Set.Icc 0 T ×ˢ Set.univ) :
      ‖f i q‖ ≤ u i := by
    dsimp [f, u]
    have ht0 : 0 ≤ q.1 := (Set.mem_Icc.mp hq.1).1
    have hlam0 : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    let e : ℝ := Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * q.1)
    let phi : ℝ := (scalarEigenFunction g i).toFun q.2
    have he_le : e ≤ 1 := by
      dsimp [e]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hφ : |(scalarEigenFunction g i).toFun q.2| ≤
        C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2) :=
      hφbdd i q.2
    have he1 : |e| ≤ 1 := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      exact he_le
    have hd0 : 0 ≤ |d i| := abs_nonneg _
    calc
      ‖e * d i * phi‖
          = |e| * |d i| * |phi| := by
            rw [Real.norm_eq_abs]
            rw [abs_mul, abs_mul]
      _ ≤ C0 * (|d i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by
            calc
              |e| * |d i| * |phi|
                  ≤ 1 * |d i| * |phi| := mul_le_mul
                    (mul_le_mul he1 (le_rfl) (abs_nonneg _) (by positivity))
                    (le_rfl) (abs_nonneg _) (by positivity)
              _ = |d i| * |phi| := by ring
              _ ≤ |d i| * (C0 * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) :=
                    mul_le_mul_of_nonneg_left hφ hd0
              _ = C0 * (|d i| * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (σ / 2)) := by ring
  have hcont := continuousOn_tsum (f := f) (s := Set.Icc 0 T ×ˢ Set.univ) hf_cont hu_sum hfu
  refine hcont.congr ?_
  intro q hq
  dsimp [f]
  unfold scalarHeatFlowTensor scalarSpecSum
  apply tsum_congr
  intro i
  unfold scalarHeatCoeff
  dsimp [d]
  rfl

theorem scalarHeatFlowTensorSmoothInitial_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    have hf : (fun x : M =>
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) 0 x) =
        u₀.toFun := by
      funext x
      exact scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x
    rw [hf]
    exact u₀.smooth
  · have htpos : 0 < t := lt_of_le_of_ne (Set.mem_Icc.mp ht).1 (Ne.symm ht0)
    have hε : 0 < t / 2 := half_pos htpos
    have hεT : t / 2 < T := lt_of_lt_of_le (half_lt_self htpos) (Set.mem_Icc.mp ht).2
    have ht' : t ∈ Set.Icc (t / 2) T :=
      Set.mem_Icc.mpr ⟨(half_lt_self htpos).le, (Set.mem_Icc.mp ht).2⟩
    exact scalarHeatFlowTensor_slice_contMDiff (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε ht'

noncomputable def scalarHeatFlowTensorSmoothInitialSlice
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) : SmoothScalar g :=
  ⟨fun x => scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x,
    scalarHeatFlowTensorSmoothInitial_slice_contMDiff (I := I) (M := M) g u₀ htail ht⟩

theorem scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g
      (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀))) := by
  change DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
    (RealTimeInterval.closed 0 T hT)
    (stationaryMetricFamily g) (fun _ _ => (0 : ℝ))
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply contMDiffOn_of_locally_contMDiffOn
    rintro ⟨t, x⟩ ⟨ht, _⟩
    have htpos : 0 < t := (Set.mem_Ioo.mp ht).1
    have htT : t < T := (Set.mem_Ioo.mp ht).2
    let ε : ℝ := t / 2
    have hε0 : 0 < ε := by
      dsimp [ε]
      positivity
    have hεt : ε < t := by
      dsimp [ε]
      exact half_lt_self htpos
    have hεT : ε < T := lt_of_lt_of_le hεt htT.le
    refine ⟨Set.Ioo ε T ×ˢ (Set.univ : Set M), isOpen_Ioo.prod isOpen_univ,
      ⟨⟨hεt, htT⟩, Set.mem_univ x⟩, ?_⟩
    have hjoint := scalarHeatFlowTensor_contMDiffOn_top (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε0
    have hsub : Set.Ioo ε T ⊆ Set.Ioo 0 T := by
      intro s hs
      exact ⟨lt_trans hε0 (Set.mem_Ioo.mp hs).1, (Set.mem_Ioo.mp hs).2⟩
    have hinter : (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) ∩
        (Set.Ioo ε T ×ˢ (Set.univ : Set M)) =
        Set.Ioo ε T ×ˢ (Set.univ : Set M) := by
      rw [Set.prod_inter_prod (s₁ := Set.Ioo 0 T) (t₁ := (Set.univ : Set M))
        (s₂ := Set.Ioo ε T) (t₂ := (Set.univ : Set M))]
      congr 1
      · rw [inter_comm]
        exact (Set.inter_eq_left.mpr hsub)
      · simp
    change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q => scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) q.1 q.2)
      ((Set.Ioo 0 T ×ˢ (Set.univ : Set M)) ∩ (Set.Ioo ε T ×ˢ (Set.univ : Set M)))
    rw [hinter]
    exact hjoint.mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  · exact scalarHeatFlowTensor_smoothInitial_continuousOn_closed (I := I) (M := M) g u₀ htail
  · intro t ht
    exact scalarHeatFlowTensorSmoothInitial_slice_contMDiff (I := I) (M := M) g u₀ htail ht
  · intro t ht x
    have htpos : 0 < t := (Set.mem_Ioo.mp ht).1
    have htT : t < T := (Set.mem_Ioo.mp ht).2
    have hε : 0 < t / 2 := half_pos htpos
    have hεT : t / 2 < T := lt_of_lt_of_le (half_lt_self htpos) htT.le
    have hderiv := scalarHeatFlowTensor_hasDerivAt (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε
      (Set.mem_Ioo.mpr ⟨half_lt_self htpos, htT⟩) x
    have hlap := scalarHeatFlowTensor_laplacian_eq_time_deriv (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε
      (Set.mem_Icc.mpr ⟨(half_lt_self htpos).le, htT.le⟩) x
    refine hderiv.congr_deriv ?_
    calc
      scalarSpecSum (I := I) (M := M) g
          (fun i s => -TensorEigenIdx.lambda (I := I) (M := M) i *
            scalarHeatCoeff (I := I) (M := M) g
              (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s) t x
          = laplacian (I := I) (LeviCivita (I := I) g) g
              (fun x => scalarHeatFlowTensor g
                (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x) x := hlap.symm
      _ = laplacianAt (I := I) (stationaryMetricFamily g) t
            (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t) x +
            0 * scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x := by
            unfold laplacianAt stationaryMetricFamily
            simp [zero_mul, add_zero]
            rfl

theorem scalarHeatFlowTensorSmoothInitialSlice_toL2_eq_heatSemigroup
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    smoothToLp (I := I) (M := M) g
        (scalarHeatFlowTensorSmoothInitialSlice g u₀ htail ht) =
      heatSemigroup (I := I) (M := M) g t (smoothToLp (I := I) (M := M) g u₀) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    rw [show heatSemigroup (I := I) (M := M) g 0 (smoothToLp (I := I) (M := M) g u₀) =
        smoothToLp (I := I) (M := M) g u₀ by simp]
    exact congrArg (smoothToLp (I := I) (M := M) g) (by
      apply SmoothScalar.ext
      funext x
      dsimp [scalarHeatFlowTensorSmoothInitialSlice]
      exact scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x)
  · have htpos : 0 < t := lt_of_le_of_ne (Set.mem_Icc.mp ht).1 (Ne.symm ht0)
    have hε : 0 < t / 2 := half_pos htpos
    have hεT : t / 2 < T := lt_of_lt_of_le (half_lt_self htpos) (Set.mem_Icc.mp ht).2
    have ht' : t ∈ Set.Icc (t / 2) T :=
      Set.mem_Icc.mpr ⟨(half_lt_self htpos).le, (Set.mem_Icc.mp ht).2⟩
    have hslice := scalarHeatFlowSliceTensor_toL2_eq_heatSemigroup (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε ht'
    have hU : tensor00ScalarL2Equiv g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) =
        smoothToLp (I := I) (M := M) g u₀ := by
      change tensor00ToScalarL2 g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) =
        smoothToLp (I := I) (M := M) g u₀
      rw [tensor00ToScalarL2_toL2]
      exact scalar0ToLp_scalarCcLift (I := I) (M := M) g u₀
    have hsame : scalarHeatFlowTensorSmoothInitialSlice g u₀ htail ht =
        scalarHeatFlowSliceTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε ht' := by
      apply SmoothScalar.ext
      rfl
    rw [hsame, ← hU]
    exact hslice

theorem scalarHeatFlowTensorSmoothInitial_restrict_eq
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} {ε : ℝ} (hε0 : 0 < ε) (hεT : ε < T)
    {t : ℝ} (ht : t ∈ Set.Icc ε T) :
    scalarHeatFlowTensorSmoothInitialSlice g u₀ htail
        (Set.mem_Icc.mpr ⟨le_trans hε0.le (Set.mem_Icc.mp ht).1, (Set.mem_Icc.mp ht).2⟩) =
      scalarHeatFlowSliceTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) htail hεT hε0 ht := by
  apply SmoothScalar.ext
  rfl

theorem scalarHeatFlowTensor_smoothInitial_unique
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T)
    (v : ℝ → M → ℝ)
    (hv : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g v)
    (hinit : ∀ x : M, v 0 x = u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      v t x = scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x := by
  classical
  have hu : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g
      (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀))) :=
    scalarHeatFlowTensor_isHeatOnStationary_smoothInitial (I := I) (M := M) g u₀ htail hT
  have hinit' : ∀ x : M,
      scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) 0 x = v 0 x := by
    intro x
    rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x]
    exact (hinit x).symm
  have hle := DifferentialGeometry.Analysis.Parabolic.heat_eq_of_initial_eq
    (I := I) (stationaryMetricFamily g) hT
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀))) v hu hv hinit'
  intro t ht x
  exact (hle t ht x).symm

theorem scalarHeatFlowTensor_smoothInitial_comparison
    (g : SmoothRiemannianMetric I M) (u₀ v₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ x : M, u₀.toFun x ≤ v₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x ≤
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g v₀)) t x := by
  classical
  have hu := scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g u₀ htail hT
  have hv := scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g v₀ htail hT
  have hinit' : ∀ x : M,
      scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) 0 x ≤
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g v₀)) 0 x := by
    intro x
    rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x,
      scalarHeatFlowTensor_zero_apply (I := I) (M := M) g v₀ x]
    exact hinit x
  exact DifferentialGeometry.Analysis.Parabolic.heat_comparison
    (I := I) (stationaryMetricFamily g) hT
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g v₀))) hu hv hinit'

theorem scalarHeatFlowTensor_smoothInitial_nonneg
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ x : M, 0 ≤ u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 ≤ scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x := by
  classical
  have hzero : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g (fun _ _ => (0 : ℝ)) := by
    change DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 T hT) (stationaryMetricFamily g)
      (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact contMDiffOn_const
    · exact continuousOn_const
    · intro t ht
      exact contMDiff_const
    · intro t ht x
      have hd : HasDerivAt (fun s : ℝ => (0 : ℝ)) (0 : ℝ) t :=
        hasDerivAt_const (c := (0 : ℝ)) (x := t)
      refine hd.congr_deriv ?_
      have hgrad (y : M) : gradientFun (I := I) g (fun _ : M => (0 : ℝ)) y = 0 := by
        apply gradientFun_eq_zero_of_mfderiv_eq_zero
        simp
      have hgrad_fun : gradientFun (I := I) g (fun _ : M => (0 : ℝ)) =
          fun y : M => (0 : TangentSpace I y) := by
        funext y
        exact hgrad y
      have hlap : laplacianAt (I := I) (stationaryMetricFamily g) t
          (fun _ : M => (0 : ℝ)) x = 0 := by
        unfold laplacianAt stationaryMetricFamily
        exact laplacian_const (I := I) (LeviCivita (I := I) g) g (0 : ℝ) x
      rw [hlap]
      simp
  exact DifferentialGeometry.Analysis.Parabolic.heat_comparison
    (I := I) (stationaryMetricFamily g) hT (fun _ _ => (0 : ℝ))
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    hzero (scalarHeatFlowTensor_isHeatOnStationary_smoothInitial (I := I) (M := M) g u₀ htail hT)
    (fun x => by
      rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x]
      exact hinit x)

theorem scalarHeatFlowTensor_smoothInitial_mass_invariant
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (∫ x, scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, u₀.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let slice : SmoothScalar g := scalarHeatFlowTensorSmoothInitialSlice g u₀ htail ht
  have hslice := scalarHeatFlowTensorSmoothInitialSlice_toL2_eq_heatSemigroup
    (I := I) (M := M) g u₀ htail ht
  have hmass := heatSemigroup_mass_invariant (I := I) (M := M) g
    (smoothToLp (I := I) (M := M) g u₀) (Set.mem_Icc.mp ht).1
  calc
    (∫ x, scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = ∫ x, (smoothToLp (I := I) (M := M) g slice : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          apply MeasureTheory.integral_congr_ae
          have hae := MemLp.coeFn_toLp (f := slice.toFun) (p := (2 : ℝ≥0∞))
            (μ := riemannianVolumeMeasure (I := I) (M := M) g) slice.memLp_two
          filter_upwards [hae] with x hx
          dsimp [slice, scalarHeatFlowTensorSmoothInitialSlice]
          exact hx.symm
    _ = ∫ x, (heatSemigroup (I := I) (M := M) g t (smoothToLp (I := I) (M := M) g u₀) :
            M → ℝ) x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          apply MeasureTheory.integral_congr_ae
          have hae : (smoothToLp (I := I) (M := M) g slice : M → ℝ) =ᵐ[
              riemannianVolumeMeasure (I := I) (M := M) g]
              (heatSemigroup (I := I) (M := M) g t (smoothToLp (I := I) (M := M) g u₀) :
                M → ℝ) := by
            rw [← hslice]
          filter_upwards [hae] with x hx
          exact hx
    _ = ∫ x, (smoothToLp (I := I) (M := M) g u₀ : M → ℝ) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hmass
    _ = ∫ x, u₀.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp (f := u₀.toFun) (p := (2 : ℝ≥0∞))
            (μ := riemannianVolumeMeasure (I := I) (M := M) g) u₀.memLp_two] with x hx
          exact hx

theorem mildSolution_slice_classical_equation_of_smooth_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k))
    (hmass_deriv : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g (deriv f) t k))
    (f_smooth : SmoothScalar g)
    (hf_smooth : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    ∃ u_smooth du_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
          mildSolution (I := I) (M := M) g u_0 f t ∧
        smoothToLp (I := I) (M := M) g du_smooth =
          -(heatPower (I := I) (M := M) g 1 t u_0) +
            mildSolution (I := I) (M := M) g (f 0) (deriv f) t ∧
        du_smooth = u_smooth.laplacian + f_smooth :=
  let ⟨u_smooth, du_smooth, hu, hdu, heq⟩ :=
    mildSolution_has_classical_representatives_of_forcingSpectralMass
      (I := I) (M := M) g u_0 hf ht hmass hmass_deriv f_smooth hf_smooth
  ⟨u_smooth, du_smooth, hu, hdu, heq⟩

noncomputable def scalarForcingCoeff
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : TensorEigenIdx00 g) (t : ℝ) : ℝ :=
  ⟪scalarEigenFunctionLp g i, f t⟫_ℝ

noncomputable def scalarForcedCoeff
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : TensorEigenIdx00 g) (t : ℝ) : ℝ :=
  ⟪scalarEigenFunctionLp g i, mildSolution (I := I) (M := M) g u₀ f t⟫_ℝ

noncomputable def scalarForcedFlow
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) (x : M) : ℝ :=
  scalarSpecSum (I := I) (M := M) g
    (fun i s => scalarForcedCoeff (I := I) (M := M) g u₀ f i s) t x

theorem mildSolution_inner_tensorBasis
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (i : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g i,
        mildSolution (I := I) (M := M) g u₀ f t⟫_ℝ =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ +
      ∫ s in (0 : ℝ)..t,
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * (t - s)) *
          ⟪scalarEigenFunctionLp g i, f s⟫_ℝ := by
  classical
  set φ : TensorEigenIdx00 g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    scalarEigenFunctionLp (I := I) (M := M) g
  set lam_i : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  unfold mildSolution
  rw [inner_add_right]
  congr 1
  · have h_self := heatSemigroup_isSelfAdjoint (I := I) (M := M) g ht
    have h_sym : (heatSemigroup (I := I) (M := M) g t :
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →ₗ[ℝ] _).IsSymmetric :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
        (A := heatSemigroup (I := I) (M := M) g t)).mp h_self)
    have h_swap : ⟪φ i, heatSemigroup (I := I) (M := M) g t u₀⟫_ℝ =
        ⟪heatSemigroup (I := I) (M := M) g t (φ i), u₀⟫_ℝ :=
      (h_sym.apply_clm (φ i) u₀).symm
    rw [h_swap]
    have h_basis_apply : heatSemigroup (I := I) (M := M) g t (φ i) =
        Real.exp (-lam_i * t) • φ i := by
      simpa [φ, lam_i] using heatSemigroup_apply_scalarEigenFunctionLp
        (I := I) (M := M) g i ht
    rw [h_basis_apply]
    rw [real_inner_smul_left]
  · have h_int := heatSemigroup_apply_f_continuous (I := I) (M := M) g hf t
    have h_uIcc : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
    rw [← h_uIcc] at h_int
    have h_intInt : IntervalIntegrable
        (fun s : ℝ => heatSemigroup (I := I) (M := M) g (t - s) (f s))
        MeasureTheory.volume 0 t := h_int.intervalIntegrable
    have h_comm := ContinuousLinearMap.intervalIntegral_comp_comm
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      (innerSL (𝕜 := ℝ)
        (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (φ i))
      h_intInt
    have h_phi_apply : ∀ s,
        (innerSL (𝕜 := ℝ)
          (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (φ i))
            (heatSemigroup (I := I) (M := M) g (t - s) (f s)) =
          ⟪φ i, heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ := by
      intro s; rfl
    change ⟪φ i, ∫ s in (0 : ℝ)..t,
        heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ = _
    rw [show ⟪φ i, ∫ s in (0 : ℝ)..t,
            heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ =
          (innerSL (𝕜 := ℝ)
            (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (φ i))
            (∫ s in (0 : ℝ)..t,
              heatSemigroup (I := I) (M := M) g (t - s) (f s)) from rfl]
    rw [← h_comm]
    have h_pointwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
        (innerSL (𝕜 := ℝ)
          (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (φ i))
            (heatSemigroup (I := I) (M := M) g (t - s) (f s)) =
          Real.exp (-lam_i * (t - s)) * ⟪φ i, f s⟫_ℝ := by
      intro s hs
      have hts_nn : 0 ≤ t - s := sub_nonneg.mpr hs.2
      rw [h_phi_apply]
      have h_self := heatSemigroup_isSelfAdjoint (I := I) (M := M) g hts_nn
      have h_sym : (heatSemigroup (I := I) (M := M) g (t - s) :
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →ₗ[ℝ] _).IsSymmetric :=
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
          (A := heatSemigroup (I := I) (M := M) g (t - s))).mp h_self)
      have h_swap : ⟪φ i, heatSemigroup (I := I) (M := M) g (t - s) (f s)⟫_ℝ =
          ⟪heatSemigroup (I := I) (M := M) g (t - s) (φ i), f s⟫_ℝ :=
        (h_sym.apply_clm (φ i) (f s)).symm
      rw [h_swap]
      have h_basis_apply : heatSemigroup (I := I) (M := M) g (t - s) (φ i) =
          Real.exp (-lam_i * (t - s)) • φ i := by
        simpa [φ, lam_i] using heatSemigroup_apply_scalarEigenFunctionLp
          (I := I) (M := M) g i hts_nn
      rw [h_basis_apply, real_inner_smul_left]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    exact h_pointwise s hs

private lemma scalarDuhamel_inner_factor
    (lam : ℝ) {t : ℝ} (h : ℝ → ℝ)
    (_h_int : IntervalIntegrable (fun s => Real.exp (lam * s) * h s)
      MeasureTheory.volume 0 t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s =
      Real.exp (-lam * t) * ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * h s := by
  have h_eq : (fun s : ℝ => Real.exp (-lam * (t - s)) * h s) =
      (fun s : ℝ => Real.exp (-lam * t) * (Real.exp (lam * s) * h s)) := by
    funext s
    have hf : Real.exp (-lam * (t - s)) = Real.exp (-lam * t) * Real.exp (lam * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf]
    ring
  rw [h_eq]
  rw [intervalIntegral.integral_const_mul]

theorem scalarForcedCoeff_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (i : TensorEigenIdx00 g) :
    HasDerivAt (fun s : ℝ => scalarForcedCoeff (I := I) (M := M) g u₀ f i s)
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
        scalarForcedCoeff (I := I) (M := M) g u₀ f i t +
        scalarForcingCoeff (I := I) (M := M) g f i t) t := by
  classical
  set φ : TensorEigenIdx00 g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    scalarEigenFunctionLp (I := I) (M := M) g
  set lam_i : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  set c_u : ℝ := ⟪φ i, u₀⟫_ℝ
  set hf_scalar : ℝ → ℝ := fun s => scalarForcingCoeff (I := I) (M := M) g f i s
  have hf_scalar_cont : Continuous hf_scalar := by
    dsimp [hf_scalar, scalarForcingCoeff]
    exact (innerSL (𝕜 := ℝ)
      (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (φ i)).continuous.comp hf
  set c1 : ℝ → ℝ := fun s => Real.exp (-lam_i * s) * c_u
  set G : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.exp (lam_i * r) * hf_scalar r
  set c2 : ℝ → ℝ := fun s => Real.exp (-lam_i * s) * G s
  have h_split : ∀ s, 0 ≤ s →
      scalarForcedCoeff (I := I) (M := M) g u₀ f i s = c1 s + c2 s := by
    intro s hs
    have h_form := mildSolution_inner_tensorBasis (I := I) (M := M) g u₀ hf hs i
    change ⟪φ i, mildSolution (I := I) (M := M) g u₀ f s⟫_ℝ = c1 s + c2 s
    rw [h_form]
    have h_int_factor : IntervalIntegrable
        (fun r => Real.exp (lam_i * r) * hf_scalar r)
        MeasureTheory.volume 0 s := by
      have h_cont_factor : Continuous
          (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r) :=
        ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul hf_scalar_cont)
      exact h_cont_factor.intervalIntegrable _ _
    have h_factored := scalarDuhamel_inner_factor (t := s) lam_i hf_scalar h_int_factor
    change Real.exp (-lam_i * s) * c_u +
      ∫ r in (0 : ℝ)..s, Real.exp (-lam_i * (s - r)) * hf_scalar r =
      c1 s + c2 s
    rw [h_factored]
  have h_c1_deriv : HasDerivAt c1 (-lam_i * Real.exp (-lam_i * t) * c_u) t := by
    have h_lin : HasDerivAt (fun s : ℝ => -lam_i * s) (-lam_i) t := by
      have := (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-lam_i)
      simpa using this
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
        (Real.exp (-lam_i * t) * (-lam_i)) t := h_lin.exp
    have h_mul := h_exp.mul_const c_u
    have h_eq : Real.exp (-lam_i * t) * (-lam_i) * c_u = -lam_i * Real.exp (-lam_i * t) * c_u := by
      ring
    rw [h_eq] at h_mul
    exact h_mul
  have h_G_deriv : HasDerivAt G (Real.exp (lam_i * t) * hf_scalar t) t := by
    have h_cont_integrand : Continuous
        (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r) :=
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hf_scalar_cont)
    have h_intInt :
        IntervalIntegrable (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r)
          MeasureTheory.volume 0 t :=
      h_cont_integrand.intervalIntegrable 0 t
    have h_meas : StronglyMeasurableAtFilter
        (fun r : ℝ => Real.exp (lam_i * r) * hf_scalar r)
        (𝓝 t) MeasureTheory.volume :=
      h_cont_integrand.aestronglyMeasurable.stronglyMeasurableAtFilter
    have h_at_t := h_cont_integrand.continuousAt (x := t)
    exact intervalIntegral.integral_hasDerivAt_right h_intInt h_meas h_at_t
  have h_exp_neg_deriv : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
      (-lam_i * Real.exp (-lam_i * t)) t := by
    have h_lin : HasDerivAt (fun s : ℝ => -lam_i * s) (-lam_i) t := by
      have := (hasDerivAt_id (𝕜 := ℝ) t).const_mul (-lam_i)
      simpa using this
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-lam_i * s))
        (Real.exp (-lam_i * t) * (-lam_i)) t := h_lin.exp
    have h_eq : Real.exp (-lam_i * t) * (-lam_i) = -lam_i * Real.exp (-lam_i * t) := by ring
    rw [h_eq] at h_exp
    exact h_exp
  have h_c2_deriv_raw : HasDerivAt c2
      ((-lam_i * Real.exp (-lam_i * t)) * G t +
        Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t)) t :=
    h_exp_neg_deriv.mul h_G_deriv
  have h_exp_cancel : Real.exp (-lam_i * t) * Real.exp (lam_i * t) = 1 := by
    rw [← Real.exp_add]
    have h_sum : -lam_i * t + lam_i * t = 0 := by ring
    rw [h_sum, Real.exp_zero]
  have h_c2_value : c2 t = Real.exp (-lam_i * t) * G t := rfl
  have h_c2_deriv : HasDerivAt c2 (-lam_i * c2 t + hf_scalar t) t := by
    have h_target_eq :
        (-lam_i * Real.exp (-lam_i * t)) * G t +
          Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t) =
        -lam_i * c2 t + hf_scalar t := by
      rw [h_c2_value]
      have h_assoc : Real.exp (-lam_i * t) * (Real.exp (lam_i * t) * hf_scalar t) =
          (Real.exp (-lam_i * t) * Real.exp (lam_i * t)) * hf_scalar t := by ring
      rw [h_assoc, h_exp_cancel, one_mul]
      ring
    rw [← h_target_eq]
    exact h_c2_deriv_raw
  have h_c1_value : c1 t = Real.exp (-lam_i * t) * c_u := rfl
  have h_c1_deriv' : HasDerivAt c1 (-lam_i * c1 t) t := by
    have h_target_eq : -lam_i * Real.exp (-lam_i * t) * c_u = -lam_i * c1 t := by
      rw [h_c1_value]; ring
    rw [← h_target_eq]
    exact h_c1_deriv
  have h_sum_deriv : HasDerivAt (fun s => c1 s + c2 s)
      (-lam_i * c1 t + (-lam_i * c2 t + hf_scalar t)) t :=
    h_c1_deriv'.add h_c2_deriv
  have h_target_eq : -lam_i * c1 t + (-lam_i * c2 t + hf_scalar t) =
      -lam_i * (c1 t + c2 t) + hf_scalar t := by ring
  rw [h_target_eq] at h_sum_deriv
  have h_at_t : c1 t + c2 t =
      scalarForcedCoeff (I := I) (M := M) g u₀ f i t :=
    (h_split t ht.le).symm
  rw [h_at_t] at h_sum_deriv
  have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have h_eventually_eq :
      (fun s : ℝ =>
        scalarForcedCoeff (I := I) (M := M) g u₀ f i s) =ᶠ[𝓝 t]
      (fun s : ℝ => c1 s + c2 s) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi (0 : ℝ), h_pos_nhds, ?_⟩
    intro s hs
    have hs_nn : 0 ≤ s := le_of_lt hs
    exact h_split s hs_nn
  simpa [hf_scalar, scalarForcingCoeff, lam_i, φ] using
    h_sum_deriv.congr_of_eventuallyEq h_eventually_eq

theorem scalarForcedCoeff_eq_exp_integral
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (i : TensorEigenIdx00 g) :
    scalarForcedCoeff (I := I) (M := M) g u₀ f i t =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ +
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ∫ s in (0 : ℝ)..t,
          Real.exp (TensorEigenIdx.lambda (I := I) (M := M) i * s) *
            scalarForcingCoeff (I := I) (M := M) g f i s := by
  classical
  set lam_i : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  have h_form := mildSolution_inner_tensorBasis (I := I) (M := M) g u₀ hf ht i
  change ⟪scalarEigenFunctionLp g i, mildSolution (I := I) (M := M) g u₀ f t⟫_ℝ =
    Real.exp (-lam_i * t) * ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ +
      Real.exp (-lam_i * t) *
        ∫ s in (0 : ℝ)..t, Real.exp (lam_i * s) *
          scalarForcingCoeff (I := I) (M := M) g f i s
  rw [h_form]
  rw [show (∫ s in (0 : ℝ)..t, Real.exp (-lam_i * (t - s)) *
          ⟪scalarEigenFunctionLp g i, f s⟫_ℝ) =
        ∫ s in (0 : ℝ)..t, Real.exp (-lam_i * (t - s)) *
          scalarForcingCoeff (I := I) (M := M) g f i s from by
      apply intervalIntegral.integral_congr
      intro s hs
      rfl]
  have h_int_factor : IntervalIntegrable
      (fun s => Real.exp (lam_i * s) * scalarForcingCoeff (I := I) (M := M) g f i s)
      MeasureTheory.volume 0 t := by
    have h_cont_factor : Continuous
        (fun s : ℝ => Real.exp (lam_i * s) * scalarForcingCoeff (I := I) (M := M) g f i s) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (by
          exact (innerSL (𝕜 := ℝ)
            (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
            (scalarEigenFunctionLp g i)).continuous.comp hf))
    exact h_cont_factor.intervalIntegrable _ _
  have h_factored := scalarDuhamel_inner_factor (t := t) lam_i
    (scalarForcingCoeff (I := I) (M := M) g f i) h_int_factor
  rw [h_factored]

theorem scalarForcingCoeff_contDiff
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {N : ℕ∞} (hf : ContDiff ℝ N f) (i : TensorEigenIdx00 g) :
    ContDiff ℝ N (fun t : ℝ => scalarForcingCoeff (I := I) (M := M) g f i t) := by
  dsimp [scalarForcingCoeff]
  exact (innerSL (𝕜 := ℝ)
    (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (scalarEigenFunctionLp g i)).contDiff.comp hf

theorem scalarForcedCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ ∞ f) (i : TensorEigenIdx00 g) (N : ℕ) :
    ContDiffOn ℝ (N : ℕ) (fun t : ℝ => scalarForcedCoeff (I := I) (M := M) g u₀ f i t)
      (Set.Ioi (0 : ℝ)) := by
  classical
  set lam_i : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  set c : ℝ → ℝ := fun t => scalarForcedCoeff (I := I) (M := M) g u₀ f i t
  set cf : ℝ → ℝ := fun t => scalarForcingCoeff (I := I) (M := M) g f i t
  have hfcont : Continuous f := hf.continuous
  have hc_eq : ∀ t ∈ Set.Ioi (0 : ℝ), deriv c t = -lam_i * c t + cf t := by
    intro t ht
    have hder := scalarForcedCoeff_hasDerivAt (I := I) (M := M) g u₀ hfcont ht i
    rw [hder.deriv]
  have hcf_cd : ∀ N : ℕ, ContDiffOn ℝ (N : ℕ) cf (Set.Ioi (0 : ℝ)) := by
    intro N
    have hle : ((N : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞))
    exact (scalarForcingCoeff_contDiff (I := I) (M := M) g
      (hf.of_le hle) i).contDiffOn
  have hmain : ∀ N : ℕ, ContDiffOn ℝ (N : ℕ) c (Set.Ioi (0 : ℝ)) := by
    intro N
    induction N with
    | zero =>
      have hG_cont : ContinuousOn
          (fun t : ℝ => ∫ s in (0 : ℝ)..t,
            Real.exp (lam_i * s) * scalarForcingCoeff (I := I) (M := M) g f i s)
          (Set.Ioi (0 : ℝ)) := by
        rw [isOpen_Ioi.continuousOn_iff]
        intro t ht
        have h_cf_cont : Continuous cf := by
          have h_innerCLM := (innerSL (𝕜 := ℝ)
              (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
              (scalarEigenFunctionLp g i)).continuous
          have h_eq : (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) =
              (fun s : ℝ => (innerSL (𝕜 := ℝ)
                (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
                (scalarEigenFunctionLp g i)) (f s)) := by
            funext s
            rw [scalarForcingCoeff, ← innerSL_apply_apply]
          dsimp [cf]
          rw [h_eq]
          exact h_innerCLM.comp hfcont
        have h_cont_integrand : Continuous
            (fun s : ℝ => Real.exp (lam_i * s) * cf s) :=
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul h_cf_cont)
        have h_intInt : IntervalIntegrable
            (fun s : ℝ => Real.exp (lam_i * s) * cf s)
            MeasureTheory.volume 0 t :=
          h_cont_integrand.intervalIntegrable 0 t
        have h_meas : StronglyMeasurableAtFilter
            (fun s : ℝ => Real.exp (lam_i * s) * cf s)
            (𝓝 t) MeasureTheory.volume :=
          h_cont_integrand.aestronglyMeasurable.stronglyMeasurableAtFilter
        have h_at_t := h_cont_integrand.continuousAt (x := t)
        exact (intervalIntegral.integral_hasDerivAt_right h_intInt h_meas h_at_t).continuousAt
      have hc1_cont : ContinuousOn (fun t : ℝ => Real.exp (-lam_i * t) *
          ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ) (Set.Ioi (0 : ℝ)) := by
        exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          continuous_const).continuousOn
      have hc2_cont : ContinuousOn (fun t : ℝ => Real.exp (-lam_i * t) *
          ∫ s in (0 : ℝ)..t, Real.exp (lam_i * s) * cf s)
          (Set.Ioi (0 : ℝ)) := by
        exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
          hG_cont
      have hsum_cont : ContinuousOn (fun t : ℝ =>
          Real.exp (-lam_i * t) * ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ +
          Real.exp (-lam_i * t) *
            ∫ s in (0 : ℝ)..t, Real.exp (lam_i * s) * cf s)
          (Set.Ioi (0 : ℝ)) :=
        hc1_cont.add hc2_cont
      exact (contDiffOn_zero.mpr (hsum_cont.congr (by
        intro t ht
        have hF := scalarForcedCoeff_eq_exp_integral (I := I) (M := M) g u₀ hfcont ht.le i
        dsimp [c, cf, lam_i]
        rw [hF])))
    | succ N ih =>
      have hdiff : DifferentiableOn ℝ c (Set.Ioi (0 : ℝ)) := by
        intro t ht
        exact DifferentiableAt.differentiableWithinAt
          (scalarForcedCoeff_hasDerivAt (I := I) (M := M) g u₀ hfcont ht i).differentiableAt
      have hdc : ContDiffOn ℝ (N : ℕ)
          (fun t : ℝ => deriv c t) (Set.Ioi (0 : ℝ)) := by
        have hcongr : ContDiffOn ℝ (N : ℕ) (fun t : ℝ => -lam_i * c t + cf t)
            (Set.Ioi (0 : ℝ)) := by
          exact (((contDiffOn_const : ContDiffOn ℝ (N : ℕ)
            (fun _ : ℝ => -lam_i) (Set.Ioi (0 : ℝ))).mul ih)).add (hcf_cd N)
        exact hcongr.congr (fun t ht => hc_eq t ht)
      change ContDiffOn ℝ (((N : ℕ∞) + 1)) c (Set.Ioi (0 : ℝ))
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ioi (0 : ℝ))]
      constructor
      · exact hdiff
      · constructor
        · intro hω
          simp at hω
        · refine hdc.congr ?_
          intro t ht
          exact derivWithin_of_isOpen (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))) ht
  exact hmain N

theorem scalarForcingCoeff_iteratedDeriv_fun
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ ∞ f) (i : TensorEigenIdx00 g) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => scalarForcingCoeff (I := I) (M := M) g f i t) =
      fun t : ℝ => scalarForcingCoeff (I := I) (M := M) g (iteratedDeriv r f) i t := by
  classical
  set L : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
    innerSL (𝕜 := ℝ)
      (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (scalarEigenFunctionLp g i)
  have hfder : ∀ r : ℕ, ContDiff ℝ ∞ (fun t : ℝ => iteratedDeriv r f t) := by
    intro r
    simpa [iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv r hf
  have hL : ∀ r : ℕ, ContDiff ℝ ∞ (fun t : ℝ => L (iteratedDeriv r f t)) := by
    intro r
    exact L.contDiff.comp (hfder r)
  induction r with
  | zero =>
    funext t
    simp [scalarForcingCoeff]
  | succ r ih =>
    funext t
    rw [iteratedDeriv_succ]
    rw [ih]
    have hg : HasDerivAt (fun t : ℝ => iteratedDeriv r f t) (iteratedDeriv (r + 1) f t) t := by
      have hdiff : DifferentiableAt ℝ (fun t : ℝ => iteratedDeriv r f t) t :=
        (hfder r).differentiable (by norm_num) t
      rw [iteratedDeriv_succ]
      exact hdiff.hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => L (iteratedDeriv r f t)) (L (iteratedDeriv (r + 1) f t)) t := by
      rw [hasDerivAt_iff_hasFDerivAt]
      have hcompF : HasFDerivAt (fun t : ℝ => L (iteratedDeriv r f t))
          (L.comp (ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv (r + 1) f t))) t :=
        L.hasFDerivAt.comp (x := t) hg.hasFDerivAt
      convert hcompF using 1
      apply ContinuousLinearMap.ext
      intro v
      simp [ContinuousLinearMap.toSpanSingleton, map_smul]
    simpa [scalarForcingCoeff, L] using hcomp.deriv

theorem scalarForcingCoeff_iteratedDeriv
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ ∞ f) (i : TensorEigenIdx00 g) (r : ℕ) (t : ℝ) :
    iteratedDeriv r (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) t =
      scalarForcingCoeff (I := I) (M := M) g (iteratedDeriv r f) i t := by
  exact congrFun (scalarForcingCoeff_iteratedDeriv_fun (I := I) (M := M) g hf i r) t

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorSymm_smoothToLp_duhamel
    (g : SmoothRiemannianMetric I M) (F : SmoothScalar g) :
    (tensor00ScalarL2Equiv g).symm (smoothToLp (I := I) (M := M) g F) =
      SmoothCcTensor.toL2 (scalarCcLift g F) := by
  have hU0 : (tensor00ScalarL2Equiv g) (SmoothCcTensor.toL2 (scalarCcLift g F)) =
      smoothToLp (I := I) (M := M) g F := by
    change tensor00ToScalarL2 g (SmoothCcTensor.toL2 (scalarCcLift g F)) =
      smoothToLp (I := I) (M := M) g F
    rw [tensor00ToScalarL2_toL2]
    exact scalar0ToLp_scalarCcLift (I := I) (M := M) g F
  simpa using congrArg (tensor00ScalarL2Equiv g).symm hU0.symm

private lemma scalarEigenCoeff_eq_tensorCoeff
    (g : SmoothRiemannianMetric I M) (F : SmoothScalar g) (i : TensorEigenIdx00 g) :
    ⟪scalarEigenFunctionLp g i, smoothToLp (I := I) (M := M) g F⟫_ℝ =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (SmoothCcTensor.toL2 (scalarCcLift g F)) i := by
  classical
  set L := tensor00ScalarL2Equiv g
  set b' := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
  have hb : L (b' i) = scalarEigenFunctionLp g i := by
    rw [show b' i = (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) by
      simp [b', eigenvectorSmooth_toL2]]
    exact (scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i).symm
  calc
    ⟪scalarEigenFunctionLp g i, smoothToLp (I := I) (M := M) g F⟫_ℝ
        = ⟪L (b' i), L (L.symm (smoothToLp (I := I) (M := M) g F))⟫_ℝ := by
          rw [hb]
          simp [LinearIsometry.inner_map_map L.toLinearIsometry (b' i)
            (L.symm (smoothToLp (I := I) (M := M) g F))).symm
    _ = ⟪b' i, L.symm (smoothToLp (I := I) (M := M) g F)⟫_ℝ := by
          simp [LinearIsometry.inner_map_map L.toLinearIsometry (b' i)
            (L.symm (smoothToLp (I := I) (M := M) g F))]
    _ = (b'.repr (L.symm (smoothToLp (I := I) (M := M) g F))) i := by
          simp [HilbertBasis.repr_apply_apply]
    _ = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
          (SmoothCcTensor.toL2 (scalarCcLift g F)) i := by
          rw [tensorSymm_smoothToLp_duhamel (I := I) (M := M) g F]
          rfl

private lemma scalarCoeff_sq_summable
    (g : SmoothRiemannianMetric I M)
    (v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : TensorEigenIdx00 g =>
      ⟪scalarEigenFunctionLp g i, v⟫_ℝ ^ 2) := by
  classical
  set b' := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
  set L := tensor00ScalarL2Equiv g
  have hsum : Summable (fun i : TensorEigenIdx00 g =>
      ‖⟪b' i, L.symm v⟫_ℝ‖ ^ 2) :=
    b'.orthonormal.inner_products_summable (L.symm v)
  refine Summable.congr hsum ?_
  intro i
  have hb : L (b' i) = scalarEigenFunctionLp g i := by
    rw [show b' i = (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g) by
      simp [b', eigenvectorSmooth_toL2]]
    exact (scalarEigenFunctionLp_eq_tensorBasis (I := I) (M := M) g i).symm
  have hinner : ⟪b' i, L.symm v⟫_ℝ = ⟪scalarEigenFunctionLp g i, v⟫_ℝ := by
    calc
      ⟪b' i, L.symm v⟫_ℝ = ⟪L (b' i), L (L.symm v)⟫_ℝ := by
            simpa using (LinearIsometry.inner_map_map L.toLinearIsometry (b' i) (L.symm v)).symm
      _ = ⟪scalarEigenFunctionLp g i, v⟫_ℝ := by
            rw [hb, LinearIsometryEquiv.apply_symm_apply]
  simp [hinner, Real.norm_eq_abs, sq_abs]

private lemma scalarForcingCoeff_deriv_eq
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ ∞ f) (i : TensorEigenIdx00 g) (t : ℝ) :
    deriv (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) t =
      scalarForcingCoeff (I := I) (M := M) g (deriv f) i t := by
  have h := scalarForcingCoeff_iteratedDeriv (I := I) (M := M) g hf i 1 t
  have h1 : iteratedDeriv 1 (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) t =
      deriv (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) t :=
    congrFun (iteratedDeriv_one (f := fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s)) t
  rw [← h1, h]
  rw [iteratedDeriv_one]

private lemma enat_coe_le_top (r : ℕ) :
    ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞))

private lemma iteratedDeriv_eq_iterate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (r : ℕ) : iteratedDeriv r f = deriv^[r] f := by
  revert f
  induction r with
  | zero => intro f; simp
  | succ r ih =>
    intro f
    rw [iteratedDeriv_succ']
    rw [show deriv^[r + 1] f = deriv^[r] (deriv f) by
      rw [Function.iterate_succ_apply]]
    exact ih (deriv f)

theorem scalarForcedCoeff_iteratedDeriv_succ
    (g : SmoothRiemannianMetric I M)
    (u₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : 0 < t) (i : TensorEigenIdx00 g) (r : ℕ) :
    iteratedDeriv (r + 1) (fun s : ℝ => scalarForcedCoeff (I := I) (M := M) g u₀ f i s) t =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
        iteratedDeriv r (fun s : ℝ => scalarForcedCoeff (I := I) (M := M) g u₀ f i s) t +
        iteratedDeriv r (fun s : ℝ => scalarForcingCoeff (I := I) (M := M) g f i s) t := by
  classical
  set lam : ℝ := TensorEigenIdx.lambda (I := I) (M := M) i
  set c : ℝ → ℝ := fun s => scalarForcedCoeff (I := I) (M := M) g u₀ f i s
  set cf : ℝ → ℝ := fun s => scalarForcingCoeff (I := I) (M := M) g f i s
  have hc_eq : ∀ s ∈ Set.Ioi (0 : ℝ), deriv c s = -TensorEigenIdx.lambda (I := I) (M := M) i * c s + cf s := by
    intro s hs
    have hder := scalarForcedCoeff_hasDerivAt (I := I) (M := M) g u₀ hf.continuous hs i
    rw [hder.deriv]
  have hloc : (fun s : ℝ => deriv c s) =ᶠ[𝓝 t] fun s : ℝ =>
      -lam * c s + cf s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simpa [lam] using hc_eq s hs
  rw [iteratedDeriv_succ']
  rw [Filter.EventuallyEq.iteratedDeriv_eq r hloc]
  have hcd : ContDiffAt ℝ (r : ℕ∞) c t :=
    (scalarForcedCoeff_contDiffOn (I := I) (M := M) g u₀ hf i r).contDiffAt
      (isOpen_Ioi.mem_nhds ht)
  have hcf : ContDiffAt ℝ (r : ℕ∞) cf t :=
    (scalarForcingCoeff_contDiff (I := I) (M := M) g (hf.of_le (enat_coe_le_top r)) i).contDiffAt
  have h1 : ContDiffAt ℝ (r : ℕ∞) (fun s : ℝ => -lam * c s) t :=
    (contDiffAt_const : ContDiffAt ℝ (r : ℕ∞) (fun _ : ℝ => -lam) t).mul hcd
  have hsum : iteratedDeriv r (fun s : ℝ => -lam * c s + cf s) t =
      -lam * iteratedDeriv r c t + iteratedDeriv r cf t := by
    change iteratedDeriv r ((fun s : ℝ => -lam * c s) + cf) t =
      -lam * iteratedDeriv r c t + iteratedDeriv r cf t
    rw [iteratedDeriv_add h1 hcf]
    rw [iteratedDeriv_const_mul (-lam) hcd]
  simpa [c, cf, lam] using hsum

private lemma summable_tensorSobolevWeight_mul_coeff_sq_of_smooth
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g) (σ : ℝ) :
    Summable (fun i : TensorEigenIdx00 g =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
          (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i) ^ 2) := by
  classical
  let S : SmoothCcTensor g 0 0 := scalarCcLift g u₀
  let V : tensorHs (I := I) (M := M) g 0 0 σ :=
    ccTensorToHs (I := I) (M := M) g 0 σ S
  have hcoeff (i : TensorEigenIdx00 g) : (V.coeff i) =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i := by
    dsimp [V, S]
  exact Summable.congr V.weighted_summable (fun i => by
    rw [hcoeff i])

theorem scalarHeatFlowTensor_smoothInitial_contMDiffOn_closed
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 < T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M =>
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
  classical
  rw [contMDiffOn_infty]
  intro N
  have hU : Set.Icc 0 T ⊆ Set.univ := Set.subset_univ _
  have hc (i : TensorEigenIdx00 g) :
      ContDiffOn ℝ (N : ℕ)
        (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g
          (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s) Set.univ := by
    exact (scalarHeatCoeff_contDiff (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i (N : ℕ∞)).contDiffOn
  set hc' := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  let d : TensorEigenIdx00 g → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M) hc' (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i
  have hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx00 g → ℝ, Summable Cm ∧
        ∀ i t, t ∈ Set.Icc 0 T →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g
              (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s) t) ^ 2 ≤ Cm i := by
    intro j hj m
    have hdecay := summable_tensorSobolevWeight_mul_coeff_sq_of_smooth
      (I := I) (M := M) g u₀ ((m : ℝ) + (2 * (j + 1) : ℕ))
    refine ⟨fun i => tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (2 * (j + 1) : ℕ)) *
        (d i) ^ 2, ?_, ?_⟩
    · exact Summable.congr hdecay (fun i => by
        dsimp [d])
    · intro i t ht
      have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
      have hlam0 : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
        tensor_lambda_nonneg (I := I) (M := M) i
      have hder := scalarHeatCoeff_iteratedDeriv (I := I) (M := M) g
        (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i t j
      have hsq : (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g
            (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s) t) ^ 2 =
          TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
            Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) * (d i) ^ 2 :=
        scalarHeatCoeff_deriv_sq (I := I) (M := M) g
          (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i t j
      have hle1 : TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
            Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) := by
        have hpow : TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) ≤
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) := by
          calc
            TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j)
                ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) :=
                  pow_le_pow_left₀ hlam0 (by linarith) (2 * j)
            _ ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) := by
                  exact pow_le_pow_right₀ (by linarith) (by omega)
        have hexp : Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith)
        calc
          TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
              Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t))
              ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) := by
                exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) := by
                rw [mul_comm]
                exact mul_le_of_le_one_left (by positivity) hexp
      have hw : tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) =
          tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (2 * (j + 1) : ℕ)) := by
        unfold tensorSobolevWeight
        rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i)
          (2 * (j + 1) : ℕ)]
        rw [← Real.rpow_add (by linarith [hlam0] : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i)]
      calc
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (fun s : ℝ => scalarHeatCoeff (I := I) (M := M) g
              (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s) t) ^ 2
            = tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                (TensorEigenIdx.lambda (I := I) (M := M) i ^ (2 * j) *
                  Real.exp (-(2 * TensorEigenIdx.lambda (I := I) (M := M) i * t)) * (d i) ^ 2) := by
              rw [hsq]
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
              ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * (j + 1) : ℕ) * (d i) ^ 2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hle1 (sq_nonneg _))
                (tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ))
        _ = tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (2 * (j + 1) : ℕ)) * (d i) ^ 2 := by
              rw [← mul_assoc]
              rw [hw]
  simpa using (scalar_path_recon (I := I) (M := M) g htail hT N
    (fun i s => scalarHeatCoeff (I := I) (M := M) g
      (SmoothCcTensor.toL2 (scalarCcLift g u₀)) i s)
    (U := Set.univ) isOpen_univ hU hc hmass)

theorem scalarHeatFlowTensor_smoothInitial_strict_pos
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hpos0 : ∀ x : M, 0 < u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 < scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t x := by
  classical
  have hmin : ∃ c : ℝ, 0 < c ∧ ∀ x : M, c ≤ u₀.toFun x := by
    have hcont : Continuous u₀.toFun := u₀.smooth.continuous
    by_cases hM : Nonempty M
    · let x₀ : M := Classical.choice hM
      have hmin' : ∃ x : M, ∀ y : M, u₀.toFun x ≤ u₀.toFun y := by
        refine hcont.exists_forall_le' x₀ ?_
        simp [Filter.cocompact_eq_bot]
      let xm : M := Classical.choose hmin'
      exact ⟨u₀.toFun xm, hpos0 xm, Classical.choose_spec hmin'⟩
    · haveI : IsEmpty M := not_nonempty_iff.mp hM
      exact ⟨(1 : ℝ), zero_lt_one, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨c₀, hc₀, hc₀_le⟩ := hmin
  have hconst : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g (fun _ _ => c₀) := by
    change DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 T hT) (stationaryMetricFamily g)
      (fun _ _ => (0 : ℝ)) (fun _ _ => c₀)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact contMDiffOn_const
    · exact continuousOn_const
    · intro t ht
      exact contMDiff_const
    · intro t ht x
      have hd : HasDerivAt (fun s : ℝ => c₀) (0 : ℝ) t :=
        hasDerivAt_const (c := c₀) (x := t)
      refine hd.congr_deriv ?_
      have hlap : laplacianAt (I := I) (stationaryMetricFamily g) t
          (fun _ : M => c₀) x = 0 := by
        unfold laplacianAt stationaryMetricFamily
        exact laplacian_const (I := I) (LeviCivita (I := I) g) g c₀ x
      rw [hlap]
      simp
  have hcomp := DifferentialGeometry.Analysis.Parabolic.heat_comparison
    (I := I) (stationaryMetricFamily g) hT (fun _ _ => c₀)
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    hconst (scalarHeatFlowTensor_isHeatOnStationary_smoothInitial (I := I) (M := M) g u₀ htail hT)
    (fun x => by
      rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x]
      exact hc₀_le x)
  intro t ht x
  exact lt_of_lt_of_le hc₀ (hcomp t ht x)

theorem scalarHeatFlowTensor_smoothInitial_strict_pos_of_nonzero
    [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hpos0 : ∀ x : M, 0 ≤ u₀.toFun x)
    {c : M} (hc : 0 < u₀.toFun c)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (y : M) :
    0 < scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) t y := by
  classical
  have hu := scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g u₀ htail hT
  have ht0 : 0 < t := (Set.mem_Ioo.mp ht).1
  let D : RealTimeInterval := RealTimeInterval.closed (-1) (t + 1) (by linarith : -1 ≤ t + 1)
  have hG : MetricFamilySmoothOn (I := I) (M := M) D ((stationaryMetricFamily g).restrict D) :=
    metricFamilySmoothOn_stationary (I := I) (M := M) g D
  have hslab : Set.Icc 0 t ⊆ D.regular := by
    intro s hs
    dsimp [D]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hconn : ∀ s ∈ Set.Icc 0 t,
      (stationaryMetricFamily g).connection s = LeviCivita (I := I)
        ((stationaryMetricFamily g).metric s) := by
    intro s hs
    rfl
  exact DifferentialGeometry.Analysis.Parabolic.heat_pos_of_initial_pos_of_metricFamilySmoothOn
    (I := I) (stationaryMetricFamily g) hT
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    hu
    (fun x => by
      rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x]
      exact hpos0 x)
    (by
      rw [scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ c]
      exact hc)
    ht hG hslab hconn y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem scalarHeatFlowTensor_smoothInitial_one_point_harnack_of_nonnegative_ricci
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (hpos0 : ∀ x : M, 0 < u₀.toFun x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : M) :
    scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) a x ≤
      (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) b x := by
  classical
  have hb0 : 0 ≤ b := le_trans ha.le hab
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hb1 : 0 ≤ b + 1 := by linarith
  have hb1pos : 0 < b + 1 := by linarith
  have hu := scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g u₀ htail hb1
  have huClosed := scalarHeatFlowTensor_smoothInitial_contMDiffOn_closed
    (I := I) (M := M) g u₀ htail hb1pos
  have hpos := scalarHeatFlowTensor_smoothInitial_strict_pos
    (I := I) (M := M) g u₀ htail hb1 hpos0
  exact DifferentialGeometry.Analysis.Parabolic.Harnack.heat_solution_one_point_harnack_of_nonnegative_ricci_on
    (I := I) (M := M) g hRic (RealTimeInterval.closed 0 (b + 1) hb1)
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    hu huClosed hpos ha hab
    (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
    (fun t ht => ⟨ht.1, le_trans ht.2 (by linarith)⟩)
    (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith)⟩) x

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem scalarHeatFlowTensor_smoothInitial_harnack_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (htail : EigenvalueTailSummable g 0 0)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (hpos0 : ∀ x : M, 0 < u₀.toFun x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x y : M) :
    scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) a x ≤
      (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a))) *
        scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) b y := by
  classical
  have hb1 : 0 ≤ b + 1 := by linarith
  have hb1pos : 0 < b + 1 := by linarith
  have hu := scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g u₀ htail hb1
  have huClosed := scalarHeatFlowTensor_smoothInitial_contMDiffOn_closed
    (I := I) (M := M) g u₀ htail hb1pos
  have hpos := scalarHeatFlowTensor_smoothInitial_strict_pos
    (I := I) (M := M) g u₀ htail hb1 hpos0
  exact DifferentialGeometry.Analysis.Parabolic.Harnack.heat_solution_harnack_of_nonnegative_ricci_on
    (I := I) (M := M) g hEnorm hRic (RealTimeInterval.closed 0 (b + 1) hb1)
    (scalarHeatFlowTensor g (SmoothCcTensor.toL2 (scalarCcLift g u₀)))
    hu huClosed hpos ha hab
    (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
    (fun t ht => ⟨ht.1, le_trans ht.2 (by linarith)⟩)
    (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith)⟩) x y

private noncomputable def scalarConst
    (g : SmoothRiemannianMetric I M) (δ : ℝ) : SmoothScalar g :=
  ⟨fun _ => δ, contMDiff_const⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensor00ScalarL2Equiv_symm_smoothToLp
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g) :
    (tensor00ScalarL2Equiv g).symm (smoothToLp (I := I) (M := M) g u₀) =
      SmoothCcTensor.toL2 (scalarCcLift g u₀) := by
  have hU0 : (tensor00ScalarL2Equiv g) (SmoothCcTensor.toL2 (scalarCcLift g u₀)) =
      smoothToLp (I := I) (M := M) g u₀ := by
    change tensor00ToScalarL2 g (SmoothCcTensor.toL2 (scalarCcLift g u₀)) =
      smoothToLp (I := I) (M := M) g u₀
    rw [tensor00ToScalarL2_toL2]
    exact scalar0ToLp_scalarCcLift (I := I) (M := M) g u₀
  simpa using congrArg (tensor00ScalarL2Equiv g).symm hU0.symm

theorem scalarHeatFlow_smoothInitial_zero_apply
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g) (x : M) :
    scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) 0 x = u₀.toFun x := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
      (smoothToLp (I := I) (M := M) g u₀)) 0 x = u₀.toFun x
  rw [hU]
  exact scalarHeatFlowTensor_zero_apply (I := I) (M := M) g u₀ x

theorem scalarHeatFlow_isHeatOnStationary_smoothInitial
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g
      (scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀)) := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
    (RealTimeInterval.closed 0 T hT) g
    (scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
      (smoothToLp (I := I) (M := M) g u₀)))
  rw [hU]
  exact scalarHeatFlowTensor_isHeatOnStationary_smoothInitial
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) hT

theorem scalarHeatFlow_smoothInitial_slice_contMDiff
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    have hf : (fun x : M =>
        scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) 0 x) =
        u₀.toFun := by
      funext x
      exact scalarHeatFlow_smoothInitial_zero_apply (I := I) (M := M) g u₀ x
    rw [hf]
    exact u₀.smooth
  · have htpos : 0 < t := lt_of_le_of_ne (Set.mem_Icc.mp ht).1 (Ne.symm ht0)
    have hε : 0 < t / 2 := half_pos htpos
    have hεT : t / 2 < T := lt_of_lt_of_le (half_lt_self htpos) (Set.mem_Icc.mp ht).2
    have ht' : t ∈ Set.Icc (t / 2) T :=
      Set.mem_Icc.mpr ⟨(half_lt_self htpos).le, (Set.mem_Icc.mp ht).2⟩
    exact scalarHeatFlow_slice_contMDiff (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u₀) hεT hε ht'

noncomputable def scalarHeatFlowSmoothInitialSlice
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) : SmoothScalar g :=
  ⟨fun x => scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x,
    scalarHeatFlow_smoothInitial_slice_contMDiff (I := I) (M := M) g u₀ ht⟩

theorem scalarHeatFlowSmoothInitialSlice_toL2_eq_heatSemigroup
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    smoothToLp (I := I) (M := M) g (scalarHeatFlowSmoothInitialSlice g u₀ ht) =
      heatSemigroup (I := I) (M := M) g t (smoothToLp (I := I) (M := M) g u₀) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    rw [show heatSemigroup (I := I) (M := M) g 0 (smoothToLp (I := I) (M := M) g u₀) =
        smoothToLp (I := I) (M := M) g u₀ by simp]
    exact congrArg (smoothToLp (I := I) (M := M) g) (by
      apply SmoothScalar.ext
      funext x
      dsimp [scalarHeatFlowSmoothInitialSlice]
      exact scalarHeatFlow_smoothInitial_zero_apply (I := I) (M := M) g u₀ x)
  · have htpos : 0 < t := lt_of_le_of_ne (Set.mem_Icc.mp ht).1 (Ne.symm ht0)
    have hε : 0 < t / 2 := half_pos htpos
    have hεT : t / 2 < T := lt_of_lt_of_le (half_lt_self htpos) (Set.mem_Icc.mp ht).2
    have ht' : t ∈ Set.Icc (t / 2) T :=
      Set.mem_Icc.mpr ⟨(half_lt_self htpos).le, (Set.mem_Icc.mp ht).2⟩
    have hslice := scalarHeatFlowSlice_toL2_eq_heatSemigroup (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u₀) hεT hε ht'
    have hsame : scalarHeatFlowSmoothInitialSlice g u₀ ht =
        scalarHeatFlowSlice g (smoothToLp (I := I) (M := M) g u₀) hεT hε ht' := by
      apply SmoothScalar.ext
      rfl
    rw [hsame]
    exact hslice

theorem scalarHeatFlow_smoothInitial_restrict_eq
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T ε : ℝ} (hε0 : 0 < ε) (hεT : ε < T)
    {t : ℝ} (ht : t ∈ Set.Icc ε T) :
    scalarHeatFlowSmoothInitialSlice g u₀
        (Set.mem_Icc.mpr ⟨le_trans hε0.le (Set.mem_Icc.mp ht).1, (Set.mem_Icc.mp ht).2⟩) =
      scalarHeatFlowSlice g (smoothToLp (I := I) (M := M) g u₀) hεT hε0 ht := by
  apply SmoothScalar.ext
  rfl

theorem scalarHeatFlow_smoothInitial_unique
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T)
    (v : ℝ → M → ℝ)
    (hv : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary
      (RealTimeInterval.closed 0 T hT) g v)
    (hinit : ∀ x : M, v 0 x = u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      v t x = scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x := by
  have h := scalarHeatFlowTensor_smoothInitial_unique (I := I) (M := M) g u₀
    (scalar_eigen_tail (I := I) (M := M) g) hT v hv hinit
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  intro t ht x
  change v t x = scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
      (smoothToLp (I := I) (M := M) g u₀)) t x
  rw [hU]
  exact h t ht x

theorem scalarHeatFlow_smoothInitial_comparison
    (g : SmoothRiemannianMetric I M) (u₀ v₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ x : M, u₀.toFun x ≤ v₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x ≤
        scalarHeatFlow g (smoothToLp (I := I) (M := M) g v₀) t x := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  have hV := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g v₀
  change ∀ t ∈ Set.Icc 0 T, ∀ x : M,
    scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
        (smoothToLp (I := I) (M := M) g u₀)) t x ≤
      scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
        (smoothToLp (I := I) (M := M) g v₀)) t x
  rw [hU, hV]
  exact scalarHeatFlowTensor_smoothInitial_comparison
    (I := I) (M := M) g u₀ v₀ (scalar_eigen_tail (I := I) (M := M) g) hT hinit

theorem scalarHeatFlow_smoothInitial_nonneg
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ x : M, 0 ≤ u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 ≤ scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change ∀ t ∈ Set.Icc 0 T, ∀ x : M,
    0 ≤ scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
        (smoothToLp (I := I) (M := M) g u₀)) t x
  rw [hU]
  exact scalarHeatFlowTensor_smoothInitial_nonneg
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) hT hinit

theorem scalarHeatFlow_smoothInitial_mass_invariant
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (∫ x, scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, u₀.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change (∫ x, scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
        (smoothToLp (I := I) (M := M) g u₀)) t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, u₀.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
  rw [hU]
  exact scalarHeatFlowTensor_smoothInitial_mass_invariant
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) ht

theorem scalarHeatFlow_smoothInitial_contMDiffOn_closed
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 < T) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun q : ℝ × M => scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
      (smoothToLp (I := I) (M := M) g u₀)) q.1 q.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  rw [hU]
  exact scalarHeatFlowTensor_smoothInitial_contMDiffOn_closed
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) hT

theorem scalarHeatFlow_smoothInitial_strict_pos
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T)
    (hpos0 : ∀ x : M, 0 < u₀.toFun x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 < scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change ∀ t ∈ Set.Icc 0 T, ∀ x : M,
    0 < scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
        (smoothToLp (I := I) (M := M) g u₀)) t x
  rw [hU]
  exact scalarHeatFlowTensor_smoothInitial_strict_pos
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) hT hpos0

theorem scalarHeatFlow_smoothInitial_strict_pos_of_nonzero
    [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T)
    (hpos0 : ∀ x : M, 0 ≤ u₀.toFun x)
    {c : M} (hc : 0 < u₀.toFun c)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (y : M) :
    0 < scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t y := by
  have hU := tensor00ScalarL2Equiv_symm_smoothToLp (I := I) (M := M) g u₀
  change 0 < scalarHeatFlowTensor g ((tensor00ScalarL2Equiv g).symm
      (smoothToLp (I := I) (M := M) g u₀)) t y
  rw [hU]
  exact scalarHeatFlowTensor_smoothInitial_strict_pos_of_nonzero
    (I := I) (M := M) g u₀ (scalar_eigen_tail (I := I) (M := M) g) hT hpos0 hc ht y

theorem scalarHeatFlow_smoothInitial_shift_const
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M) :
    scalarHeatFlow g (smoothToLp (I := I) (M := M) g (u₀ + scalarConst g δ)) t x =
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) t x + δ := by
  classical
  let D : RealTimeInterval := RealTimeInterval.closed 0 T hT
  let u : ℝ → M → ℝ := scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀)
  let v : ℝ → M → ℝ := fun s y => u s y + δ
  have hu : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary D g u := by
    simpa [u, D] using scalarHeatFlow_isHeatOnStationary_smoothInitial
      (I := I) (M := M) g u₀ hT
  have hv : DifferentialGeometry.Analysis.Parabolic.IsHeatOnStationary D g v := by
    change DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn D (stationaryMetricFamily g)
      (fun _ _ => (0 : ℝ)) v
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hjoint := hu.jointSmooth
      simpa [v, D] using hjoint.add
        (contMDiffOn_const : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun _ : ℝ × M => δ) (D.regular ×ˢ Set.univ))
    · have hcont := hu.jointCont
      simpa [v, D] using hcont.add
        (continuousOn_const : ContinuousOn (fun _ : ℝ × M => δ) (D.carrier ×ˢ Set.univ))
    · intro s hs
      have hslicem := hu.sliceSmooth s hs
      exact hslicem.add (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => δ))
    · intro s hs x
      have hder := (hu.equation s hs x).add (hasDerivAt_const (c := δ) (x := s))
      refine hder.congr_deriv ?_
      have hlap : laplacianAt (I := I) (stationaryMetricFamily g) s
          (fun y : M => u s y + δ) x = laplacianAt (I := I) (stationaryMetricFamily g) s (u s) x := by
        have hsub := heatOperatorWithDrift_sub_const (I := I)
          (G := stationaryMetricFamily g) s (fun y : M => (0 : TangentSpace I y))
          (f := u s) (-δ)
          (fun y => (hu.sliceSmooth s (D.regular_subset hs)).mdifferentiable (by simp) y) x
        have hfun : (fun y : M => u s y - (-δ)) = fun y : M => u s y + δ := by
          funext y
          ring
        rw [hfun] at hsub
        simpa [heatOperatorWithDrift, driftTerm_zero_drift] using hsub
      change laplacianAt (I := I) (stationaryMetricFamily g) s (u s) x + 0 * u s x + 0 =
        laplacianAt (I := I) (stationaryMetricFamily g) s (fun y : M => u s y + δ) x +
          0 * (u s x + δ)
      rw [hlap]
      simp [zero_mul, add_zero]
  have hinit : ∀ y : M, v 0 y = (u₀ + scalarConst g δ).toFun y := by
    intro y
    change scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) 0 y + δ =
      (u₀ + scalarConst g δ).toFun y
    rw [scalarHeatFlow_smoothInitial_zero_apply (I := I) (M := M) g u₀ y]
    simp [scalarConst]
  have heq := scalarHeatFlow_smoothInitial_unique (I := I) (M := M) g
    (u₀ + scalarConst g δ) hT v hv hinit
  have hmain := heq t ht x
  simpa [v, u] using hmain.symm

private lemma le_of_forall_pos_lt_add
    {u v : ℝ} {C : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → u + δ ≤ C * (v + δ)) :
    u ≤ C * v := by
  by_contra hnot
  have hpos : 0 < u - C * v := sub_pos.mpr (not_le.mp hnot)
  rcases le_or_gt C 1 with hC1 | hC1
  · have hle := h (u - C * v) hpos
    nlinarith
  · have hc1' : 0 < C - 1 := sub_pos.mpr hC1
    let δ : ℝ := (u - C * v) / (2 * (C - 1))
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact div_pos hpos (mul_pos (by norm_num) hc1')
    have hle := h δ hδ0
    have hd : u - C * v ≤ (C - 1) * δ := by
      nlinarith [hle]
    have hδeq : (C - 1) * δ = (u - C * v) / 2 := by
      dsimp [δ]
      field_simp [hc1'.ne']
    have hd' : u - C * v ≤ (u - C * v) / 2 := by
      rw [hδeq] at hd
      exact hd
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem scalarHeatFlow_smoothInitial_one_point_harnack_of_nonnegative_ricci
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (hpos0 : ∀ x : M, 0 ≤ u₀.toFun x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : M) :
    scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) a x ≤
      (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) b x := by
  classical
  have hb1 : 0 ≤ b + 1 := by linarith
  have hb1pos : 0 < b + 1 := by linarith
  let C : ℝ := (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2)
  have hle_all : ∀ δ : ℝ, 0 < δ →
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) a x + δ ≤
        C * (scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) b x + δ) := by
    intro δ hδ
    let uδ : ℝ → M → ℝ :=
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g (u₀ + scalarConst g δ))
    have hposδ0 : ∀ y : M, 0 < (u₀ + scalarConst g δ).toFun y := by
      intro y
      simp [scalarConst]
      linarith [hpos0 y, hδ]
    have huδ := scalarHeatFlow_isHeatOnStationary_smoothInitial (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1
    have huδClosed := scalarHeatFlow_smoothInitial_contMDiffOn_closed (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1pos
    have hposδ := scalarHeatFlow_smoothInitial_strict_pos (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1 hposδ0
    have hharnack := DifferentialGeometry.Analysis.Parabolic.Harnack.heat_solution_one_point_harnack_of_nonnegative_ricci_on
      (I := I) (M := M) g hRic (RealTimeInterval.closed 0 (b + 1) hb1) uδ
      huδ huδClosed
      (fun t ht x => hposδ t ht x)
      ha hab
      (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
      (fun t ht => ⟨ht.1, le_trans ht.2 (by linarith)⟩)
      (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith)⟩) x
    have hshift_a := scalarHeatFlow_smoothInitial_shift_const (I := I) (M := M) g u₀ hb1 δ
      (Set.mem_Icc.mpr ⟨le_of_lt ha, by linarith⟩) x
    have hshift_b := scalarHeatFlow_smoothInitial_shift_const (I := I) (M := M) g u₀ hb1 δ
      (Set.mem_Icc.mpr ⟨le_trans ha.le hab, by linarith⟩) x
    rw [← hshift_a, ← hshift_b]
    simpa [uδ] using hharnack
  simpa [C] using le_of_forall_pos_lt_add hle_all

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem scalarHeatFlow_smoothInitial_harnack_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothScalar g)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (hpos0 : ∀ x : M, 0 ≤ u₀.toFun x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x y : M) :
    scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) a x ≤
      (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a))) *
        scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) b y := by
  classical
  have hb1 : 0 ≤ b + 1 := by linarith
  have hb1pos : 0 < b + 1 := by linarith
  let C : ℝ := (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
    Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a)))
  have hle_all : ∀ δ : ℝ, 0 < δ →
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) a x + δ ≤
        C * (scalarHeatFlow g (smoothToLp (I := I) (M := M) g u₀) b y + δ) := by
    intro δ hδ
    let uδ : ℝ → M → ℝ :=
      scalarHeatFlow g (smoothToLp (I := I) (M := M) g (u₀ + scalarConst g δ))
    have hposδ0 : ∀ y : M, 0 < (u₀ + scalarConst g δ).toFun y := by
      intro y
      simp [scalarConst]
      linarith [hpos0 y, hδ]
    have huδ := scalarHeatFlow_isHeatOnStationary_smoothInitial (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1
    have huδClosed := scalarHeatFlow_smoothInitial_contMDiffOn_closed (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1pos
    have hposδ := scalarHeatFlow_smoothInitial_strict_pos (I := I) (M := M) g
      (u₀ + scalarConst g δ) hb1 hposδ0
    have hharnack := DifferentialGeometry.Analysis.Parabolic.Harnack.heat_solution_harnack_of_nonnegative_ricci_on
      (I := I) (M := M) g hEnorm hRic (RealTimeInterval.closed 0 (b + 1) hb1) uδ
      huδ huδClosed
      (fun t ht x => hposδ t ht x)
      ha hab
      (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
      (fun t ht => ⟨ht.1, le_trans ht.2 (by linarith)⟩)
      (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith)⟩) x y
    have hshift_a := scalarHeatFlow_smoothInitial_shift_const (I := I) (M := M) g u₀ hb1 δ
      (Set.mem_Icc.mpr ⟨le_of_lt ha, by linarith⟩) x
    have hshift_b := scalarHeatFlow_smoothInitial_shift_const (I := I) (M := M) g u₀ hb1 δ
      (Set.mem_Icc.mpr ⟨le_trans ha.le (le_of_lt hab), by linarith⟩) y
    rw [← hshift_a, ← hshift_b]
    simpa [uδ] using hharnack
  simpa [C] using le_of_forall_pos_lt_add hle_all

end HeatEquation
end Analysis
end DifferentialGeometry

end
