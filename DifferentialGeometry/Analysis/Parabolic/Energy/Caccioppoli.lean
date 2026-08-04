import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import DifferentialGeometry.Geometry.Metric.MetricBounds


noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Energy

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def localizedL2Mass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 * u.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedDirichletEnergy {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def cutoffGradientError {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, u.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma neg_four_mul_inner_grad_le
    (g : SmoothRiemannianMetric I M) (cutoff u : SmoothScalar g) (x : M) :
    -4 * (cutoff.toFun x * u.toFun x *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g u.toFun x)) ≤
      cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) +
        4 * (u.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x)) := by
  have hnonneg := metric_inner_self_nonneg (I := I) (M := M) g x
    (cutoff.toFun x • gradFun (I := I) g u.toFun x +
      (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x)
  have hexpand :
      g.inner x
          (cutoff.toFun x • gradFun (I := I) g u.toFun x +
            (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x)
          (cutoff.toFun x • gradFun (I := I) g u.toFun x +
            (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x) =
        cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g u.toFun x)
              (gradFun (I := I) g u.toFun x) +
          4 * (cutoff.toFun x * u.toFun x *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g u.toFun x)) +
          4 * (u.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g cutoff.toFun x)) := by
    simp only [map_add, ContinuousLinearMap.add_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm x
      (gradFun (I := I) g u.toFun x)
      (gradFun (I := I) g cutoff.toFun x)]
    ring
  rw [hexpand] at hnonneg
  linarith

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma gradFun_sq_mul
    (g : SmoothRiemannianMetric I M) (cutoff u : SmoothScalar g) (x : M) :
    gradFun (I := I) g
        (fun y : M => cutoff.toFun y ^ 2 * u.toFun y) x =
      cutoff.toFun x ^ 2 • gradFun (I := I) g u.toFun x +
        (2 * cutoff.toFun x * u.toFun x) •
          gradFun (I := I) g cutoff.toFun x := by
  change gradientFun (I := I) g
      (fun y : M => cutoff.toFun y ^ 2 * u.toFun y) x = _
  rw [gradientFun_mul (I := I) (f := fun y : M => cutoff.toFun y ^ 2)
    (h := u.toFun) g
    ((cutoff.smooth.mdifferentiable (by simp) x).pow 2)
    (u.smooth.mdifferentiable (by simp) x)]
  rw [gradientFun_pow (I := I) g 1
    (cutoff.smooth.mdifferentiable (by simp) x)]
  rw [smul_smul]
  congr 1
  ring_nf
  rfl

theorem caccioppoli_spatial
    {g : SmoothRiemannianMetric I M} (cutoff u : SmoothScalar g) :
    localizedDirichletEnergy (I := I) (M := M) cutoff u ≤
      -2 * ∫ x, cutoff.toFun x ^ 2 * u.toFun x *
          Δ_g (I := I) g u.smooth x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      4 * cutoffGradientError (I := I) (M := M) cutoff u := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let test : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x ^ 2 * u.toFun x,
      (cutoff.smooth.pow 2).mul u.smooth⟩
  have hgrad_u : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x)) := by
    simpa only [grad_g_apply] using u.continuous_inner_grad u
  have hgrad_cutoff : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    simpa only [grad_g_apply] using cutoff.continuous_inner_grad cutoff
  have hgrad_cross : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g u.toFun x)) := by
    simpa only [grad_g_apply] using cutoff.continuous_inner_grad u
  have hD_cont : Continuous (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) :=
    (cutoff.smooth.continuous.pow 2).mul hgrad_u
  have hE_cont : Continuous (fun x : M =>
      u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) :=
    (u.smooth.continuous.pow 2).mul hgrad_cutoff
  have hC_cont : Continuous (fun x : M =>
      cutoff.toFun x * u.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g u.toFun x)) :=
    (cutoff.smooth.continuous.mul u.smooth.continuous).mul hgrad_cross
  have hD_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) μ :=
    hD_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE_int : Integrable (fun x : M =>
      u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) μ :=
    hE_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hC_int : Integrable (fun x : M =>
      cutoff.toFun x * u.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g u.toFun x)) μ :=
    hC_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgreen :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g test.smooth u.smooth (HasCompactSupport.of_compactSpace _)
  have htest_pointwise : ∀ x : M,
      g.inner x
          ((grad_g (I := I) g test.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g u.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g u.toFun x)
              (gradFun (I := I) g u.toFun x) +
          2 * (cutoff.toFun x * u.toFun x *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g u.toFun x)) := by
    intro x
    rw [grad_g_apply, grad_g_apply]
    change g.inner x
        (gradFun (I := I) g
          (fun y : M => cutoff.toFun y ^ 2 * u.toFun y) x)
        (gradFun (I := I) g u.toFun x) = _
    rw [gradFun_sq_mul (I := I) (M := M) g cutoff u x]
    simp only [map_add, ContinuousLinearMap.add_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hidentity :
      (∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ) +
        2 * ∫ x, cutoff.toFun x * u.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ =
        -∫ x, cutoff.toFun x ^ 2 * u.toFun x *
          Δ_g (I := I) g u.smooth x ∂μ := by
    rw [← integral_const_mul]
    rw [← integral_add hD_int (hC_int.const_mul 2)]
    rw [← integral_congr_ae (ae_of_all μ htest_pointwise)]
    simpa [μ, test] using hgreen
  have hcross :
      -4 * ∫ x, cutoff.toFun x * u.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ ≤
        (∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ) +
        4 * ∫ x, u.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x) ∂μ := by
    rw [← integral_const_mul]
    rw [← integral_const_mul]
    rw [← integral_add hD_int (hE_int.const_mul 4)]
    exact integral_mono (hC_int.const_mul (-4)) (hD_int.add (hE_int.const_mul 4))
      (fun x => neg_four_mul_inner_grad_le (I := I) (M := M) g cutoff u x)
  change (∫ x, cutoff.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x) ∂μ) ≤
    -2 * ∫ x, cutoff.toFun x ^ 2 * u.toFun x *
      Δ_g (I := I) g u.smooth x ∂μ +
    4 * ∫ x, u.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x) ∂μ
  linarith

end DifferentialGeometry.Analysis.Parabolic.Energy

end
