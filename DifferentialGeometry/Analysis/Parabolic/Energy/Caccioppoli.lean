import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Geometry.Operator.NormGradSq


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

def smoothScalarSlice (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) : SmoothScalar g where
  toFun := fun x => u t x
  smooth := hu.comp (contMDiff_const.prodMk contMDiff_id)

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] in
@[simp] lemma smoothScalarSlice_toFun
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) (x : M) :
    (smoothScalarSlice (I := I) g u hu t).toFun x = u t x := rfl

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

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedL2Mass_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ localizedL2Mass (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedDirichletEnergy_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ localizedDirichletEnergy (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) g x _))

omit [I.Boundaryless] [CompactSpace M] in
theorem cutoffGradientError_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ cutoffGradientError (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) g x _))

omit [I.Boundaryless] in
theorem contDiff_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContDiff ℝ ∞
      (fun t => localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1 ^ 2) :=
    (hcutoff_joint.pow 2).mul (hu_swap.pow 2)
  simpa only [localizedL2Mass, smoothScalarSlice, μ] using
    contDiff_integral_of_jointContMDiff μ
      (fun x t => cutoff.toFun x ^ 2 * u t x ^ 2) hintegrand

omit [I.Boundaryless] in
theorem hasDerivAt_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) :
    HasDerivAt
      (fun s => localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu s))
      (∫ x, 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) t := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1 ^ 2) :=
    (hcutoff_joint.pow 2).mul (hu_swap.pow 2)
  have hraw := hasDerivAt_integral_of_jointContMDiff μ
    (fun x s => cutoff.toFun x ^ 2 * u s x ^ 2) hintegrand t
  have hderiv : ∀ x : M,
      deriv (fun s => cutoff.toFun x ^ 2 * u s x ^ 2) t =
        2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t := by
    intro x
    have hfiber : ContDiff ℝ ∞ (fun s : ℝ => u s x) :=
      contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
    have hu_at : HasDerivAt (fun s : ℝ => u s x) (deriv (fun s : ℝ => u s x) t) t :=
      (hfiber.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hproduct := (hasDerivAt_const t (cutoff.toFun x ^ 2)).mul (hu_at.pow 2)
    have heq : HasDerivAt (fun s => cutoff.toFun x ^ 2 * u s x ^ 2)
        (2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t) t := by
      convert hproduct using 1
      all_goals ring
    exact heq.deriv
  convert hraw using 1
  simpa only [μ] using (integral_congr_ae (ae_of_all μ hderiv)).symm

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

theorem caccioppoli_differential
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (t : ℝ)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x) :
    deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ut := smoothScalarSlice (I := I) g u hu t
  let ft := smoothScalarSlice (I := I) g source hsource t
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hlap_cont : Continuous (fun x : M =>
      Δ_g (I := I) g ut.smooth x) :=
    (Δ_g_contMDiff (I := I) g ut.smooth).continuous
  have hcoeff_cont : Continuous (fun x : M => 2 * cutoff.toFun x ^ 2 * u t x) :=
    (continuous_const.mul (cutoff.smooth.continuous.pow 2)).mul ut.smooth.continuous
  have hsource_cont : Continuous (fun x : M => source t x) := ft.smooth.continuous
  have hlap_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ut.smooth x) μ :=
    (hcoeff_cont.mul hlap_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsource_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * source t x) μ :=
    (hcoeff_cont.mul hsource_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t ∂μ =
        (∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ut.smooth x ∂μ) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ := by
    rw [← integral_add hlap_int hsource_int]
    apply integral_congr_ae
    refine ae_of_all μ (fun x => ?_)
    change 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t =
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ut.smooth x +
        2 * cutoff.toFun x ^ 2 * u t x * source t x
    rw [hpde x]
    ring
  have hmass := hasDerivAt_localizedL2Mass
    (I := I) (M := M) cutoff u hu t
  have hspatial := caccioppoli_spatial
    (I := I) (M := M) cutoff ut
  change deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
      localizedDirichletEnergy (I := I) (M := M) cutoff ut ≤
    4 * cutoffGradientError (I := I) (M := M) cutoff ut +
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ
  have hlap_scale :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ut.smooth x ∂μ =
        2 * ∫ x, cutoff.toFun x ^ 2 * ut.toFun x *
          Δ_g (I := I) g ut.smooth x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all μ (fun x => ?_)
    change 2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ut.smooth x =
      2 * (cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ut.smooth x)
    ring
  rw [hmass.deriv, hsplit]
  rw [hlap_scale]
  linarith

theorem caccioppoli
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b))
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let dirichlet : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let forcing : ℝ → ℝ := fun t =>
    ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using
      contDiff_localizedL2Mass (I := I) (M := M) cutoff u hu
  have hmass_cont : ContinuousOn mass (Icc a b) := hmass_smooth.continuous.continuousOn
  have hdmass_cont : ContinuousOn (deriv mass) (Icc a b) :=
    (hmass_smooth.continuous_deriv (by simp)).continuousOn
  have hmass_deriv : ∀ t ∈ Icc a b, HasDerivAt mass (deriv mass t) t := by
    intro t _
    exact (hmass_smooth.differentiable (by simp) t).hasDerivAt
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hcutoff_grad_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g cutoff.smooth) (grad_g (I := I) g cutoff.smooth)
    simpa only [grad_g_apply] using h
  have hcutoff_grad_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    hcutoff_grad_smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hsource_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => source p.2 p.1) :=
    hsource.comp (contMDiff_snd.prodMk contMDiff_fst)
  have herror_integrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1 ^ 2 *
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    (hu_swap.pow 2).mul hcutoff_grad_joint
  have herror_cont : ContinuousOn error (Icc a b) := by
    have hsmooth := contDiff_integral_of_jointContMDiff μ
      (fun x t => u t x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) herror_integrand
    exact (by simpa only [error, cutoffGradientError, smoothScalarSlice, μ]
      using hsmooth.continuous.continuousOn)
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hforcing_integrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        2 * cutoff.toFun p.1 ^ 2 * u p.2 p.1 * source p.2 p.1) :=
    ((contMDiff_const.mul (hcutoff_joint.pow 2)).mul hu_swap).mul hsource_swap
  have hforcing_cont : ContinuousOn forcing (Icc a b) := by
    have hsmooth := contDiff_integral_of_jointContMDiff μ
      (fun x t => 2 * cutoff.toFun x ^ 2 * u t x * source t x) hforcing_integrand
    exact (by simpa only [forcing] using hsmooth.continuous.continuousOn)
  have hdissipation : ContinuousOn (fun t => weight t * dirichlet t) (Icc a b) :=
    hweight_cont.mul (by simpa only [dirichlet] using hdirichlet)
  have hrhs : ContinuousOn
      (fun t => dweight t * mass t + weight t * (4 * error t + forcing t))
      (Icc a b) :=
    (hdweight.mul hmass_cont).add
      (hweight_cont.mul ((continuousOn_const.mul herror_cont).add hforcing_cont))
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * mass t + weight t * deriv mass t + weight t * dirichlet t ≤
        dweight t * mass t + weight t * (4 * error t + forcing t) := by
    intro t ht
    have hdiff := caccioppoli_differential
      (I := I) (M := M) cutoff u source hu hsource t (hpde t ht)
    have hmul := mul_le_mul_of_nonneg_left hdiff (hweight_nonneg t ht)
    change weight t * (deriv mass t + dirichlet t) ≤
      weight t * (4 * error t + forcing t) at hmul
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdmass_cont hmass_deriv hdissipation hrhs hpointwise
  simpa only [mass, dirichlet, error, forcing, μ] using hresult

end DifferentialGeometry.Analysis.Parabolic.Energy

end
