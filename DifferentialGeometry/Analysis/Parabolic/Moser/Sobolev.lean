import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Analysis.Sobolev.Manifold.IntrinsicEmbedding


noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] in
private theorem metric_inner_add_self_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (v + w) (v + w) ≤
      2 * g.inner x v v + 2 * g.inner x w w := by
  have hminus := metric_inner_self_nonneg (I := I) (M := M) g x (v - w)
  have hparallelogram :
      g.inner x (v + w) (v + w) + g.inner x (v - w) (v - w) =
        2 * g.inner x v v + 2 * g.inner x w w := by
    simp only [map_add, ContinuousLinearMap.add_apply, map_sub,
      ContinuousLinearMap.sub_apply]
    rw [g.symm x w v]
    ring
  linarith

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private theorem inner_grad_mul_self_le
    (g : SmoothRiemannianMetric I M) (cutoff u : SmoothScalar g) (x : M) :
    g.inner x
        (gradFun (I := I) g (fun y => cutoff.toFun y * u.toFun y) x)
        (gradFun (I := I) g (fun y => cutoff.toFun y * u.toFun y) x) ≤
      2 * (cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) +
      2 * (u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) := by
  change g.inner x
      (gradientFun (I := I) g (fun y => cutoff.toFun y * u.toFun y) x)
      (gradientFun (I := I) g (fun y => cutoff.toFun y * u.toFun y) x) ≤ _
  rw [gradientFun_mul (I := I) g
    (cutoff.smooth.mdifferentiable (by simp) x)
    (u.smooth.mdifferentiable (by simp) x)]
  calc
    _ ≤ 2 * g.inner x
          (cutoff.toFun x • gradientFun (I := I) g u.toFun x)
          (cutoff.toFun x • gradientFun (I := I) g u.toFun x) +
        2 * g.inner x
          (u.toFun x • gradientFun (I := I) g cutoff.toFun x)
          (u.toFun x • gradientFun (I := I) g cutoff.toFun x) :=
      metric_inner_add_self_le (I := I) (M := M) g x _ _
    _ = _ := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hgrad_u : gradientFun (I := I) g u.toFun x =
          gradFun (I := I) g u.toFun x := rfl
      have hgrad_cutoff : gradientFun (I := I) g cutoff.toFun x =
          gradFun (I := I) g cutoff.toFun x := rfl
      rw [hgrad_u, hgrad_cutoff]
      ring

theorem localized_sobolev
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ cutoff u : SmoothScalar g,
        lpNorm (fun x => cutoff.toFun x * u.toFun x)
              (ENNReal.ofReal
                ((Module.finrank ℝ E : ℝ) * 2 /
                  ((Module.finrank ℝ E : ℝ) - 2)))
              (riemannianVolumeMeasure (I := I) (M := M) g) ^ 2 ≤
          C * (localizedL2Mass (I := I) (M := M) cutoff u +
            localizedDirichletEnergy (I := I) (M := M) cutoff u +
            cutoffGradientError (I := I) (M := M) cutoff u) := by
  obtain ⟨C, hC, hSob⟩ :=
    DifferentialGeometry.Analysis.Sobolev.sobolev_two_integral
      (I := I) (M := M) g hdim
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro cutoff u
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let v : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x * u.toFun x, cutoff.smooth.mul u.smooth⟩
  have hgrad_v_cont : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)) := by
    simpa only [grad_g_apply] using v.continuous_inner_grad v
  have hD_cont : Continuous (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) := by
    simpa only [grad_g_apply] using
      (cutoff.smooth.continuous.pow 2).mul (u.continuous_inner_grad u)
  have hE_cont : Continuous (fun x : M =>
      u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) := by
    simpa only [grad_g_apply] using
      (u.smooth.continuous.pow 2).mul (cutoff.continuous_inner_grad cutoff)
  have hgrad_v_int := hgrad_v_cont.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hD_int := hD_cont.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hE_int := hE_cont.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hgrad :
      (∫ x, g.inner x
          (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) ∂μ) ≤
        2 * localizedDirichletEnergy (I := I) (M := M) cutoff u +
          2 * cutoffGradientError (I := I) (M := M) cutoff u := by
    calc
      _ ≤ ∫ x,
          2 * (cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g u.toFun x)
              (gradFun (I := I) g u.toFun x)) +
          2 * (u.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g cutoff.toFun x)) ∂μ := by
        exact integral_mono hgrad_v_int
          ((hD_int.const_mul 2).add (hE_int.const_mul 2))
          (fun x => inner_grad_mul_self_le (I := I) (M := M) g cutoff u x)
      _ = _ := by
        rw [integral_add (hD_int.const_mul 2) (hE_int.const_mul 2)]
        rw [integral_const_mul, integral_const_mul]
        rfl
  have hmass :
      (∫ x, v.toFun x ^ 2 ∂μ) =
        localizedL2Mass (I := I) (M := M) cutoff u := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [v]
    ring
  have hbase := hSob v.smooth
  change lpNorm v.toFun
        (ENNReal.ofReal
          ((Module.finrank ℝ E : ℝ) * 2 /
            ((Module.finrank ℝ E : ℝ) - 2))) μ ^ 2 ≤ _ at hbase
  rw [hmass] at hbase
  have hmass_nonneg := localizedL2Mass_nonneg (I := I) (M := M) cutoff u
  calc
    _ ≤ 2 * C ^ 2 *
        (localizedL2Mass (I := I) (M := M) cutoff u +
          ∫ x, g.inner x
            (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x) ∂μ) := hbase
    _ ≤ 2 * C ^ 2 *
        (localizedL2Mass (I := I) (M := M) cutoff u +
          (2 * localizedDirichletEnergy (I := I) (M := M) cutoff u +
            2 * cutoffGradientError (I := I) (M := M) cutoff u)) := by
      gcongr
    _ ≤ 2 * C ^ 2 *
        (2 * (localizedL2Mass (I := I) (M := M) cutoff u +
          localizedDirichletEnergy (I := I) (M := M) cutoff u +
          cutoffGradientError (I := I) (M := M) cutoff u)) := by
      gcongr
      linarith
    _ = 4 * C ^ 2 *
        (localizedL2Mass (I := I) (M := M) cutoff u +
          localizedDirichletEnergy (I := I) (M := M) cutoff u +
          cutoffGradientError (I := I) (M := M) cutoff u) := by ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
