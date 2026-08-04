import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff
import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral
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

omit [I.Boundaryless] in
theorem critical_slice_interpolation
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (u : SmoothScalar g) :
    ∫ x, |u.toFun x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, u.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^
          (2 / (Module.finrank ℝ E : ℝ)) *
        lpNorm u.toFun
            (ENNReal.ofReal
              (2 * (Module.finrank ℝ E : ℝ) /
                ((Module.finrank ℝ E : ℝ) - 2)))
            (riemannianVolumeMeasure (I := I) (M := M) g) ^ 2 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by linarith
  have hd2pos : 0 < (Module.finrank ℝ E : ℝ) - 2 := by linarith
  have hcritical : 0 ≤
      2 * (Module.finrank ℝ E : ℝ) /
        ((Module.finrank ℝ E : ℝ) - 2) :=
    (div_pos (mul_pos (by norm_num) hdpos) hd2pos).le
  have h2_cont : Continuous (fun x : M => u.toFun x ^ 2) :=
    u.smooth.continuous.pow 2
  have hq_cont : Continuous (fun x : M =>
      |u.toFun x| ^
        (2 * (Module.finrank ℝ E : ℝ) /
          ((Module.finrank ℝ E : ℝ) - 2))) :=
    u.smooth.continuous.abs.rpow_const (fun _ => Or.inr hcritical)
  exact DifferentialGeometry.Integral.critical_sobolev_interpolation hdim
    u.smooth.continuous.aestronglyMeasurable
    (h2_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem localized_parabolic_sobolev
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ cutoff u : SmoothScalar g,
        ∫ x, |cutoff.toFun x * u.toFun x| ^
              (2 + 4 / (Module.finrank ℝ E : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          C * localizedL2Mass (I := I) (M := M) cutoff u ^
              (2 / (Module.finrank ℝ E : ℝ)) *
            (localizedL2Mass (I := I) (M := M) cutoff u +
              localizedDirichletEnergy (I := I) (M := M) cutoff u +
              cutoffGradientError (I := I) (M := M) cutoff u) := by
  obtain ⟨C, hC, hSob⟩ := localized_sobolev (I := I) (M := M) g hdim
  refine ⟨C, hC, ?_⟩
  intro cutoff u
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let v : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x * u.toFun x, cutoff.smooth.mul u.smooth⟩
  have hinterp := critical_slice_interpolation (I := I) (M := M) g hdim v
  change (∫ x, |cutoff.toFun x * u.toFun x| ^
        (2 + 4 / (Module.finrank ℝ E : ℝ)) ∂μ) ≤ _ at hinterp
  have hmass :
      (∫ x, v.toFun x ^ 2 ∂μ) =
        localizedL2Mass (I := I) (M := M) cutoff u := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [v]
    ring
  rw [hmass] at hinterp
  have hlocal := hSob cutoff u
  have hmass_rpow_nonneg :
      0 ≤ localizedL2Mass (I := I) (M := M) cutoff u ^
        (2 / (Module.finrank ℝ E : ℝ)) :=
    Real.rpow_nonneg
      (localizedL2Mass_nonneg (I := I) (M := M) cutoff u) _
  calc
    _ ≤ localizedL2Mass (I := I) (M := M) cutoff u ^
          (2 / (Module.finrank ℝ E : ℝ)) *
        lpNorm (fun x => cutoff.toFun x * u.toFun x)
            (ENNReal.ofReal
              ((Module.finrank ℝ E : ℝ) * 2 /
                ((Module.finrank ℝ E : ℝ) - 2))) μ ^ 2 := by
      simpa only [v, μ, mul_comm] using hinterp
    _ ≤ localizedL2Mass (I := I) (M := M) cutoff u ^
          (2 / (Module.finrank ℝ E : ℝ)) *
        (C * (localizedL2Mass (I := I) (M := M) cutoff u +
          localizedDirichletEnergy (I := I) (M := M) cutoff u +
          cutoffGradientError (I := I) (M := M) cutoff u)) := by
      exact mul_le_mul_of_nonneg_left hlocal hmass_rpow_nonneg
    _ = C * localizedL2Mass (I := I) (M := M) cutoff u ^
          (2 / (Module.finrank ℝ E : ℝ)) *
        (localizedL2Mass (I := I) (M := M) cutoff u +
          localizedDirichletEnergy (I := I) (M := M) cutoff u +
          cutoffGradientError (I := I) (M := M) cutoff u) := by ring

theorem localized_parabolic_sobolev_time
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b S : ℝ} (hab : a ≤ b)
    (hmass_le : ∀ t ∈ Icc a b,
      localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) ≤ S)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in a..b, ∫ x,
          |cutoff.toFun x * u t x| ^
            (2 + 4 / (Module.finrank ℝ E : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        C * S ^ (2 / (Module.finrank ℝ E : ℝ)) *
          ∫ t in a..b,
            localizedL2Mass (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              localizedDirichletEnergy (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) := by
  obtain ⟨C, hC, hSob⟩ := localized_parabolic_sobolev (I := I) (M := M) g hdim
  refine ⟨C, hC, ?_⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let lhs : ℝ → ℝ := fun t =>
    ∫ x, |cutoff.toFun x * u t x| ^
      (2 + 4 / (Module.finrank ℝ E : ℝ)) ∂μ
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let dirichlet : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let energy : ℝ → ℝ := fun t => mass t + dirichlet t + error t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by linarith
  have hcritical : 0 ≤ 2 + 4 / (Module.finrank ℝ E : ℝ) := by positivity
  have hbase_cont : Continuous (fun p : ℝ × M =>
      |cutoff.toFun p.2 * u p.1 p.2|) :=
    ((cutoff.smooth.continuous.comp continuous_snd).mul hu.continuous).abs
  have hintegrand_cont : Continuous (fun p : ℝ × M =>
      |cutoff.toFun p.2 * u p.1 p.2| ^
        (2 + 4 / (Module.finrank ℝ E : ℝ))) :=
    hbase_cont.rpow_const (fun _ => Or.inr hcritical)
  have hlhs_cont : ContinuousOn lhs (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ (fun t x => |cutoff.toFun x * u t x| ^
        (2 + 4 / (Module.finrank ℝ E : ℝ))) isCompact_Icc
      hintegrand_cont.continuousOn
    simpa only [lhs] using h
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using
      (contDiff_localizedL2Mass (I := I) (M := M) cutoff u hu).continuous.continuousOn
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using
      (contDiff_cutoffGradientError (I := I) (M := M) cutoff u hu).continuous.continuousOn
  have henergy_cont : ContinuousOn energy (Icc a b) := by
    simpa only [energy] using (hmass_cont.add hdirichlet).add herror_cont
  have hmass_nonneg : ∀ t ∈ Icc a b, 0 ≤ mass t := by
    intro t _
    exact localizedL2Mass_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  have henergy_nonneg : ∀ t ∈ Icc a b, 0 ≤ energy t := by
    intro t _
    exact add_nonneg
      (add_nonneg
        (localizedL2Mass_nonneg (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t))
        (localizedDirichletEnergy_nonneg (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t)))
      (cutoffGradientError_nonneg (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t))
  have hpoint : ∀ t ∈ Icc a b,
      lhs t ≤ C * mass t ^ (2 / (Module.finrank ℝ E : ℝ)) * energy t := by
    intro t _
    have h := hSob cutoff (smoothScalarSlice (I := I) g u hu t)
    simpa only [lhs, mass, dirichlet, error, energy, smoothScalarSlice_toFun, μ] using h
  have htime := intervalIntegral_le_const_mul_sup_rpow
    hab hlhs_cont henergy_cont hC
    (div_nonneg (by norm_num) hdpos.le) hmass_nonneg
    (by simpa only [mass] using hmass_le) henergy_nonneg hpoint
  simpa only [lhs, mass, dirichlet, error, energy, μ] using htime

theorem localized_parabolic_sobolev_of_energy_bound
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hmass_le : ∀ t ∈ Icc a b,
      localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) ≤ A)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b))
    (henergy_le :
      (∫ t in a..b,
        localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          cutoffGradientError (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t)) ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in a..b, ∫ x,
          |cutoff.toFun x * u t x| ^
            (2 + 4 / (Module.finrank ℝ E : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        C * A ^ (1 + 2 / (Module.finrank ℝ E : ℝ)) := by
  obtain ⟨C, hC, htime⟩ := localized_parabolic_sobolev_time
    (I := I) (M := M) g hdim cutoff u hu hab hmass_le hdirichlet
  refine ⟨C, hC, htime.trans ?_⟩
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by linarith
  have htheta : 0 ≤ 2 / (Module.finrank ℝ E : ℝ) :=
    div_nonneg (by norm_num) hdpos.le
  have hfactor : 0 ≤ C * A ^ (2 / (Module.finrank ℝ E : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg hA _)
  calc
    C * A ^ (2 / (Module.finrank ℝ E : ℝ)) *
          (∫ t in a..b,
            localizedL2Mass (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              localizedDirichletEnergy (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t)) ≤
        C * A ^ (2 / (Module.finrank ℝ E : ℝ)) * A :=
      mul_le_mul_of_nonneg_left henergy_le hfactor
    _ = C * A ^ (1 + 2 / (Module.finrank ℝ E : ℝ)) := by
      rw [Real.rpow_add_of_nonneg hA (by norm_num) htheta, Real.rpow_one]
      ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
