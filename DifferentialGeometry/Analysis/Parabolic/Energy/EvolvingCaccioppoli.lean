import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Analysis.Parabolic.Energy.EvolvingMass


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

omit [I.Boundaryless] in
theorem deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t =
      deriv (fun s => localizedL2Mass (I := I) (M := M)
        (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
        (smoothScalarSlice (I := I) (g t) u hu s)) t +
      ∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hu_t : Continuous (u t) :=
    (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => u p.1 p.2, hu⟩
  have htime : Continuous (fun x : M => deriv (fun s => u s x) t) := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace_cont : Continuous
      (fun x : M => traceTimeDerivMetric (I := I) g t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hg
  have htime_int : Integrable (fun x : M =>
      2 * cutoff x ^ 2 * u t x * deriv (fun s => u s x) t) μ :=
    (((continuous_const.mul (hcutoff.continuous.pow 2)).mul hu_t).mul htime)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvolume_int : Integrable (fun x : M => cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)) μ :=
    ((hcutoff.continuous.pow 2).mul
      ((continuous_const.mul htrace_cont).mul (hu_t.pow 2)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [(hasDerivAt_evolvingLocalizedL2Mass
    (I := I) (M := M) g cutoff u t hg hcutoff hu).deriv]
  rw [(hasDerivAt_localizedL2Mass
    (I := I) (M := M) (⟨cutoff, hcutoff⟩ : SmoothScalar (g t)) u hu t).deriv]
  change (∫ x, cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2) ∂μ) =
    (∫ x, 2 * cutoff x ^ 2 * u t x * deriv (fun s => u s x) t ∂μ) +
      ∫ x, cutoff x ^ 2 *
        ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2) ∂μ
  rw [← integral_add htime_int hvolume_int]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem caccioppoli_differential_evolving
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        ∫ x, cutoff x ^ 2 *
            ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  have hfixed := caccioppoli_differential
    (I := I) (M := M) (g := g t)
    (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
    u source hu hsource t hpde
  change deriv (fun s => localizedL2Mass (I := I) (M := M)
      (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
      (smoothScalarSlice (I := I) (g t) u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) at hfixed
  rw [deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (I := I) (M := M) g cutoff u t hg hcutoff hu]
  linarith

theorem caccioppoli_differential_evolving_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hu_nonneg : ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        ∫ x, cutoff x ^ 2 *
            ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  have hfixed := caccioppoli_differential_of_subsolution
    (I := I) (M := M) (g := g t)
    (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
    u source hu hsource t hu_nonneg hpde
  change deriv (fun s => localizedL2Mass (I := I) (M := M)
      (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
      (smoothScalarSlice (I := I) (g t) u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) at hfixed
  rw [deriv_evolvingLocalizedL2Mass_eq_deriv_localizedL2Mass_add_volume
    (I := I) (M := M) g cutoff u t hg hcutoff hu]
  linarith

theorem caccioppoli_differential_evolving_of_trace_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x)
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        (1 / 2) * B * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff u t := by
  have henergy := caccioppoli_differential_evolving
    (I := I) (M := M) g cutoff u source t hg hcutoff hu hsource hpde
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        evolvingLocalizedVolumeDistortion
          (I := I) (M := M) g cutoff u t at henergy
  have hvolume := evolvingLocalizedVolumeDistortion_le
    (I := I) (M := M) g cutoff u t B hg hcutoff.continuous
      (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous htrace
  linarith

theorem caccioppoli_differential_evolving_of_subsolution_of_trace_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hu_nonneg : ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x)
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        (1 / 2) * B * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff u t := by
  have henergy := caccioppoli_differential_evolving_of_subsolution
    (I := I) (M := M) g cutoff u source t hg hcutoff hu hsource hu_nonneg hpde
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
        localizedDirichletEnergy (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M)
          (⟨cutoff, hcutoff⟩ : SmoothScalar (g t))
          (smoothScalarSlice (I := I) (g t) u hu t) +
        ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) +
        evolvingLocalizedVolumeDistortion
          (I := I) (M := M) g cutoff u t at henergy
  have hvolume := evolvingLocalizedVolumeDistortion_le
    (I := I) (M := M) g cutoff u t B hg hcutoff.continuous
      (hu.comp (contMDiff_const.prodMk contMDiff_id)).continuous htrace
  linarith

end DifferentialGeometry.Analysis.Parabolic.Energy
