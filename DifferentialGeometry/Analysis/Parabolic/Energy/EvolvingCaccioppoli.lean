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

def evolvingLocalizedDirichletEnergy
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 *
      (g t).inner x
        (gradientFun (I := I) (g t) (u t) x)
        (gradientFun (I := I) (g t) (u t) x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingCutoffGradientError
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, u t x ^ 2 *
      (g t).inner x
        (gradientFun (I := I) (g t) cutoff x)
        (gradientFun (I := I) (g t) cutoff x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedForcing
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, 2 * cutoff x ^ 2 * u t x * source t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedDirichletEnergy_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedDirichletEnergy
      (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) (g t) x _)

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingCutoffGradientError_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingCutoffGradientError (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) (g t) x _)

omit [I.Boundaryless] in
theorem evolvingLocalizedDirichletEnergy_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u) K := by
  let G : RealizedMetricFamily (I := I) (M := M) ℝ :=
    { metric := g
      connection := fun s => LeviCivita (I := I) (g s)
      metricCompatible := fun s => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (g s)) }
  have hgrad : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M =>
        (g p.1).inner p.2
          (gradientFun (I := I) (g p.1) (u p.1) p.2)
          (gradientFun (I := I) (g p.1) (u p.1) p.2)) := by
    have hraw := gradSq_joint (I := I) G isOpen_univ hgram u hu.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using hraw
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact (((hcutoff.continuous.comp continuous_snd).pow 2).mul
      hgrad.continuous).continuousOn

omit [I.Boundaryless] in
theorem evolvingCutoffGradientError_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingCutoffGradientError (I := I) (M := M) g cutoff u) K := by
  let G : RealizedMetricFamily (I := I) (M := M) ℝ :=
    { metric := g
      connection := fun s => LeviCivita (I := I) (g s)
      metricCompatible := fun s => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (g s)) }
  have hcutoff_joint : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => cutoff p.2) :=
    hcutoff.comp contMDiff_snd
  have hgrad : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M =>
        (g p.1).inner p.2
          (gradientFun (I := I) (g p.1) cutoff p.2)
          (gradientFun (I := I) (g p.1) cutoff p.2)) := by
    have hraw := gradSq_joint (I := I) G isOpen_univ hgram
      (fun _ => cutoff) hcutoff_joint.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using hraw
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact ((hu.continuous.pow 2).mul hgrad.continuous).continuousOn

omit [I.Boundaryless] in
theorem evolvingLocalizedForcing_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2))
    (hsource : Continuous (fun p : ℝ × M => source p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedForcing (I := I) (M := M) g cutoff u source) K := by
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact ((((continuous_const.mul
      ((hcutoff.comp continuous_snd).pow 2)).mul hu).mul hsource)).continuousOn

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

omit [I.Boundaryless] in
private theorem caccioppoli_evolving_of_differential
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hdifferential : ∀ t ∈ Icc a b,
      deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
        4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
          evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
          evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u
  let dirichlet : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u
  let forcing : ℝ → ℝ :=
    evolvingLocalizedForcing (I := I) (M := M) g cutoff u source
  let distortion : ℝ → ℝ :=
    evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u
  have hmass_cont : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hcutoff.continuous hu.continuous
  have hdmass_cont : ContinuousOn (deriv mass) (Icc a b) := by
    simpa only [mass] using deriv_evolvingLocalizedL2Mass_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hcutoff hu
  have hmass_deriv : ∀ t ∈ Icc a b,
      HasDerivAt mass (deriv mass t) t := by
    intro t _
    have hraw := hasDerivAt_evolvingLocalizedL2Mass
      (I := I) (M := M) g cutoff u t (hg.at_any t) hcutoff hu
    simpa only [mass] using hraw.congr_deriv hraw.deriv.symm
  have hdirichlet : ContinuousOn dirichlet (Icc a b) := by
    simpa only [dirichlet] using evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have herror : ContinuousOn error (Icc a b) := by
    simpa only [error] using evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  have hforcing : ContinuousOn forcing (Icc a b) := by
    simpa only [forcing] using evolvingLocalizedForcing_continuousOn
      (I := I) (M := M) g cutoff u source isCompact_Icc hg
        hcutoff.continuous hu.continuous hsource.continuous
  have hdistortion : ContinuousOn distortion (Icc a b) := by
    simpa only [distortion] using evolvingLocalizedVolumeDistortion_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg
        hcutoff.continuous hu.continuous
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hdissipation : ContinuousOn
      (fun t => weight t * dirichlet t) (Icc a b) :=
    hweight_cont.mul hdirichlet
  have hrhs : ContinuousOn
      (fun t => dweight t * mass t +
        weight t * (4 * error t + forcing t + distortion t)) (Icc a b) :=
    (hdweight.mul hmass_cont).add
      (hweight_cont.mul
        (((continuousOn_const.mul herror).add hforcing).add hdistortion))
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * mass t + weight t * deriv mass t + weight t * dirichlet t ≤
        dweight t * mass t +
          weight t * (4 * error t + forcing t + distortion t) := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_left (hdifferential t ht)
      (hweight_nonneg t ht)
    change weight t * (deriv mass t + dirichlet t) ≤
      weight t * (4 * error t + forcing t + distortion t) at hmul
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdmass_cont hmass_deriv hdissipation hrhs hpointwise
  simpa only [mass, dirichlet, error, forcing, distortion] using hresult

theorem caccioppoli_evolving
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  apply caccioppoli_evolving_of_differential
    (I := I) (M := M) g cutoff u source hcutoff hu hsource hg hgram
      hab hdweight hweight hweight_nonneg
  intro t ht
  have hraw := caccioppoli_differential_evolving
    (I := I) (M := M) g cutoff u source t (hg.at_any t)
      hcutoff hu hsource (hpde t ht)
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
      evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
    4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
      evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
      evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t at hraw
  exact hraw

theorem caccioppoli_evolving_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {t₀ : ℝ} (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hu_nonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x) :
    weight b * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u b -
        weight a * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff u t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff u source t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff u t) := by
  apply caccioppoli_evolving_of_differential
    (I := I) (M := M) g cutoff u source hcutoff hu hsource hg hgram
      hab hdweight hweight hweight_nonneg
  intro t ht
  have hraw := caccioppoli_differential_evolving_of_subsolution
    (I := I) (M := M) g cutoff u source t (hg.at_any t)
      hcutoff hu hsource (hu_nonneg t ht) (hpde t ht)
  change deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t +
      evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t ≤
    4 * evolvingCutoffGradientError (I := I) (M := M) g cutoff u t +
      evolvingLocalizedForcing (I := I) (M := M) g cutoff u source t +
      evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t at hraw
  exact hraw

end DifferentialGeometry.Analysis.Parabolic.Energy
