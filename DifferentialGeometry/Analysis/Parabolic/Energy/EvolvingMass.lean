import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity


noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Energy

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingLocalizedIntegral
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 * u t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedL2Mass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 * u t x ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedVolumeDistortion
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

omit [CompactSpace M] in
theorem evolvingLocalizedL2Mass_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem evolvingLocalizedIntegral_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedIntegral (I := I) (M := M) g cutoff u) K := by
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact ((hcutoff.comp continuous_snd).pow 2).mul hu |>.continuousOn

theorem evolvingLocalizedL2Mass_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) K := by
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact (((hcutoff.comp continuous_snd).pow 2).mul (hu.pow 2)).continuousOn

theorem evolvingLocalizedVolumeDistortion_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff)
    (hu : Continuous (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u) K := by
  apply integral_family_cont (I := I) (M := M) hK
  · intro x₀ i j
    exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
      (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
  · exact
      (((hcutoff.comp continuous_snd).pow 2).mul
        ((continuous_const.mul
          (traceTimeDerivMetric_joint_continuous (I := I) (M := M) hg)).mul
            (hu.pow 2))).continuousOn

theorem hasDerivAt_evolvingLocalizedIntegral
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    HasDerivAt
      (evolvingLocalizedIntegral (I := I) (M := M) g cutoff u)
      (∫ x, cutoff x ^ 2 *
          (deriv (fun s => u s x) t +
            (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) t := by
  have hintegrand : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => cutoff p.2 ^ 2 * u p.1 p.2) :=
    ((hcutoff.comp contMDiff_snd).pow 2).mul hu
  have hraw := first_variation_of_volume (I := I) (M := M) hg
    (FunctionRegularAt.of_contMDiff
      (fun s x => cutoff x ^ 2 * u s x) hintegrand t)
  have hderiv : ∀ x : M,
      deriv (fun s => cutoff x ^ 2 * u s x) t =
        cutoff x ^ 2 * deriv (fun s => u s x) t := by
    intro x
    have hfiber : ContDiff ℝ ∞ (fun s : ℝ => u s x) :=
      contMDiff_iff_contDiff.mp
        (hu.comp (contMDiff_id.prodMk contMDiff_const))
    have hu_at : HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t :=
      (hfiber.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hproduct := ((hasDerivAt_const t (cutoff x ^ 2)).mul hu_at).deriv
    simpa only [Pi.mul_apply, zero_mul, zero_add] using hproduct
  convert hraw using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hderiv x]
  ring

theorem hasDerivAt_evolvingLocalizedL2Mass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    HasDerivAt
      (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u)
      (∫ x, cutoff x ^ 2 *
          (2 * u t x * deriv (fun s => u s x) t +
            (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) t := by
  have hu_sq : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2 ^ 2) := hu.pow 2
  have hraw := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff (fun s x => u s x ^ 2) t hg hcutoff hu_sq
  have hderiv : ∀ x : M,
      deriv (fun s => u s x ^ 2) t =
        2 * u t x * deriv (fun s => u s x) t := by
    intro x
    have hfiber : ContDiff ℝ ∞ (fun s : ℝ => u s x) :=
      contMDiff_iff_contDiff.mp
        (hu.comp (contMDiff_id.prodMk contMDiff_const))
    have hu_at : HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t :=
      (hfiber.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hsquare := (hu_at.pow 2).deriv
    convert hsquare using 1
    ring
  convert hraw using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hderiv x]

theorem deriv_evolvingLocalizedL2Mass_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) {K : Set ℝ} (hK : IsCompact K) {t : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContinuousOn
      (fun s => deriv
        (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) s) K := by
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => u p.1 p.2, hu⟩
  have htime : Continuous
      (fun p : ℝ × M => deriv (fun s => u s p.2) p.1) := by
    simpa only [F] using
      (DifferentialGeometry.contMDiff_partial_deriv_fst I F).continuous
  have hintegral : ContinuousOn
      (fun s => ∫ x, cutoff x ^ 2 *
          (2 * u s x * deriv (fun r => u r x) s +
            (1 / 2) * traceTimeDerivMetric (I := I) g s x * u s x ^ 2)
        ∂(riemannianMeasureFamily (I := I) (M := M) g s)) K := by
    apply integral_family_cont (I := I) (M := M) hK
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ K) Set.Subset.rfl)
    · exact
        (((hcutoff.continuous.comp continuous_snd).pow 2).mul
          (((continuous_const.mul hu.continuous).mul htime).add
            ((continuous_const.mul
              (traceTimeDerivMetric_joint_continuous
                (I := I) (M := M) hg)).mul (hu.continuous.pow 2)))) |>.continuousOn
  refine hintegral.congr ?_
  intro s _
  exact (hasDerivAt_evolvingLocalizedL2Mass
    (I := I) (M := M) g cutoff u s (hg.at_any s) hcutoff hu).deriv

theorem evolvingLocalizedVolumeDistortion_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : Continuous cutoff) (hu : Continuous (u t))
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    evolvingLocalizedVolumeDistortion (I := I) (M := M) g cutoff u t ≤
      (1 / 2) * B * evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have htrace_cont : Continuous
      (fun x : M => traceTimeDerivMetric (I := I) g t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hg
  have hleft_int : Integrable (fun x : M => cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)) μ :=
    ((hcutoff.pow 2).mul
      ((continuous_const.mul htrace_cont).mul (hu.pow 2)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : Integrable (fun x : M =>
      ((1 / 2) * B) * (cutoff x ^ 2 * u t x ^ 2)) μ :=
    (continuous_const.mul ((hcutoff.pow 2).mul (hu.pow 2)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, cutoff x ^ 2 *
      ((1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2) ∂μ) ≤
    (1 / 2) * B * ∫ x, cutoff x ^ 2 * u t x ^ 2 ∂μ
  rw [← integral_const_mul]
  apply integral_mono hleft_int hright_int
  intro x
  have ht := mul_le_mul_of_nonneg_right (htrace x) (sq_nonneg (u t x))
  have hh := mul_le_mul_of_nonneg_left ht (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hc := mul_le_mul_of_nonneg_left hh (sq_nonneg (cutoff x))
  nlinarith

theorem deriv_evolvingLocalizedL2Mass_le_of_trace_le
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t B : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (htrace : ∀ x : M, traceTimeDerivMetric (I := I) g t x ≤ B) :
    deriv (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u) t ≤
      ∫ x, cutoff x ^ 2 *
          (2 * u t x * deriv (fun s => u s x) t +
            (1 / 2) * B * u t x ^ 2)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  rw [(hasDerivAt_evolvingLocalizedL2Mass
    (I := I) (M := M) g cutoff u t hg hcutoff hu).deriv]
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
  have hleft_cont : Continuous (fun x : M => cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)) :=
    (hcutoff.continuous.pow 2).mul
      (((continuous_const.mul hu_t).mul htime).add
        ((continuous_const.mul htrace_cont).mul (hu_t.pow 2)))
  have hright_cont : Continuous (fun x : M => cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * B * u t x ^ 2)) :=
    (hcutoff.continuous.pow 2).mul
      (((continuous_const.mul hu_t).mul htime).add
        ((continuous_const.mul continuous_const).mul (hu_t.pow 2)))
  have hleft_int : Integrable (fun x : M => cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x ^ 2)) μ :=
    hleft_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : Integrable (fun x : M => cutoff x ^ 2 *
      (2 * u t x * deriv (fun s => u s x) t +
        (1 / 2) * B * u t x ^ 2)) μ :=
    hright_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integral_mono hleft_int hright_int
  intro x
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (cutoff x))
  have hmul := mul_le_mul_of_nonneg_right (htrace x) (sq_nonneg (u t x))
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.Energy
