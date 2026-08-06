import DifferentialGeometry.Analysis.Integration.Measure.Family


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

omit [CompactSpace M] in
theorem evolvingLocalizedL2Mass_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))

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
