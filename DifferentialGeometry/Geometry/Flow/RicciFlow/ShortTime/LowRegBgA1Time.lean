import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime

/-!
# Time packets for the fixed-background high first-order action

This module converts the ball-local completed `H3 → H2` coefficient into the
strongly measurable, time-square-integrable family consumed by the adjacent
scale lift.  No smooth representative of the completed state is chosen.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricH3 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A ball-local smooth-core pair estimate bounds the completed high
first-order coefficient uniformly on the corresponding ambient `H3` ball. -/
theorem lowA1HiBg_ball
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : metricH3 (I := I) (M := M) g, ‖v‖ ≤ R →
        ‖lowA1HiBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ C := by
  let j : SmoothCcTensor g 0 2 →ₗ[ℝ]
      metricH3 (I := I) (M := M) g :=
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
  let F := lowA1HiBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal
  obtain ⟨K, hK⟩ := hpair (R + 1)
  let K₀ : ℝ := max K 0
  let C : ℝ := K₀ * R + ‖F 0‖
  have hK₀ : 0 ≤ K₀ := le_max_right K 0
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hK₀ hR) (norm_nonneg (F 0))
  refine ⟨C, hC, ?_⟩
  intro v hv
  have hF : Continuous F :=
    lowA1HiBg_cont (I := I) (M := M) g g hpair
  have hright : Continuous
      (fun w : metricH3 (I := I) (M := M) g =>
        K₀ * ‖w‖ + ‖F 0‖) :=
    (continuous_const.mul continuous_norm).add continuous_const
  have hFnorm : Continuous
      (fun w : metricH3 (I := I) (M := M) g => ‖F w‖) :=
    Continuous.comp
      (continuous_norm (E :=
        metricH3 (I := I) (M := M) g →L[ℝ]
          metricH2 (I := I) (M := M) g)) hF
  change ‖F v‖ ≤ C
  have hclosed :
      IsClosed {w : metricH3 (I := I) (M := M) g |
        R + 1 ≤ ‖w‖ ∨ ‖F w‖ ≤ K₀ * ‖w‖ + ‖F 0‖} := by
    simpa only [Set.setOf_or] using
      (isClosed_le continuous_const continuous_norm).union
        (isClosed_le hFnorm hright)
  have hall : R + 1 ≤ ‖v‖ ∨ ‖F v‖ ≤ K₀ * ‖v‖ + ‖F 0‖ := by
    refine (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).induction_on
      v hclosed ?_
    intro S
    by_cases hlarge : R + 1 ≤ ‖j S‖
    · exact Or.inl hlarge
    · right
      have hsmall : ‖j S‖ ≤ R + 1 := (lt_of_not_ge hlarge).le
      have hzero : ‖j (0 : SmoothCcTensor g 0 2)‖ ≤ R + 1 := by
        simp only [map_zero, norm_zero]
        linarith
      have hdiff := hK S (0 : SmoothCcTensor g 0 2) hsmall hzero
      have hcoreS :
          F (j S) =
            (lowCoreDataBg (I := I) (M := M)
              g g hρ hδ0 hδ_le hreal S).a1Hi (I := I) (M := M) := by
        exact lowA1HiBg_core (I := I) (M := M) g g hpair S
      have hcore0 :
          F 0 =
            (lowCoreDataBg (I := I) (M := M)
              g g hρ hδ0 hδ_le hreal
              (0 : SmoothCcTensor g 0 2)).a1Hi (I := I) (M := M) := by
        simpa only [map_zero] using
          (lowA1HiBg_core (I := I) (M := M) g g hpair
            (0 : SmoothCcTensor g 0 2))
      rw [← hcoreS, ← hcore0] at hdiff
      have hdiff0 : ‖F (j S) - F 0‖ ≤ K * ‖j S‖ := by
        simpa only [map_zero, sub_zero] using hdiff
      have hdiff' : ‖F (j S) - F 0‖ ≤ K₀ * ‖j S‖ := by
        refine hdiff0.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _)
      calc
        ‖F (j S)‖ = ‖(F (j S) - F 0) + F 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖F (j S) - F 0‖ + ‖F 0‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
        _ ≤ K₀ * ‖j S‖ + ‖F 0‖ := add_le_add hdiff' le_rfl
  rcases hall with hlarge | hbound
  · exact (not_le_of_gt (hv.trans_lt (lt_add_one R)) hlarge).elim
  · refine hbound.trans ?_
    simpa only [C] using
      add_le_add (mul_le_mul_of_nonneg_left hv hK₀) (le_refl ‖F 0‖)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A ball-local smooth-core pair estimate also bounds the completed low
first-order coefficient uniformly on the ambient `H3` ball. -/
theorem lowA1LoBg_ball
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : BgA1CorePair (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : metricH3 (I := I) (M := M) g, ‖v‖ ≤ R →
        ‖lowA1LoBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ C := by
  let j : SmoothCcTensor g 0 2 →ₗ[ℝ]
      metricH3 (I := I) (M := M) g :=
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
  let F := lowA1LoBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal
  obtain ⟨K, hK⟩ := hpair (R + 1)
  let K₀ : ℝ := max K 0
  let C : ℝ := K₀ * R + ‖F 0‖
  have hK₀ : 0 ≤ K₀ := le_max_right K 0
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hK₀ hR) (norm_nonneg (F 0))
  refine ⟨C, hC, ?_⟩
  intro v hv
  have hF : Continuous F :=
    lowA1LoBg_cont (I := I) (M := M) g g hpair
  have hright : Continuous
      (fun w : metricH3 (I := I) (M := M) g =>
        K₀ * ‖w‖ + ‖F 0‖) :=
    (continuous_const.mul continuous_norm).add continuous_const
  have hFnorm : Continuous
      (fun w : metricH3 (I := I) (M := M) g => ‖F w‖) :=
    Continuous.comp
      (continuous_norm (E :=
        metricH2 (I := I) (M := M) g →L[ℝ]
          metricH1 (I := I) (M := M) g)) hF
  change ‖F v‖ ≤ C
  have hclosed :
      IsClosed {w : metricH3 (I := I) (M := M) g |
        R + 1 ≤ ‖w‖ ∨ ‖F w‖ ≤ K₀ * ‖w‖ + ‖F 0‖} := by
    simpa only [Set.setOf_or] using
      (isClosed_le continuous_const continuous_norm).union
        (isClosed_le hFnorm hright)
  have hall : R + 1 ≤ ‖v‖ ∨ ‖F v‖ ≤ K₀ * ‖v‖ + ‖F 0‖ := by
    refine (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).induction_on
      v hclosed ?_
    intro S
    by_cases hlarge : R + 1 ≤ ‖j S‖
    · exact Or.inl hlarge
    · right
      have hsmall : ‖j S‖ ≤ R + 1 := (lt_of_not_ge hlarge).le
      have hzero : ‖j (0 : SmoothCcTensor g 0 2)‖ ≤ R + 1 := by
        simp only [map_zero, norm_zero]
        linarith
      have hdiff := hK S (0 : SmoothCcTensor g 0 2) hsmall hzero
      have hcoreS :
          F (j S) =
            (lowCoreDataBg (I := I) (M := M)
              g g hρ hδ0 hδ_le hreal S).a1Lo (I := I) (M := M) := by
        exact lowA1LoBg_core (I := I) (M := M) g g hpair S
      have hcore0 :
          F 0 =
            (lowCoreDataBg (I := I) (M := M)
              g g hρ hδ0 hδ_le hreal
              (0 : SmoothCcTensor g 0 2)).a1Lo (I := I) (M := M) := by
        simpa only [map_zero] using
          (lowA1LoBg_core (I := I) (M := M) g g hpair
            (0 : SmoothCcTensor g 0 2))
      rw [← hcoreS, ← hcore0] at hdiff
      have hdiff0 : ‖F (j S) - F 0‖ ≤ K * ‖j S‖ := by
        simpa only [map_zero, sub_zero] using hdiff
      have hdiff' : ‖F (j S) - F 0‖ ≤ K₀ * ‖j S‖ := by
        refine hdiff0.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _)
      calc
        ‖F (j S)‖ = ‖(F (j S) - F 0) + F 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖F (j S) - F 0‖ + ‖F 0‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
        _ ≤ K₀ * ‖j S‖ + ‖F 0‖ := add_le_add hdiff' le_rfl
  rcases hall with hlarge | hbound
  · exact (not_le_of_gt (hv.trans_lt (lt_add_one R)) hlarge).elim
  · refine hbound.trans ?_
    simpa only [C] using
      add_le_add (mul_le_mul_of_nonneg_left hv hK₀) (le_refl ‖F 0‖)

/-- Along an a.e. bounded measurable `H3` trajectory, the completed high
first-order coefficient is strongly measurable, square-integrable in time, and
uniformly bounded in operator norm. -/
theorem lowA1HiBg_time
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal)
    {T R : ℝ} (hR : 0 ≤ R)
    (u : ℝ → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (hball : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
          (fun t => lowA1HiBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal (u t)) (timeMeasure T) ∧
        MemLp
          (fun t => lowA1HiBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal (u t)) 2 (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖lowA1HiBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal (u t)‖ ≤ C) := by
  obtain ⟨C, hC, hCstate⟩ :=
    lowA1HiBg_ball (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hpair hR
  let A := fun t => lowA1HiBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (u t)
  have hmeas : AEStronglyMeasurable A (timeMeasure T) := by
    simpa only [A] using
      lowA1HiBg_aesm (I := I) (M := M) g g hpair u hu
  have hbd : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C := by
    filter_upwards [hball] with t ht
    exact hCstate (u t) ht
  have hmem : MemLp A 2 (timeMeasure T) :=
    MemLp.of_bound (f := A) (p := 2) (μ := timeMeasure T) hmeas C hbd
  exact ⟨C, hC, hmeas, hmem, hbd⟩

/-- The high first-order affine family freezes the radial passenger map at the
same completed `H3` state as its coefficient. -/
noncomputable def hiAffA1Bg
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) :
    ℝ → metricH3 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  fun t =>
    (lowA1HiBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (u t)).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

/-- Freezing the radial passenger map does not enlarge the high first-order
coefficient norm. -/
theorem hiAffA1Bg_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    ‖hiAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowA1HiBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (u t)‖ := by
  let A1 := lowA1HiBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (u t)
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A1.comp R3‖ ≤ ‖A1‖
  calc
    ‖A1.comp R3‖ ≤ ‖A1‖ * ‖R3‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A1‖ * 1 := mul_le_mul_of_nonneg_left hR3 (norm_nonneg A1)
    _ = ‖A1‖ := mul_one _

/-- The radialized high first-order family supplies the measurable and
time-`L²` coefficient packet used by the adjacent-scale affine equation. -/
theorem hiAffA1Bg_data
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : BgA1HiCorePair (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal)
    {T R : ℝ} (hR : 0 ≤ R)
    (u : ℝ → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (hball : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
          (hiAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
        MemLp
          (hiAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u) 2 (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖hiAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u t‖ ≤ C) := by
  obtain ⟨C, hC, hA1, _, hA1bd⟩ :=
    lowA1HiBg_time (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hpair hR u hu hball
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g (u t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hR3 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hmeas : AEStronglyMeasurable
      (hiAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    simpa only [hiAffA1Bg] using
      (ContinuousLinearMap.compL ℝ
        (metricH3 (I := I) (M := M) g)
        (metricH3 (I := I) (M := M) g)
        (metricH2 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hA1 hR3
  have hbd : ∀ᵐ t ∂timeMeasure T,
      ‖hiAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u t‖ ≤ C := by
    filter_upwards [hA1bd] with t ht
    exact (hiAffA1Bg_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans ht
  have hmem : MemLp
      (hiAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) 2 (timeMeasure T) :=
    MemLp.of_bound
      (f := hiAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u)
      (p := 2) (μ := timeMeasure T) hmeas C hbd
  exact ⟨C, hC, hmeas, hmem, hbd⟩

/-- The low first-order affine family freezes the same radial passenger map as
the high family, now on the `H2 → H1` scale. -/
noncomputable def loAffA1Bg
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) :
    ℝ → metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  fun t =>
    (lowA1LoBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (u t)).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

/-- Freezing the radial passenger map does not enlarge the low first-order
coefficient norm. -/
theorem loAffA1Bg_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    ‖loAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowA1LoBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (u t)‖ := by
  let A1 := lowA1LoBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (u t)
  let R2 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 2 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR2 : ‖R2‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A1.comp R2‖ ≤ ‖A1‖
  calc
    ‖A1.comp R2‖ ≤ ‖A1‖ * ‖R2‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A1‖ * 1 := mul_le_mul_of_nonneg_left hR2 (norm_nonneg A1)
    _ = ‖A1‖ := mul_one _

/-- The high and low radialized first-order time families commute with the
adjacent Sobolev inclusions at every time. -/
theorem affA1Bg_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hHi : BgA1HiCorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (hLo : BgA1CorePair (I := I) (M := M)
      g g hρ.le hδ0 hδ_le hreal)
    (u : ℝ → metricH3 (I := I) (M := M) g) (t : ℝ) :
    (incl12 (I := I) (M := M) g).comp
        (hiAffA1Bg (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal u t) =
      (loAffA1Bg (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal u t).comp
        (incl32 (I := I) (M := M) g) := by
  let J12 := incl12 (I := I) (M := M) g
  let J23 := incl32 (I := I) (M := M) g
  let AHi := lowA1HiBg (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal (u t)
  let ALo := lowA1LoBg (I := I) (M := M)
    g g hρ.le hδ0 hδ_le hreal (u t)
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ (J23 (u t))
  let R2 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 2 by norm_num) ρ (J23 (u t))
  have hcoef : J12.comp AHi = ALo.comp J23 :=
    lowA1Bg_comm (I := I) (M := M) hDim g
      hρ hδ0 hδ_le hreal hHi hLo (u t)
  have hrad : J23.comp R3 = R2.comp J23 :=
    radialCLM_incl (I := I) (M := M) g
      (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 3 by norm_num)
      (show (2 : ℝ) ≤ 3 by norm_num) ρ (J23 (u t))
  apply ContinuousLinearMap.ext
  intro x
  simp only [hiAffA1Bg, loAffA1Bg, ContinuousLinearMap.comp_apply]
  rw [show J12 (AHi (R3 x)) = ALo (J23 (R3 x)) by
      exact DFunLike.congr_fun hcoef (R3 x)]
  rw [show J23 (R3 x) = R2 (J23 x) by
      exact DFunLike.congr_fun hrad x]

/-- The radialized low first-order family supplies its matching measurable and
time-`L²` coefficient packet on every a.e. bounded `H3` trajectory. -/
theorem loAffA1Bg_data
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : BgA1CorePair (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal)
    {T R : ℝ} (hR : 0 ≤ R)
    (u : ℝ → metricH3 (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (hball : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
          (loAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
        MemLp
          (loAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u) 2 (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖loAffA1Bg (I := I) (M := M)
            g hρ hδ0 hδ_le hreal u t‖ ≤ C) := by
  obtain ⟨C, hC, hCstate⟩ :=
    lowA1LoBg_ball (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hpair hR
  have hA1 : AEStronglyMeasurable
      (fun t => lowA1LoBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (u t)) (timeMeasure T) :=
    lowA1LoBg_aesm (I := I) (M := M) g g hpair u hu
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g (u t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hR2 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 2 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hmeas : AEStronglyMeasurable
      (loAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    simpa only [loAffA1Bg] using
      (ContinuousLinearMap.compL ℝ
        (metricH2 (I := I) (M := M) g)
        (metricH2 (I := I) (M := M) g)
        (metricH1 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hA1 hR2
  have hbd : ∀ᵐ t ∂timeMeasure T,
      ‖loAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u t‖ ≤ C := by
    filter_upwards [hball] with t ht
    exact (loAffA1Bg_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans (hCstate (u t) ht)
  have hmem : MemLp
      (loAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) 2 (timeMeasure T) :=
    MemLp.of_bound
      (f := loAffA1Bg (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u)
      (p := 2) (μ := timeMeasure T) hmeas C hbd
  exact ⟨C, hC, hmeas, hmem, hbd⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
