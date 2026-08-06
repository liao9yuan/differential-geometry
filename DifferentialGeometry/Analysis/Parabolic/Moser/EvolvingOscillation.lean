import DifferentialGeometry.Analysis.Parabolic.Energy.EvolvingCaccioppoli
import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedIntegral (I := I) (M := M) g cutoff (fun _ _ => 1) t

def evolvingLocalizedAverage
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedIntegral (I := I) (M := M) g cutoff u t /
    evolvingCutoffMass (I := I) (M := M) g cutoff t

def evolvingLocalizedL2Deviation
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (center t : ℝ) : ℝ :=
  ∫ x, cutoff x ^ 2 * (u t x - center) ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedL2Oscillation
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  evolvingLocalizedL2Deviation (I := I) (M := M) g cutoff u
    (evolvingLocalizedAverage (I := I) (M := M) g cutoff u t) t

def HasEvolvingLocalizedPoincare
    (g : ℝ → SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : M → ℝ) (C : ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ u : SmoothScalar (g t),
    evolvingLocalizedL2Oscillation (I := I) (M := M) g averagingCutoff
        (fun _ x => u.toFun x) t ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g energyCutoff (fun _ x => u.toFun x) t

omit [CompactSpace M] in
theorem hasEvolvingLocalizedPoincare_iff [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M)
    (averagingCutoff energyCutoff : M → ℝ) (C : ℝ) (J : Set ℝ)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (henergyCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ energyCutoff) :
    HasEvolvingLocalizedPoincare
        (I := I) (M := M) g averagingCutoff energyCutoff C J ↔
      ∀ t ∈ J,
        HasLocalizedPoincare (I := I) (M := M) (g t)
          ⟨averagingCutoff, haveragingCutoff⟩
          ⟨energyCutoff, henergyCutoff⟩ C := by
  constructor
  · intro h t ht u
    simpa only [HasLocalizedPoincare, localizedL2Oscillation,
      localizedL2Deviation, localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincare,
      evolvingLocalizedL2Oscillation, evolvingLocalizedL2Deviation,
      evolvingLocalizedAverage, evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u
  · intro h t ht u
    simpa only [HasLocalizedPoincare, localizedL2Oscillation,
      localizedL2Deviation, localizedAverage, localizedIntegral, cutoffMass,
      localizedDirichletEnergy, HasEvolvingLocalizedPoincare,
      evolvingLocalizedL2Oscillation, evolvingLocalizedL2Deviation,
      evolvingLocalizedAverage, evolvingCutoffMass, evolvingLocalizedIntegral,
      evolvingLocalizedDirichletEnergy, riemannianMeasureFamily, mul_one,
      grad_g_apply] using h t ht u

omit [CompactSpace M] in
theorem evolvingCutoffMass_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ) :
    0 ≤ evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  simp only [evolvingCutoffMass, evolvingLocalizedIntegral, mul_one]
  exact integral_nonneg fun x => sq_nonneg (cutoff x)

theorem evolvingCutoffMass_pos
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ)
    (hcutoff : Continuous cutoff) (hne : ∃ x, cutoff x ≠ 0) :
    0 < evolvingCutoffMass (I := I) (M := M) g cutoff t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  letI : μ.IsOpenPosMeasure := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g t)
  obtain ⟨x, hx⟩ := hne
  have hsq : cutoff x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  simp only [evolvingCutoffMass, evolvingLocalizedIntegral, mul_one]
  exact integral_pos_of_integrable_nonneg_nonzero
    (hcutoff.pow 2)
    ((hcutoff.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun y => sq_nonneg (cutoff y)) hsq

omit [CompactSpace M] in
theorem evolvingLocalizedL2Oscillation_nonneg
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ) :
    0 ≤ evolvingLocalizedL2Oscillation
      (I := I) (M := M) g cutoff u t := by
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem hasDerivAt_evolvingCutoffMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff) :
    HasDerivAt
      (evolvingCutoffMass (I := I) (M := M) g cutoff)
      (∫ x, cutoff x ^ 2 *
          ((1 / 2) * traceTimeDerivMetric (I := I) g t x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) t := by
  have h := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff (fun _ _ => 1) t hg hcutoff contMDiff_const
  simpa only [evolvingCutoffMass, evolvingLocalizedIntegral, deriv_const,
    zero_add, mul_one] using h

theorem hasDerivAt_evolvingLocalizedAverage
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hmass : evolvingCutoffMass (I := I) (M := M) g cutoff t ≠ 0) :
    HasDerivAt
      (evolvingLocalizedAverage (I := I) (M := M) g cutoff u)
      (((∫ x, cutoff x ^ 2 *
            (deriv (fun s => u s x) t +
              (1 / 2) * traceTimeDerivMetric (I := I) g t x * u t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g t)) *
          evolvingCutoffMass (I := I) (M := M) g cutoff t -
        evolvingLocalizedIntegral (I := I) (M := M) g cutoff u t *
          (∫ x, cutoff x ^ 2 *
              ((1 / 2) * traceTimeDerivMetric (I := I) g t x)
            ∂(riemannianMeasureFamily (I := I) (M := M) g t))) /
        evolvingCutoffMass (I := I) (M := M) g cutoff t ^ 2) t := by
  have hnum := hasDerivAt_evolvingLocalizedIntegral
    (I := I) (M := M) g cutoff u t hg hcutoff hu
  have hden := hasDerivAt_evolvingCutoffMass
    (I := I) (M := M) g cutoff t hg hcutoff
  simpa only [evolvingLocalizedAverage] using hnum.div hden hmass

end DifferentialGeometry.Analysis.Parabolic.Moser

end
