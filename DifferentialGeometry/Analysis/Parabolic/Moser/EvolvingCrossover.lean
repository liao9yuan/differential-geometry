import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLogTail
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [I.Boundaryless] in
theorem localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | level < u z.1 z.2} ≤
      C.toReal * ∫ t in a..b,
        evolvingLocalizedSuperlevelMass
          (I := I) (M := M) g cutoff.toFun u t level := by
  let fixed : ℝ → ℝ := fun t =>
    ∫ x in {x : M | level < u t x}, cutoff.toFun x ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let moving : ℝ → ℝ := fun t =>
    evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g cutoff.toFun u t level
  have hfixed_int : IntervalIntegrable fixed volume a b := by
    simpa only [fixed, localizedSuperlevelMass, smoothScalarSlice_toFun] using
      intervalIntegrable_localizedSuperlevelMass
        (I := I) (M := M) q cutoff u hu (fun _ => level)
          continuous_const a b
  have hmoving_int : IntervalIntegrable moving volume a b := by
    simpa only [moving] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff.toFun u hu (fun _ => level)
          continuous_const hg cutoff.smooth a b
  have hpoint : ∀ t ∈ Icc a b, fixed t ≤ C.toReal * moving t := by
    intro t ht
    let μ := riemannianMeasureFamily (I := I) (M := M) g t
    let S : Set M := {x | level < u t x}
    let f : M → ℝ := fun x => cutoff.toFun x ^ 2
    letI : IsFiniteMeasure μ := by
      dsimp only [μ, riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    have hf_int : Integrable f (C • μ) :=
      cutoff.smooth.continuous.pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure
      (Measure.restrict_mono_measure (hvolume t ht) S)
      (ae_of_all _ fun x => sq_nonneg (cutoff.toFun x)) hf_int.restrict
    rw [Measure.restrict_smul, integral_smul_measure] at hmono
    simpa only [fixed, moving, evolvingLocalizedSuperlevelMass, μ, S, f,
      smul_eq_mul] using hmono
  have hmono : (∫ t in a..b, fixed t) ≤
      ∫ t in a..b, C.toReal * moving t :=
    intervalIntegral.integral_mono_on hab hfixed_int
      (hmoving_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [localizedSpacetimeMeasure_real_superlevel cutoff hab
    (fun z => u z.1 z.2) hu.continuous]
  simpa only [fixed, moving] using hmono

omit [I.Boundaryless] in
theorem localizedSpacetimeMeasure_real_sublevel_le_evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (cutoff : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b level t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    (localizedSpacetimeMeasure (I := I) (M := M) cutoff a b).real
        {z | u z.1 z.2 < level} ≤
      C.toReal * ∫ t in a..b,
        evolvingLocalizedSublevelMass
          (I := I) (M := M) g cutoff.toFun u t level := by
  have h :=
    localizedSpacetimeMeasure_real_superlevel_le_evolvingLocalizedSuperlevelMass
      (I := I) (M := M) g cutoff (fun t x => -u t x) hu.neg hab hg C hC
        hvolume (level := -level)
  simpa only [neg_lt_neg_iff, evolvingLocalizedSuperlevelMass,
    evolvingLocalizedSublevelMass] using h

end DifferentialGeometry.Analysis.Parabolic.Moser

end
