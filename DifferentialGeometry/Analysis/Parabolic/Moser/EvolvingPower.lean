import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingSobolev
import DifferentialGeometry.Analysis.Parabolic.Moser.Power


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

theorem caccioppoli_evolving_rpow_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (cutoff : M → ℝ)
    (u source : ℝ → M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
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
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x) :
    weight b * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ q) b -
        weight a * evolvingLocalizedL2Mass
          (I := I) (M := M) g cutoff (fun s x => u s x ^ q) a +
        ∫ t in a..b, weight t *
          evolvingLocalizedDirichletEnergy
            (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t ≤
      ∫ t in a..b,
        dweight t * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t +
          weight t *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q)
                  (rpowSource q u source) t +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff (fun s x => u s x ^ q) t) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let hsourceq := contMDiff_rpowSource_of_pos hu hsource hpos q
  apply caccioppoli_evolving_of_subsolution
    (I := I) (M := M) g cutoff (fun t x => u t x ^ q)
      (rpowSource q u source) hcutoff huq hsourceq hg hgram hab hdweight
      hweight hweight_nonneg
  · intro t _ x
    exact (Real.rpow_pos_of_pos (hpos t x) q).le
  · intro t ht x
    exact rpow_subsolution
      (I := I) (M := M) (g t) u source hu hpos hq (hpde t ht x)

theorem evolving_rpow_moser_step_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (houter : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ outer)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} (hg : MetricFamilyRegularAt (I := I) g t)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {C : ℝ} (hC : 0 ≤ C)
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A K L : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hSobolev : ∀ t ∈ Icc t₀ t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * evolvingLocalizedL2Mass
            (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s +
          weight s *
            (4 * evolvingCutoffGradientError
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s +
              evolvingLocalizedForcing
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q)
                  (rpowSource q u source) s +
              evolvingLocalizedVolumeDistortion
                (I := I) (M := M) g cutoff (fun r x => u r x ^ q) s)) ≤ A)
    (hgrad : ∀ t ∈ Icc t₀ t₁, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t) cutoff x)
          (gradientFun (I := I) (g t) cutoff x) ≤
        K * outer x ^ 2)
    (houterMass_le :
      (∫ t in t₀..t₁,
        evolvingLocalizedL2Mass
          (I := I) (M := M) g outer (fun s x => u s x ^ q) t) ≤ L) :
    (∫ t in t₀..t₁, ∫ x,
        |cutoff x * u t x ^ q| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * (((t₁ - t₀ + 1) * A + K * L) ^
        (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let sourceq := rpowSource q u source
  have hsourceq : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => sourceq p.1 p.2) := by
    simpa only [sourceq] using contMDiff_rpowSource_of_pos hu hsource hpos q
  have hpdeq : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x ^ q) t ≤
        Δ_g (I := I) (g t)
            (smoothScalarSlice (I := I) (g t)
              (fun s x => u s x ^ q) huq t).smooth x +
          sourceq t x := by
    intro t ht x
    simpa only [huq, sourceq] using rpow_subsolution
      (I := I) (M := M) (g t) u source hu hpos hq (hpde t ht x)
  have henergy := caccioppoli_evolving_inner_energy_of_subsolution
    (I := I) (M := M) g cutoff (fun t x => u t x ^ q) sourceq
      hcutoff huq hsourceq hg hgram hat₀ ht₀t₁ hdweight hweight
      hweight_nonneg hweight_a hweight_inner
      (fun t _ x => (Real.rpow_pos_of_pos (hpos t x) q).le) hpdeq
      (by simpa only [huq, sourceq] using hrhs_le)
  apply evolving_localized_parabolic_sobolev_of_nested_cutoffs_le
    (I := I) (M := M) g hdim cutoff outer hcutoff houter
      (fun t x => u t x ^ q) huq ht₀t₁ hA hC hK hg hgram hSobolev
      henergy.1 henergy.2 hgrad
  simpa only [huq] using houterMass_le

end DifferentialGeometry.Analysis.Parabolic.Moser

end
