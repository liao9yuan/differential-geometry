import DifferentialGeometry.Analysis.Parabolic.Energy.EvolvingCaccioppoli
import DifferentialGeometry.Analysis.Parabolic.Moser.Sobolev


noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem evolving_localized_parabolic_sobolev_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) :
    ∫ x, |cutoff x * u t x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) ≤
      localizedSobolevConstant (I := I) (M := M) (g t) hdim *
        evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ^
          (2 / (Module.finrank ℝ E : ℝ)) *
        (evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
          evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u t +
          evolvingCutoffGradientError (I := I) (M := M) g cutoff u t) := by
  let cutoffSlice : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let uSlice : SmoothScalar (g t) :=
    smoothScalarSlice (I := I) (g t) u hu t
  have hfixed := localized_parabolic_sobolev_le
    (I := I) (M := M) (g t) hdim cutoffSlice uSlice
  simpa only [cutoffSlice, uSlice, smoothScalarSlice_toFun,
    riemannianMeasureFamily_def, localizedL2Mass,
    localizedDirichletEnergy, cutoffGradientError,
    evolvingLocalizedL2Mass, evolvingLocalizedDirichletEnergy,
    evolvingCutoffGradientError] using hfixed

theorem evolving_localized_parabolic_sobolev_time_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b C S t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hC : 0 ≤ C)
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hmass_le : ∀ t ∈ Icc a b,
      evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ≤ S)
    (hdirichlet : ContinuousOn
      (evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u)
      (Icc a b))
    (herror : ContinuousOn
      (evolvingCutoffGradientError (I := I) (M := M) g cutoff u)
      (Icc a b)) :
    (∫ t in a..b, ∫ x,
        |cutoff x * u t x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * S ^ (2 / (Module.finrank ℝ E : ℝ)) *
        ∫ t in a..b,
          evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
            evolvingLocalizedDirichletEnergy
              (I := I) (M := M) g cutoff u t +
            evolvingCutoffGradientError (I := I) (M := M) g cutoff u t := by
  let lhs : ℝ → ℝ := fun t =>
    ∫ x, |cutoff x * u t x| ^
      (2 + 4 / (Module.finrank ℝ E : ℝ))
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  let mass : ℝ → ℝ :=
    evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u
  let dirichlet : ℝ → ℝ :=
    evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u
  let error : ℝ → ℝ :=
    evolvingCutoffGradientError (I := I) (M := M) g cutoff u
  let energy : ℝ → ℝ := fun t => mass t + dirichlet t + error t
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by linarith
  have hcritical : 0 ≤ 2 + 4 / (Module.finrank ℝ E : ℝ) := by
    positivity
  have hintegrand : Continuous (fun p : ℝ × M =>
      |cutoff p.2 * u p.1 p.2| ^
        (2 + 4 / (Module.finrank ℝ E : ℝ))) :=
    (((hcutoff.continuous.comp continuous_snd).mul hu.continuous).abs
      |>.rpow_const (fun _ => Or.inr hcritical))
  have hlhs : ContinuousOn lhs (Icc a b) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc a b)) Set.Subset.rfl)
    · exact hintegrand.continuousOn
  have hmass : ContinuousOn mass (Icc a b) := by
    simpa only [mass] using
      evolvingLocalizedL2Mass_continuousOn
        (I := I) (M := M) g cutoff u isCompact_Icc hg
          hcutoff.continuous hu.continuous
  have henergy : ContinuousOn energy (Icc a b) := by
    simpa only [energy, mass, dirichlet, error] using
      (hmass.add hdirichlet).add herror
  have hmass_nonneg : ∀ t ∈ Icc a b, 0 ≤ mass t := by
    intro t _
    exact evolvingLocalizedL2Mass_nonneg
      (I := I) (M := M) g cutoff u t
  have henergy_nonneg : ∀ t ∈ Icc a b, 0 ≤ energy t := by
    intro t _
    exact add_nonneg
      (add_nonneg
        (evolvingLocalizedL2Mass_nonneg
          (I := I) (M := M) g cutoff u t)
        (evolvingLocalizedDirichletEnergy_nonneg
          (I := I) (M := M) g cutoff u t))
      (evolvingCutoffGradientError_nonneg
        (I := I) (M := M) g cutoff u t)
  have hpoint : ∀ t ∈ Icc a b,
      lhs t ≤ C * mass t ^ (2 / (Module.finrank ℝ E : ℝ)) * energy t := by
    intro t ht
    have hslice := evolving_localized_parabolic_sobolev_le
      (I := I) (M := M) g hdim cutoff hcutoff u hu t
    have hrpow : 0 ≤ mass t ^ (2 / (Module.finrank ℝ E : ℝ)) :=
      Real.rpow_nonneg (hmass_nonneg t ht) _
    have hfactor : 0 ≤ mass t ^ (2 / (Module.finrank ℝ E : ℝ)) * energy t :=
      mul_nonneg hrpow (henergy_nonneg t ht)
    calc
      lhs t ≤ localizedSobolevConstant (I := I) (M := M) (g t) hdim *
          mass t ^ (2 / (Module.finrank ℝ E : ℝ)) * energy t := by
        simpa only [lhs, mass, dirichlet, error, energy] using hslice
      _ ≤ C * mass t ^ (2 / (Module.finrank ℝ E : ℝ)) * energy t := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hSobolev t ht) hfactor
  have htime := intervalIntegral_le_const_mul_sup_rpow
    hab hlhs henergy hC
      (div_nonneg (by norm_num) hdpos.le) hmass_nonneg
      (by simpa only [mass] using hmass_le) henergy_nonneg hpoint
  simpa only [lhs, mass, dirichlet, error, energy] using htime

theorem evolving_localized_parabolic_sobolev_time_le_of_chartGramMatrix_smooth
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b C S t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hC : 0 ≤ C)
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hmass_le : ∀ t ∈ Icc a b,
      evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ≤ S) :
    (∫ t in a..b, ∫ x,
        |cutoff x * u t x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * S ^ (2 / (Module.finrank ℝ E : ℝ)) *
        ∫ t in a..b,
          evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
            evolvingLocalizedDirichletEnergy
              (I := I) (M := M) g cutoff u t +
            evolvingCutoffGradientError (I := I) (M := M) g cutoff u t := by
  apply evolving_localized_parabolic_sobolev_time_le
    (I := I) (M := M) g hdim cutoff hcutoff u hu hab hg hC
      hSobolev hmass_le
  · exact evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  · exact evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu

theorem evolving_localized_parabolic_sobolev_of_energy_bound_le
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b A C t₀ : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hC : 0 ≤ C)
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hmass_le : ∀ t ∈ Icc a b,
      evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ≤ A)
    (hdirichlet : ContinuousOn
      (evolvingLocalizedDirichletEnergy (I := I) (M := M) g cutoff u)
      (Icc a b))
    (herror : ContinuousOn
      (evolvingCutoffGradientError (I := I) (M := M) g cutoff u)
      (Icc a b))
    (henergy_le :
      (∫ t in a..b,
        evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
          evolvingLocalizedDirichletEnergy
            (I := I) (M := M) g cutoff u t +
          evolvingCutoffGradientError (I := I) (M := M) g cutoff u t) ≤ A) :
    (∫ t in a..b, ∫ x,
        |cutoff x * u t x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * A ^ (1 + 2 / (Module.finrank ℝ E : ℝ)) := by
  have htime := evolving_localized_parabolic_sobolev_time_le
    (I := I) (M := M) g hdim cutoff hcutoff u hu hab hg hC
      hSobolev hmass_le hdirichlet herror
  refine htime.trans ?_
  have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by linarith
  have htheta : 0 ≤ 2 / (Module.finrank ℝ E : ℝ) :=
    div_nonneg (by norm_num) hdpos.le
  have hfactor : 0 ≤ C * A ^ (2 / (Module.finrank ℝ E : ℝ)) :=
    mul_nonneg hC (Real.rpow_nonneg hA _)
  calc
    C * A ^ (2 / (Module.finrank ℝ E : ℝ)) *
          (∫ t in a..b,
            evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
              evolvingLocalizedDirichletEnergy
                (I := I) (M := M) g cutoff u t +
              evolvingCutoffGradientError
                (I := I) (M := M) g cutoff u t) ≤
        C * A ^ (2 / (Module.finrank ℝ E : ℝ)) * A :=
      mul_le_mul_of_nonneg_left henergy_le hfactor
    _ = C * A ^ (1 + 2 / (Module.finrank ℝ E : ℝ)) := by
      rw [Real.rpow_add_of_nonneg hA (by norm_num) htheta, Real.rpow_one]
      ring

theorem evolving_localized_parabolic_sobolev_of_energy_bound_le_of_chartGramMatrix_smooth
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff : M → ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a b A C t₀ : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hC : 0 ≤ C)
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hmass_le : ∀ t ∈ Icc a b,
      evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t ≤ A)
    (henergy_le :
      (∫ t in a..b,
        evolvingLocalizedL2Mass (I := I) (M := M) g cutoff u t +
          evolvingLocalizedDirichletEnergy
            (I := I) (M := M) g cutoff u t +
          evolvingCutoffGradientError (I := I) (M := M) g cutoff u t) ≤ A) :
    (∫ t in a..b, ∫ x,
        |cutoff x * u t x| ^
          (2 + 4 / (Module.finrank ℝ E : ℝ))
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C * A ^ (1 + 2 / (Module.finrank ℝ E : ℝ)) := by
  apply evolving_localized_parabolic_sobolev_of_energy_bound_le
    (I := I) (M := M) g hdim cutoff hcutoff u hu hab hA hg hC
      hSobolev hmass_le
  · exact evolvingLocalizedDirichletEnergy_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  · exact evolvingCutoffGradientError_continuousOn
      (I := I) (M := M) g cutoff u isCompact_Icc hg hgram hcutoff hu
  · exact henergy_le

end DifferentialGeometry.Analysis.Parabolic.Moser

end
