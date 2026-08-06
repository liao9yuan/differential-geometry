import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingOscillation

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

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem evolving_log_spatial_energy_differential_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t ≤
      (∫ x, cutoff x ^ 2 * deriv (fun s => Real.log (u s x)) t
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) +
        2 * evolvingCutoffGradientError
          (I := I) (M := M) g cutoff (fun _ _ => 1) t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let hlog := contMDiff_log_of_pos hu hpos
  have hfixed := log_energy_differential_of_supersolution
    (I := I) (M := M) (g t) cutoff_t u hu hpos t hpde
  have hderiv := hasDerivAt_localizedIntegral
    (I := I) (M := M) cutoff_t (fun s x => Real.log (u s x)) hlog t
  rw [hderiv.deriv] at hfixed
  simpa only [evolvingLocalizedDirichletEnergy, localizedDirichletEnergy,
    evolvingCutoffGradientError, cutoffDirichletEnergy,
    riemannianMeasureFamily_def, smoothScalarSlice_toFun, cutoff_t,
    one_pow, one_mul] using hfixed

theorem evolving_log_average_deriv_lower_bound_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t C H : ℝ) (J : Set ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hne : ∃ x, cutoff x ≠ 0)
    (hP : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g cutoff cutoff C J)
    (ht : t ∈ J)
    (htrace : ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    ((1 / 4 : ℝ) * evolvingLocalizedDirichletEnergy
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x)) t -
        2 * evolvingCutoffGradientError
          (I := I) (M := M) g cutoff (fun _ _ => 1) t) /
        evolvingCutoffMass (I := I) (M := M) g cutoff t -
      max 1 C * H ^ 2 ≤
        deriv (evolvingLocalizedAverage
          (I := I) (M := M) g cutoff (fun s x => Real.log (u s x))) t := by
  let μ := riemannianMeasureFamily (I := I) (M := M) g t
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let mass := evolvingCutoffMass (I := I) (M := M) g cutoff t
  let average := evolvingLocalizedAverage
    (I := I) (M := M) g cutoff logu t
  let dirichlet := evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g cutoff logu t
  let cutoffError := evolvingCutoffGradientError
    (I := I) (M := M) g cutoff (fun _ _ => 1) t
  let K := max 1 C
  let trace : M → ℝ := fun x =>
    (1 / 2) * traceTimeDerivMetric (I := I) g t x
  let timeIntegrand : M → ℝ := fun x =>
    cutoff x ^ 2 * deriv (fun s => logu s x) t
  let covarianceIntegrand : M → ℝ := fun x =>
    cutoff x ^ 2 * trace x * (logu t x - average)
  let hlog := contMDiff_log_of_pos hu hpos
  letI : IsFiniteMeasure μ := by
    dsimp only [μ, riemannianMeasureFamily]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  have hmass : 0 < mass := by
    exact evolvingCutoffMass_pos
      (I := I) (M := M) g cutoff t hcutoff.continuous hne
  have hspatial :
      (1 / 2 : ℝ) * dirichlet ≤ ∫ x, timeIntegrand x ∂μ + 2 * cutoffError := by
    simpa only [dirichlet, timeIntegrand, cutoffError, logu, μ] using
      evolving_log_spatial_energy_differential_of_supersolution
        (I := I) (M := M) g cutoff u hu hpos t hcutoff hpde
  have hcovariance :
      -(1 / 4 : ℝ) * dirichlet - K * H ^ 2 * mass ≤
        ∫ x, covarianceIntegrand x ∂μ := by
    simpa only [dirichlet, K, mass, covarianceIntegrand, trace, logu, average, μ]
      using evolving_volume_covariance_lower_bound_of_poincare
        (I := I) (M := M) g cutoff cutoff logu t C H J hg hcutoff
          (HasCompactSupport.of_compactSpace _) hlog hP ht htrace
  let F : C^∞⟮(modelWithCornersSelf ℝ ℝ).prod I, ℝ × M; ℝ⟯ :=
    ⟨fun p => logu p.1 p.2, hlog⟩
  have htime : Continuous (fun x : M => deriv (fun s => logu s x) t) := by
    exact ((DifferentialGeometry.contMDiff_partial_deriv_fst I F).comp
      (contMDiff_const.prodMk contMDiff_id)).continuous
  have htrace_cont : Continuous trace :=
    continuous_const.mul
      (traceTimeDerivMetric_continuous (I := I) (M := M) hg)
  have hlog_t : Continuous (logu t) :=
    (hlog.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have htime_int : Integrable timeIntegrand μ := by
    exact ((hcutoff.continuous.pow 2).mul htime).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcovariance_int : Integrable covarianceIntegrand μ := by
    exact (((hcutoff.continuous.pow 2).mul htrace_cont).mul
      (hlog_t.sub continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hsum :
      (1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass ≤
        ∫ x, cutoff x ^ 2 *
          (deriv (fun s => logu s x) t +
            trace x * (logu t x - average)) ∂μ := by
    calc
      (1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass =
          ((1 / 2 : ℝ) * dirichlet - 2 * cutoffError) +
            (-(1 / 4 : ℝ) * dirichlet - K * H ^ 2 * mass) := by ring
      _ ≤ (∫ x, timeIntegrand x ∂μ) +
          ∫ x, covarianceIntegrand x ∂μ := by
            exact add_le_add (by linarith) hcovariance
      _ = ∫ x, cutoff x ^ 2 *
          (deriv (fun s => logu s x) t +
            trace x * (logu t x - average)) ∂μ := by
            rw [← integral_add htime_int hcovariance_int]
            exact integral_congr_ae (ae_of_all μ fun x => by
              dsimp only [timeIntegrand, covarianceIntegrand]
              ring)
  have haverage := deriv_evolvingLocalizedAverage_eq_integral_centered
    (I := I) (M := M) g cutoff logu t hg hcutoff hlog hmass.ne'
  have hnormalized :
      ((1 / 4 : ℝ) * dirichlet - 2 * cutoffError) / mass - K * H ^ 2 =
        ((1 / 4 : ℝ) * dirichlet - 2 * cutoffError - K * H ^ 2 * mass) /
          mass := by
    field_simp [hmass.ne']
  rw [hnormalized]
  rw [haverage]
  apply (div_le_div_iff_of_pos_right hmass).2
  simpa only [logu, mass, average, trace, μ] using hsum

end DifferentialGeometry.Analysis.Parabolic.Moser

end
