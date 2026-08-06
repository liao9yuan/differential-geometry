import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLogEnergy
import DifferentialGeometry.Analysis.Parabolic.Moser.LogTail

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

private theorem mul_dirichlet_le_mul_mass_bound_normalized
    {C D m W : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 0 < m) (hmW : m ≤ W) :
    C * D ≤ (C * W) * (D / m) := by
  have hD_eq : D = m * (D / m) := by
    field_simp [hm.ne']
  have hnormalized : 0 ≤ D / m := div_nonneg hD hm.le
  have hscaled := mul_le_mul_of_nonneg_right hmW hnormalized
  calc
    C * D = C * (m * (D / m)) := congrArg (fun x : ℝ => C * x) hD_eq
    _ ≤ C * (W * (D / m)) := mul_le_mul_of_nonneg_left hscaled hC
    _ = (C * W) * (D / m) := by ring

def evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ) : ℝ :=
  ∫ x in {x : M | level < u t x}, cutoff x ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ) : ℝ :=
  ∫ x in {x : M | u t x < level}, cutoff x ^ 2
    ∂(riemannianMeasureFamily (I := I) (M := M) g t)

omit [I.Boundaryless] in
theorem intervalIntegrable_evolvingLocalizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t (level t)) volume a b := by
  exact intervalIntegrable_evolvingLocalizedSuperlevelIntegral
    (I := I) (M := M) g cutoff u level hg hcutoff.continuous
      hu.continuous hlevel a b

omit [I.Boundaryless] in
theorem intervalIntegrable_evolvingLocalizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (level : ℝ → ℝ) (hlevel : Continuous level) {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t => evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t (level t)) volume a b := by
  exact intervalIntegrable_evolvingLocalizedSublevelIntegral
    (I := I) (M := M) g cutoff u level hg hcutoff.continuous
      hu.continuous hlevel a b

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSuperlevelMass_eq_localizedSuperlevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (u t)) :
    evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t level =
      localizedSuperlevelMass (I := I) (M := M)
        (g := g t) ⟨cutoff, hcutoff⟩ ⟨u t, hu⟩ level := by
  rfl

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingLocalizedSublevelMass_eq_localizedSublevelMass
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ) (t level : ℝ)
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (u t)) :
    evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t level =
      localizedSublevelMass (I := I) (M := M)
        (g := g t) ⟨cutoff, hcutoff⟩ ⟨u t, hu⟩ level := by
  rfl

omit [I.Boundaryless] in
theorem evolving_superlevel_chebyshev_of_center
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (t center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r) (hlevel : center + r ≤ level) :
    r ^ 2 * evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingLocalizedL2Deviation
        (I := I) (M := M) g cutoff u center t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have h := localized_superlevel_chebyshev_of_center
    (I := I) (M := M) cutoff_t u_t center hr hlevel
  simpa only [evolvingLocalizedSuperlevelMass, localizedSuperlevelMass,
    evolvingLocalizedL2Deviation, localizedL2Deviation,
    riemannianMeasureFamily_def, cutoff_t, u_t] using h

omit [I.Boundaryless] in
theorem evolving_sublevel_chebyshev_of_center
    (g : ℝ → SmoothRiemannianMetric I M) (cutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hcutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ cutoff)
    (t center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r) (hlevel : level ≤ center - r) :
    r ^ 2 * evolvingLocalizedSublevelMass
        (I := I) (M := M) g cutoff u t level ≤
      evolvingLocalizedL2Deviation
        (I := I) (M := M) g cutoff u center t := by
  let cutoff_t : SmoothScalar (g t) := ⟨cutoff, hcutoff⟩
  let u_t : SmoothScalar (g t) :=
    ⟨u t, hu.comp (contMDiff_const.prodMk contMDiff_id)⟩
  have h := localized_sublevel_chebyshev_of_center
    (I := I) (M := M) cutoff_t u_t center hr hlevel
  simpa only [evolvingLocalizedSublevelMass, localizedSublevelMass,
    evolvingLocalizedL2Deviation, localizedL2Deviation,
    riemannianMeasureFamily_def, cutoff_t, u_t] using h

omit [I.Boundaryless] in
theorem evolving_superlevel_tail_of_poincareAtAverage
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (C : ℝ) (J : Set ℝ)
    (hP : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff C J)
    (t : ℝ) (ht : t ∈ J) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff u t + r ≤ level) :
    r ^ 2 * evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff u t level ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff u t := by
  let u_t := smoothScalarSlice (I := I) (g t) u hu t
  have hchebyshev := evolving_superlevel_chebyshev_of_center
    (I := I) (M := M) g deviationCutoff u hu hdeviationCutoff t
      (evolvingLocalizedAverage
        (I := I) (M := M) g averagingCutoff u t) hr hlevel
  exact hchebyshev.trans (by
    simpa only [u_t, smoothScalarSlice_toFun] using hP t ht u_t)

omit [I.Boundaryless] in
theorem evolving_sublevel_tail_of_poincareAtAverage
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (C : ℝ) (J : Set ℝ)
    (hP : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff C J)
    (t : ℝ) (ht : t ∈ J) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff u t - r) :
    r ^ 2 * evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff u t level ≤
      C * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff u t := by
  let u_t := smoothScalarSlice (I := I) (g t) u hu t
  have hchebyshev := evolving_sublevel_chebyshev_of_center
    (I := I) (M := M) g deviationCutoff u hu hdeviationCutoff t
      (evolvingLocalizedAverage
        (I := I) (M := M) g averagingCutoff u t) hr hlevel
  exact hchebyshev.trans (by
    simpa only [u_t, smoothScalarSlice_toFun] using hP t ht u_t)

theorem early_evolving_log_superlevel_tail_with_center_gap_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base : ℝ) {a τ s t₀ r : ℝ}
    (haτ : a ≤ τ) (hs : s ∈ Icc a τ) (hr : 0 ≤ r)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
        evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base s + r) ^ 2 *
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) + r) ≤
      Ctail * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff
          (fun q x => Real.log (u q x)) s := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let driftIntegral : ℝ → ℝ := fun t => ∫ q in base..t,
    evolvingLogCenterDrift
      (I := I) (M := M) g averagingCutoff Ccenter H q
  let gap := shifted τ - shifted s + r
  let level := shifted τ - driftIntegral s + r
  let hlog := contMDiff_log_of_pos hu hpos
  have hmono := evolvingShiftedLogCenter_monotoneOn_of_supersolution
    (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base hg hgram
      haveragingCutoff hne hPcenter htrace hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff logu s + gap ≤ level := by
    dsimp only [gap, level, shifted, driftIntegral, logu]
    simp only [evolvingShiftedLogCenter]
    ring_nf
    exact le_rfl
  simpa only [gap, level, shifted, driftIntegral, logu] using
    evolving_superlevel_tail_of_poincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff logu hlog
        hdeviationCutoff Ctail (Icc a τ) hPtail s hs hgap hlevel

theorem late_evolving_log_sublevel_tail_with_center_gap_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base : ℝ) {τ b s t₀ r : ℝ}
    (hτb : τ ≤ b) (hs : s ∈ Icc τ b) (hr : 0 ≤ r)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base s -
        evolvingShiftedLogCenter
          (I := I) (M := M) g averagingCutoff u Ccenter H base τ + r) ^ 2 *
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) - r) ≤
      Ctail * evolvingLocalizedDirichletEnergy
        (I := I) (M := M) g averagingCutoff
          (fun q x => Real.log (u q x)) s := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let shifted := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let driftIntegral : ℝ → ℝ := fun t => ∫ q in base..t,
    evolvingLogCenterDrift
      (I := I) (M := M) g averagingCutoff Ccenter H q
  let gap := shifted s - shifted τ + r
  let level := shifted τ - driftIntegral s - r
  let hlog := contMDiff_log_of_pos hu hpos
  have hmono := evolvingShiftedLogCenter_monotoneOn_of_supersolution
    (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base hg hgram
      haveragingCutoff hne hPcenter htrace hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : level ≤ evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff logu s - gap := by
    dsimp only [gap, level, shifted, driftIntegral, logu]
    simp only [evolvingShiftedLogCenter]
    ring_nf
    exact le_rfl
  simpa only [gap, level, shifted, driftIntegral, logu] using
    evolving_sublevel_tail_of_poincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff logu hlog
        hdeviationCutoff Ctail (Icc τ b) hPtail s hs hgap hlevel

theorem integrated_early_evolving_log_superlevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base W : ℝ) {a τ t₀ r : ℝ}
    (haτ : a ≤ τ) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc a τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc a τ))
    (htrace : ∀ t ∈ Icc a τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc a τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (∫ s in a..τ,
      evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) + r)) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let center := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let level : ℝ → ℝ := fun s =>
    center τ - (∫ q in base..s,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H q) + r
  let tailMass : ℝ → ℝ := fun s => evolvingLocalizedSuperlevelMass
    (I := I) (M := M) g deviationCutoff logu s (level s)
  let dirichlet : ℝ → ℝ := fun s => evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g averagingCutoff logu s
  let mass : ℝ → ℝ := evolvingCutoffMass
    (I := I) (M := M) g averagingCutoff
  let normalizedEnergy : ℝ → ℝ := fun s => dirichlet s / mass s
  have hcenter_smooth : ContDiff ℝ 1 center :=
    contDiff_evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne
  have hcenter_mono : MonotoneOn center (Icc a τ) := by
    exact evolvingShiftedLogCenter_monotoneOn_of_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne hPcenter htrace hpde
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.add continuous_const
  have htail_int : IntervalIntegrable tailMass volume a τ := by
    simpa only [tailMass, level, logu] using
      intervalIntegrable_evolvingLocalizedSuperlevelMass
        (I := I) (M := M) g deviationCutoff logu
          (contMDiff_log_of_pos hu hpos) level hlevel_cont hg
            hdeviationCutoff a τ
  have htail : ∀ s ∈ Icc a τ,
      (center τ - center s + r) ^ 2 * tailMass s ≤
        (Ctail * W) * normalizedEnergy s := by
    intro s hs
    have hpointwise :=
      early_evolving_log_superlevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H base haτ hs hr.le hg hgram hdeviationCutoff
          haveragingCutoff hne hPcenter hPtail htrace hpde
    have hdirichlet : 0 ≤ dirichlet s :=
      evolvingLocalizedDirichletEnergy_nonneg
        (I := I) (M := M) g averagingCutoff logu s
    have hmass : 0 < mass s := evolvingCutoffMass_pos
      (I := I) (M := M) g averagingCutoff s
        haveragingCutoff.continuous hne
    have hnormalize := mul_dirichlet_le_mul_mass_bound_normalized
      hCtail hdirichlet hmass (hmass_le s hs)
    have hpointwise' :
        (center τ - center s + r) ^ 2 * tailMass s ≤ Ctail * dirichlet s := by
      simpa only [center, tailMass, level, dirichlet, logu] using hpointwise
    have hnormalize' :
        Ctail * dirichlet s ≤ (Ctail * W) * normalizedEnergy s := by
      simpa only [normalizedEnergy, dirichlet, mass] using hnormalize
    exact hpointwise'.trans hnormalize'
  have henergy : ∀ s ∈ Icc a τ,
      (1 / 2 : ℝ) * normalizedEnergy s ≤ 2 * deriv center s := by
    intro s hs
    have hquarter :=
      quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
        (I := I) (M := M) g averagingCutoff u hu hpos s Ccenter H base
          (Icc a τ) hg hgram haveragingCutoff hne hPcenter hs
            (htrace s hs) (hpde s hs)
    change (1 / 2 : ℝ) * (dirichlet s / mass s) ≤ 2 * deriv center s
    change (1 / 4 : ℝ) * dirichlet s / mass s ≤ deriv center s at hquarter
    calc
      (1 / 2 : ℝ) * (dirichlet s / mass s) =
          2 * ((1 / 4 : ℝ) * dirichlet s / mass s) := by ring
      _ ≤ 2 * deriv center s := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff a).trans
        (hmass_le a ⟨le_rfl, haτ⟩)
  have hresult := integral_tail_le_of_center_gap_sq
    center tailMass normalizedEnergy hcenter_smooth haτ hr
      (mul_nonneg hCtail hW) (by norm_num) hcenter_mono
      htail_int htail henergy
  simpa only [tailMass, level, center, logu] using (show
    (∫ s in a..τ, tailMass s) ≤ 4 * Ctail * W / r by
      calc
        (∫ s in a..τ, tailMass s) ≤ 2 * (Ctail * W) * 2 / r := hresult
        _ = 4 * Ctail * W / r := by ring)

theorem integrated_late_evolving_log_sublevel_tail_of_supersolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H base W : ℝ) {τ b t₀ r : ℝ}
    (hτb : τ ≤ b) (hr : 0 < r) (hCtail : 0 ≤ Ctail)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdeviationCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ deviationCutoff)
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ b))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g deviationCutoff averagingCutoff Ctail (Icc τ b))
    (htrace : ∀ t ∈ Icc τ b, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ b,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (∫ s in τ..b,
      evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff
          (fun q x => Real.log (u q x)) s
          (evolvingShiftedLogCenter
              (I := I) (M := M) g averagingCutoff u Ccenter H base τ -
            (∫ q in base..s,
              evolvingLogCenterDrift
                (I := I) (M := M) g averagingCutoff Ccenter H q) - r)) ≤
      4 * Ctail * W / r := by
  let logu : ℝ → M → ℝ := fun q x => Real.log (u q x)
  let center := evolvingShiftedLogCenter
    (I := I) (M := M) g averagingCutoff u Ccenter H base
  let level : ℝ → ℝ := fun s =>
    center τ - (∫ q in base..s,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H q) - r
  let tailMass : ℝ → ℝ := fun s => evolvingLocalizedSublevelMass
    (I := I) (M := M) g deviationCutoff logu s (level s)
  let dirichlet : ℝ → ℝ := fun s => evolvingLocalizedDirichletEnergy
    (I := I) (M := M) g averagingCutoff logu s
  let mass : ℝ → ℝ := evolvingCutoffMass
    (I := I) (M := M) g averagingCutoff
  let normalizedEnergy : ℝ → ℝ := fun s => dirichlet s / mass s
  have hcenter_smooth : ContDiff ℝ 1 center :=
    contDiff_evolvingShiftedLogCenter
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne
  have hcenter_mono : MonotoneOn center (Icc τ b) := by
    exact evolvingShiftedLogCenter_monotoneOn_of_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos Ccenter H base
        hg hgram haveragingCutoff hne hPcenter htrace hpde
  have hdrift := evolvingLogCenterDrift_continuous
    (I := I) (M := M) g averagingCutoff Ccenter H hg hgram
      haveragingCutoff hne
  have hlevel_cont : Continuous level := by
    exact continuous_const.sub
      (intervalIntegral.differentiable_integral_of_continuous hdrift).continuous
        |>.sub continuous_const
  have htail_int : IntervalIntegrable tailMass volume τ b := by
    simpa only [tailMass, level, logu] using
      intervalIntegrable_evolvingLocalizedSublevelMass
        (I := I) (M := M) g deviationCutoff logu
          (contMDiff_log_of_pos hu hpos) level hlevel_cont hg
            hdeviationCutoff τ b
  have htail : ∀ s ∈ Icc τ b,
      (center s - center τ + r) ^ 2 * tailMass s ≤
        (Ctail * W) * normalizedEnergy s := by
    intro s hs
    have hpointwise :=
      late_evolving_log_sublevel_tail_with_center_gap_of_supersolution
        (I := I) (M := M) g deviationCutoff averagingCutoff u hu hpos
          Ccenter Ctail H base hτb hs hr.le hg hgram hdeviationCutoff
          haveragingCutoff hne hPcenter hPtail htrace hpde
    have hdirichlet : 0 ≤ dirichlet s :=
      evolvingLocalizedDirichletEnergy_nonneg
        (I := I) (M := M) g averagingCutoff logu s
    have hmass : 0 < mass s := evolvingCutoffMass_pos
      (I := I) (M := M) g averagingCutoff s
        haveragingCutoff.continuous hne
    have hnormalize := mul_dirichlet_le_mul_mass_bound_normalized
      hCtail hdirichlet hmass (hmass_le s hs)
    have hpointwise' :
        (center s - center τ + r) ^ 2 * tailMass s ≤ Ctail * dirichlet s := by
      simpa only [center, tailMass, level, dirichlet, logu] using hpointwise
    have hnormalize' :
        Ctail * dirichlet s ≤ (Ctail * W) * normalizedEnergy s := by
      simpa only [normalizedEnergy, dirichlet, mass] using hnormalize
    exact hpointwise'.trans hnormalize'
  have henergy : ∀ s ∈ Icc τ b,
      (1 / 2 : ℝ) * normalizedEnergy s ≤ 2 * deriv center s := by
    intro s hs
    have hquarter :=
      quarter_evolving_log_dirichlet_energy_le_shifted_center_deriv_of_supersolution
        (I := I) (M := M) g averagingCutoff u hu hpos s Ccenter H base
          (Icc τ b) hg hgram haveragingCutoff hne hPcenter hs
            (htrace s hs) (hpde s hs)
    change (1 / 2 : ℝ) * (dirichlet s / mass s) ≤ 2 * deriv center s
    change (1 / 4 : ℝ) * dirichlet s / mass s ≤ deriv center s at hquarter
    calc
      (1 / 2 : ℝ) * (dirichlet s / mass s) =
          2 * ((1 / 4 : ℝ) * dirichlet s / mass s) := by ring
      _ ≤ 2 * deriv center s := mul_le_mul_of_nonneg_left hquarter (by norm_num)
  have hW : 0 ≤ W :=
    (evolvingCutoffMass_nonneg
      (I := I) (M := M) g averagingCutoff τ).trans
        (hmass_le τ ⟨le_rfl, hτb⟩)
  have hresult := integral_tail_le_of_center_gap_sq_from_left
    center tailMass normalizedEnergy hcenter_smooth hτb hr
      (mul_nonneg hCtail hW) (by norm_num) hcenter_mono
      htail_int htail henergy
  simpa only [tailMass, level, center, logu] using (show
    (∫ s in τ..b, tailMass s) ≤ 4 * Ctail * W / r by
      calc
        (∫ s in τ..b, tailMass s) ≤ 2 * (Ctail * W) * 2 / r := hresult
        _ = 4 * Ctail * W / r := by ring)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
