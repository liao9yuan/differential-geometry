import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingLogEnergy
import DifferentialGeometry.Analysis.Parabolic.Moser.LogTail

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

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

end DifferentialGeometry.Analysis.Parabolic.Moser

end
