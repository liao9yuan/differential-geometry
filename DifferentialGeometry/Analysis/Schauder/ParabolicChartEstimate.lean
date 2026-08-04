import DifferentialGeometry.Analysis.Parabolic.Euclidean.BallInteriorLocalSource
import DifferentialGeometry.Analysis.Schauder.ParabolicChartExtension

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclN (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem parabolic_nondivergence_interior_schauder_estimate_in_euclideanChart_of_small_freeze_defect
    {alpha Ksource Kc Ku KdtimeU Kdu Kd2u Bsource Bc
      Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : EuclN E) {r R Rext : Real}
    (hr : 0 ≤ r) (hrR : r < R) (hRRext : R < Rext)
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (chartCenter : M) (intrinsicU : Real → M → Real)
    (p0 : ParabolicPoint (EuclN E))
    (u dtimeU : Real → BoundedContinuousFunction (EuclN E) Real)
    (du : Real →
      BoundedContinuousFunction (EuclN E) (EuclN E →L[Real] Real))
    (d2u : Real → BoundedContinuousFunction (EuclN E)
      (EuclN E →L[Real] EuclN E →L[Real] Real))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : EuclN E → Real) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : EuclN E → EuclN E →L[Real] Real)
        (d2u s x) x)
    (huCont : Continuous u)
    (hrealize : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ parabolicEuclideanChartRepresentation
        I chartCenter intrinsicU p.time p.space)
      (parabolicCylinder Set.univ (Metric.ball center R)))
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)).restrict
        (parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU)))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R) →
        ‖parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU p‖ ≤ Bsource)
    (Kb Bb : Fin (Module.finrank Real E) → NNReal)
    (A Ka omega : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal)
    (hA : (Matrix.of fun i j : Fin (Module.finrank Real E) =>
      parabolicChartPrincipalCoefficientExtension (I := I)
        center R Rext g chartCenter p0 i j p0).PosDef)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartDriftCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartPotentialCoefficientExtension (I := I)
          center R Rext V chartCenter p0)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartDriftCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPotentialCoefficientExtension (I := I)
          center R Rext V chartCenter p0 p‖ ≤ Bc)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext g chartCenter p0 i j p0 -
          parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext g chartCenter p0 i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0 i j p‖ ≤ A i j)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖d2u p.time p.space‖ ≤ Md2u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ parabolicChartPrincipalCoefficientExtension (I := I)
        center R Rext g chartCenter p0 i j p0)
      hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeInEuclideanChartOn alpha I chartCenter
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)) intrinsicU ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext g chartCenter p0)
        p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        Kdu Ku
        (Bsource + parabolicLowerOrderSupConst Bb Bc Mdu Mu)
        Mdu Mu A Ka omega T := by
  let aext := parabolicChartPrincipalCoefficientExtension (I := I)
    center R Rext g chartCenter p0
  let bext := parabolicChartDriftCoefficientExtension (I := I)
    center R Rext g chartCenter p0
  let cext := parabolicChartPotentialCoefficientExtension (I := I)
    center R Rext V chartCenter p0
  let chartU := parabolicEuclideanChartRepresentation I chartCenter intrinsicU
  let Qlocal := parabolicCylinder (Icc (0 : Real) S) (Metric.ball center R)
  let Qglobal := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (EuclN E))
  let Urealize := parabolicCylinder Set.univ (Metric.ball center R)
  have hR : 0 ≤ R := hr.trans hrR.le
  have hUrealize : IsOpen Urealize :=
    isOpen_parabolicCylinder isOpen_univ Metric.isOpen_ball
  have hQlocalQglobal : Qlocal ⊆ Qglobal := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ p.space⟩
  have hsourceEq : Set.EqOn
      (parabolicNondivergenceOperator aext bext cext (fun t x ↦ u t x))
      (parabolicNondivergenceOperatorInEuclideanChart (I := I)
        g V chartCenter intrinsicU) Qlocal := by
    intro p hp
    have hpU : p ∈ Urealize := ⟨Set.mem_univ p.time, hp.2⟩
    calc
      parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x) p =
          parabolicNondivergenceOperator aext bext cext chartU p :=
        parabolicNondivergenceOperator_congr_of_eqOn_open
          hUrealize aext bext cext (fun t x ↦ u t x) chartU hpU
            (by simpa only [Urealize, chartU] using hrealize)
      _ = parabolicNondivergenceOperatorInEuclideanChart (I := I)
          g V chartCenter intrinsicU p := by
        exact parabolicNondivergenceOperator_coefficientExtension_eq
          (I := I) center hR hRRext g V chartCenter p0 chartU p
            (Metric.ball_subset_closedBall hp.2)
  have hsourceHolder' : HolderWith Ksource alpha
      (Qlocal.restrict
        (parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x))) := by
    have hfun : Qlocal.restrict
        (parabolicNondivergenceOperator aext bext cext
          (fun t x ↦ u t x)) =
        Qlocal.restrict
          (parabolicNondivergenceOperatorInEuclideanChart (I := I)
            g V chartCenter intrinsicU) := by
      funext p
      exact hsourceEq p.2
    rw [hfun]
    simpa only [Qlocal] using hsourceHolder
  have hsourceNorm' : ∀ p, p ∈ Qlocal →
      ‖parabolicNondivergenceOperator aext bext cext
        (fun t x ↦ u t x) p‖ ≤ Bsource := by
    intro p hp
    rw [hsourceEq hp]
    exact hsourceNorm p (by simpa only [Qlocal] using hp)
  have hbLocal : ∀ i, HolderWith (Kb i) alpha
      (Qlocal.restrict (bext i)) := by
    intro i
    exact ((HolderWith.restrict_iff.mp
      (by simpa only [Qglobal, bext] using hb i)).mono hQlocalQglobal).holderWith
  have hcLocal : HolderWith Kc alpha (Qlocal.restrict cext) :=
    ((HolderWith.restrict_iff.mp
      (by simpa only [Qglobal, cext] using hc)).mono hQlocalQglobal).holderWith
  have hbNormLocal : ∀ i p, p ∈ Qlocal → ‖bext i p‖ ≤ Bb i := by
    intro i p hp
    exact hbNorm i p (by simpa only [Qglobal] using hQlocalQglobal hp)
  have hcNormLocal : ∀ p, p ∈ Qlocal → ‖cext p‖ ≤ Bc := by
    intro p hp
    exact hcNorm p (by simpa only [Qglobal] using hQlocalQglobal hp)
  have hestimate :=
    parabolic_nondivergence_ball_interior_schauder_estimate_of_local_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      aext p0 hA bext cext u dtimeU du d2u huTime hu hdu huCont
      (by simpa only [Qlocal] using hsourceHolder')
      (by simpa only [Qlocal] using hsourceNorm')
      Kb Bb A Ka omega
      (by simpa only [Qlocal] using hbLocal)
      (by simpa only [Qlocal] using hcLocal)
      (by simpa only [Qlocal] using hbNormLocal)
      (by simpa only [Qlocal] using hcNormLocal)
      (by simpa only [aext] using ha) (by simpa only [aext] using homega)
      (by simpa only [aext] using haNorm) huHolder hdtimeUHolder hduHolder
      hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
      (by simpa only [aext] using hsmall)
  let Qinner := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  have hQinnerU : Qinner ⊆ Urealize := by
    intro p hp
    exact ⟨Set.mem_univ p.time, Metric.ball_subset_ball hrR.le hp.2⟩
  have hgauge : eParabolicC2HolderGaugeOn alpha Qinner
      (fun t x ↦ u t x) = eParabolicC2HolderGaugeOn alpha Qinner chartU :=
    eParabolicC2HolderGaugeOn_congr_of_eqOn_open
      hUrealize hQinnerU (by simpa only [Urealize, chartU] using hrealize) alpha
  unfold eParabolicC2HolderGaugeInEuclideanChartOn
  rw [← hgauge]
  simpa only [Qinner, aext, bext, cext] using hestimate

end DifferentialGeometry.Analysis.Schauder

end
