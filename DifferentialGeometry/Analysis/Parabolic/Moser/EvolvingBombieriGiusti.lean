import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiForward
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiReciprocal
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingReciprocal

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

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

def canonicalEvolvingEarlyBombieriGiustiReverseCost
    (n : ℕ) (V : ℝ≥0∞) (C p₀ A b τ G B lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalEvolvingForwardMoserReverseCost n V C p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem one_le_canonicalEvolvingEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    (C p₀ A b τ G B lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEvolvingEarlyBombieriGiustiReverseCost
      n V C p₀ A b τ G B lower upper k := by
  exact one_le_canonicalEvolvingForwardMoserReverseCost n V C p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem localizedSpacetimeRpowNorm_le_canonicalEvolvingEarlyBombieriGiustiReverseCost_of_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc A τ,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc A τ, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc A τ, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A τ,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) u p₀ A
            (bombieriGiustiIncreasingLevel b τ k) ≤
        canonicalEvolvingEarlyBombieriGiustiReverseCost
            (Module.finrank ℝ E) V C p₀ A b τ G B lower upper k ^
              (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1)) u p A
              (bombieriGiustiIncreasingLevel b τ (k + 1)) := by
  intro k p hp hpp₀
  let localLower := bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let localUpper := bombieriGiustiDescendingLevel lower upper (2 * k + 1)
  let pivot := bombieriGiustiIncreasingLevel b τ k
  let endpoint := bombieriGiustiIncreasingLevel b τ (k + 1)
  have hpivotEndpoint : pivot < endpoint :=
    bombieriGiustiIncreasingLevel_strictMono hbτ (Nat.lt_succ_self k)
  have hApivot : A ≤ pivot := hAb.trans
    (bombieriGiustiIncreasingLevel_ge hbτ k)
  have hendpointτ : endpoint < τ :=
    bombieriGiustiIncreasingLevel_lt hbτ (k + 1)
  have hlocal : localLower < localUpper :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)
  apply localizedSpacetimeRpowNorm_le_evolvingReverseCost_of_supersolution_of_lt
    (I := I) (M := M) qMetric g hdim rho
      (bombieriGiustiSpatialCutoff rho lower upper k)
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
      u hu hpos V hp hpp₀ hp₀_one hApivot hpivotEndpoint
      hC hG hB hlocal hg hgram
  · intro t ht
    exact hSobolev t ⟨ht.1, ht.2.trans hendpointτ.le⟩
  · intro t ht x
    exact htrace t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · intro t ht x
    exact hrho t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · intro t ht x
    exact hpde t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · exact hVtop
  · intro t ht
    exact hvolume t ⟨ht.1, ht.2.trans hendpointτ.le⟩
  · exact le_rfl
  · intro m _
    exact (moserUpperTimeLevel_lt hpivotEndpoint m).le
  · intro m _ x
    exact bombieriGiustiSpatialCutoff_le_forward_inner
      rho hlowerUpper k m x
  · exact le_rfl
  · exact le_rfl
  · intro x
    exact forward_initial_spatialCutoffBetween_le_bombieriGiustiSpatialCutoff_succ
      rho hlowerUpper k x

def evolvingBombieriGiustiReciprocalGradientCost
    (G lower upper : ℝ) (k : ℕ) : ℝ :=
  16 * CutoffProfile.derivBound ^ 2 *
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
      bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 * G

theorem evolvingBombieriGiustiReciprocalGradientCost_nonneg
    {G lower upper : ℝ} (hG : 0 ≤ G) (k : ℕ) :
    0 ≤ evolvingBombieriGiustiReciprocalGradientCost G lower upper k := by
  unfold evolvingBombieriGiustiReciprocalGradientCost
  positivity

omit [SigmaCompactSpace M] [CompactSpace M] in
theorem spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
    (g : SmoothRiemannianMetric I M) {q : SmoothRiemannianMetric I M}
    (rho : SmoothScalar q) {G lower upper : ℝ}
    (hG : 0 ≤ G)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ G)
    (k j : ℕ) (x : M) :
    g.inner x
        (gradientFun (I := I) g
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j + 1)).toFun x)
        (gradientFun (I := I) g
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j + 1)).toFun x) ≤
      evolvingMoserSpatialGradientCost
          (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
        (spatialMoserCutoff
          (bombieriGiustiReciprocalLocalizer rho lower upper k)
          (2 * j)).toFun x ^ 2 := by
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper k
  let gap := bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
    bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let K := gap⁻¹ ^ 2 * G
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hG
  have hlocalizer : ∀ y : M,
      g.inner y
          (gradFun (I := I) g localizer.toFun y)
          (gradFun (I := I) g localizer.toFun y) ≤ K := by
    intro y
    simpa only [localizer, gap, K] using
      (bombieriGiustiReciprocalLocalizer_inner_grad_self_le
        (I := I) g rho hrho k y)
  have hcutoff := spatialMoserCutoff_succ_gradient_le
    (I := I) g localizer hK hlocalizer (2 * j) x
  calc
    g.inner x
        (gradientFun (I := I) g
          (spatialMoserCutoff localizer (2 * j + 1)).toFun x)
        (gradientFun (I := I) g
          (spatialMoserCutoff localizer (2 * j + 1)).toFun x) ≤
      (CutoffProfile.derivBound ^ 2 * K /
          moserCutoffWidth (2 * j + 1) ^ 2) *
        (spatialMoserCutoff localizer (2 * j)).toFun x ^ 2 := hcutoff
    _ = evolvingMoserSpatialGradientCost
          (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
        (spatialMoserCutoff localizer (2 * j)).toFun x ^ 2 := by
      rw [div_eq_mul_inv, moserCutoffWidth_succ_inv_sq]
      unfold evolvingMoserSpatialGradientCost
        evolvingBombieriGiustiReciprocalGradientCost
      dsimp only [K, gap]
      ring

def canonicalEvolvingLateBombieriGiustiReverseCost
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  max 1 (evolvingReciprocalReverseCost n Vfixed Vmoving C
    (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) B
    (bombieriGiustiDescendingLevel τ c (k + 1))
    (bombieriGiustiLatePivot τ c k)
    (bombieriGiustiIncreasingLevel d D (k + 1)))

theorem one_le_canonicalEvolvingLateBombieriGiustiReverseCost
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving C G B τ c d D lower upper k := by
  exact le_max_left _ _

theorem localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_gradient_bound_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k j t, t ∈ Icc τ D → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff
              (bombieriGiustiReciprocalLocalizer rho lower upper k)
              (2 * j + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff
              (bombieriGiustiReciprocalLocalizer rho lower upper k)
              (2 * j + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost
            (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j)).toFun x ^ 2)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
            (fun t x => (u t x)⁻¹) p
            (bombieriGiustiDescendingLevel τ c (k + 1))
            (bombieriGiustiIncreasingLevel d D (k + 1)) := by
  intro k p hp hpp₀
  let aOuter := bombieriGiustiDescendingLevel τ c (k + 1)
  let aInner := bombieriGiustiDescendingLevel τ c k
  let bInner := bombieriGiustiIncreasingLevel d D k
  let bOuter := bombieriGiustiIncreasingLevel d D (k + 1)
  let pivot := bombieriGiustiLatePivot τ c k
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper k
  let gradientCost := evolvingBombieriGiustiReciprocalGradientCost G lower upper k
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  let reverseCost := evolvingReciprocalReverseCost
    (Module.finrank ℝ E) Vfixed Vmoving C gradientCost B aOuter pivot bOuter
  have haOuterInner : aOuter < aInner :=
    bombieriGiustiDescendingLevel_strictAnti hτc (Nat.lt_succ_self k)
  have hbInnerOuter : bInner < bOuter :=
    bombieriGiustiIncreasingLevel_strictMono hdD (Nat.lt_succ_self k)
  have hτaOuter : τ < aOuter :=
    bombieriGiustiDescendingLevel_gt hτc (k + 1)
  have hbOuterD : bOuter < D :=
    bombieriGiustiIncreasingLevel_lt hdD (k + 1)
  have haInnerc : aInner ≤ c :=
    bombieriGiustiDescendingLevel_le hτc k
  have hdbInner : d ≤ bInner :=
    bombieriGiustiIncreasingLevel_ge hdD k
  have haInnerbInner : aInner ≤ bInner :=
    haInnerc.trans (hcd.trans hdbInner)
  have haOuterPivot : aOuter < pivot := by
    dsimp only [pivot, bombieriGiustiLatePivot]
    linarith
  have hpivotInner : pivot < aInner := by
    dsimp only [pivot, bombieriGiustiLatePivot]
    linarith
  have hpivotbOuter : pivot ≤ bOuter :=
    hpivotInner.le.trans (haInnerbInner.trans hbInnerOuter.le)
  have hmeasureLocalizer : localizedSpacetimeMeasure (I := I) (M := M)
      (spatialMoserCutoff localizer 0) aOuter bOuter ≠ 0 := by
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      haOuterInner.le hbInnerOuter.le
      (bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
        rho hlowerUpper k)
    apply Measure.measure_univ_pos.mp
    have htarget : 0 <
        localizedSpacetimeMeasure (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) aInner bInner
            Set.univ := by
      simpa only [aInner, bInner] using
        (Measure.measure_univ_pos.mpr (hmeasure k))
    exact htarget.trans_le (hdom Set.univ)
  have hreverse :
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialMoserCutoff localizer 0) inv p aOuter bOuter := by
    apply localizedSpacetimeRpowNorm_inv_le_evolvingReciprocalReverseCost_of_volume_le
      (I := I) (M := M) g hdim localizer
        (bombieriGiustiSpatialCutoff rho lower upper k) u hu hpos
        hp hpp₀.le haOuterPivot hpivotbOuter haOuterInner.le hpivotInner
        haInnerbInner hbInnerOuter hB hC
        (evolvingBombieriGiustiReciprocalGradientCost_nonneg hG k) hg hgram
    · intro t ht
      exact hSobolev t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · intro t ht x
      exact hpde t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · intro t ht x
      exact htrace t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · intro j t ht x
      exact hgradient k j t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · exact hVfixedTop
    · exact hVmovingZero
    · exact hVmovingTop
    · intro t ht
      exact hfixedVolume t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · intro t ht
      exact hmovingVolume t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · exact one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
        rho hlowerUpper k
    · exact bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
        rho hlowerUpper k
    · exact hmeasureLocalizer
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  have hmono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) inv hinv hinvpos
      (a := aOuter) (b := bOuter) (c := aOuter) (d := bOuter)
      hp le_rfl le_rfl
      (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k)
  have hexponent : 0 ≤ 1 / p - 1 / p₀ := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp hpp₀.le)
  have hreverseCost : 0 ≤ reverseCost := by
    unfold reverseCost evolvingReciprocalReverseCost
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg
      (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le) _)
      ENNReal.toReal_nonneg
  have hcost : reverseCost ^ (1 / p - 1 / p₀) ≤
      canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) := by
    exact Real.rpow_le_rpow hreverseCost (le_max_right _ _) hexponent
  change localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
    canonicalEvolvingLateBombieriGiustiReverseCost
        (Module.finrank ℝ E) Vfixed Vmoving C G B
          τ c d D lower upper k ^ (1 / p - 1 / p₀) *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
        inv p aOuter bOuter
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
      reverseCost ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter := hreverse
    _ ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_right hcost
        (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv
          (fun t x => (hinvpos t x).le) p aOuter bOuter)
    _ ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
          inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_left hmono
        (Real.rpow_nonneg
          (zero_le_one.trans (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k)) _)

theorem localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
            (fun t x => (u t x)⁻¹) p
            (bombieriGiustiDescendingLevel τ c (k + 1))
            (bombieriGiustiIncreasingLevel d D (k + 1)) := by
  exact
    localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_gradient_bound_of_volume_le
      (I := I) (M := M) qMetric g hdim rho u hu hpos Vfixed Vmoving
        hτc hcd hdD hC hG hB hlowerUpper hg hgram hSobolev hpde htrace
        (fun k j t ht x =>
          spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
            (I := I) (g t) rho hG (hrho t ht) k j x)
        hVfixedTop hVmovingZero hVmovingTop hfixedVolume hmovingVolume hmeasure

end DifferentialGeometry.Analysis.Parabolic.Moser

end
