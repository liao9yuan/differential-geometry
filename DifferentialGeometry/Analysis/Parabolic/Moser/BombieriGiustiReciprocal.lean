import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCylinder
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def bombieriGiustiLatePivot (τ c : ℝ) (k : ℕ) : ℝ :=
  (bombieriGiustiDescendingLevel τ c (k + 1) +
    bombieriGiustiDescendingLevel τ c k) / 2

def canonicalLateBombieriGiustiReverseCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  moserLocalBoundFactor (I := I) (M := M) g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper k) 2
      (bombieriGiustiDescendingLevel τ c (k + 1))
      (bombieriGiustiLatePivot τ c k)
      (bombieriGiustiIncreasingLevel d D (k + 1)) ^ (2 : ℝ)

theorem one_le_canonicalLateBombieriGiustiReverseCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (τ c d D lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
      g hdim rho τ c d D lower upper k := by
  unfold canonicalLateBombieriGiustiReverseCost
  exact Real.one_le_rpow
    (one_le_moserLocalBoundFactor g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper k)
      (by norm_num) _ _ _)
    (by norm_num)

theorem localizedSpacetimeRpowNorm_inv_le_canonicalLateBombieriGiustiReverseCost_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
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
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have ha := bombieriGiustiDescendingLevel_strictAnti hτc
  have hb := bombieriGiustiIncreasingLevel_strictMono hdD
  have haOuterInner : aOuter < aInner := ha (Nat.lt_succ_self k)
  have hbInnerOuter : bInner < bOuter := hb (Nat.lt_succ_self k)
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
  have hpdeOuter : ∀ t ∈ Icc aOuter bOuter, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t := by
    intro t ht x
    exact hpde t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
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
        canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialMoserCutoff localizer 0) inv p aOuter bOuter := by
    simpa only [inv, localizer, aOuter, aInner, bInner, bOuter, pivot,
      canonicalLateBombieriGiustiReverseCost] using
      (localizedSpacetimeRpowNorm_inv_reverse_holder_of_supersolution
        (I := I) (M := M) g hdim localizer
          (bombieriGiustiSpatialCutoff rho lower upper k) u hu hpos
          hp hpp₀.le haOuterPivot hpivotbOuter haOuterInner.le hpivotInner
          haInnerbInner hbInnerOuter
          (one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
            rho hlowerUpper k)
          (bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
            rho hlowerUpper k)
          hmeasureLocalizer hpdeOuter)
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  have hmono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) inv hinv hinvpos
      (a := aOuter) (b := bOuter) (c := aOuter) (d := bOuter)
      hp le_rfl le_rfl
      (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k)
  have hcost : 0 ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
      g hdim rho τ c d D lower upper k :=
    zero_le_one.trans (one_le_canonicalLateBombieriGiustiReverseCost
      g hdim rho τ c d D lower upper k)
  change localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
    canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
        g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
        inv p aOuter bOuter
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
      canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter := hreverse
    _ ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
          inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hcost _)

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t)
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k) / 4))) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k) / 4)) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).smooth x ≤
        deriv (fun q => v q x) t := by
    intro t ht x
    exact centered_exponential_time_rescale_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos τ (hpde t ht x)
  have hbound :=
    late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
      (I := I) (M := M) g
      (bombieriGiustiSpatialCutoff rho lower upper) outer averagingCutoff
      (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
        g hdim rho τ c d D lower upper)
      (bombieriGiustiDescendingLevel τ c)
      (bombieriGiustiIncreasingLevel d D)
      C hC hP u hu hpos (τ := τ) (D := D) hp₀
      (fun k => one_le_canonicalLateBombieriGiustiReverseCost
        g hdim rho τ c d D lower upper k)
      hmeasure hmeasure_le_one
      (fun k => (bombieriGiustiDescendingLevel_strictAnti hτc
        (Nat.lt_succ_self k)).le)
      (fun k => (bombieriGiustiIncreasingLevel_strictMono hdD
        (Nat.lt_succ_self k)).le)
      (bombieriGiustiSpatialCutoff_mono rho hlowerUpper)
      (hτc.le.trans (hcd.trans hdD.le))
      (fun k => (bombieriGiustiDescendingLevel_gt hτc k).le)
      (fun k => (bombieriGiustiIncreasingLevel_lt hdD k).le)
      houter hmass hpde
      (fun k p hp hpp₀ => by
        simpa only [v, rate, center] using
          (localizedSpacetimeRpowNorm_inv_le_canonicalLateBombieriGiustiReverseCost_of_supersolution
            (I := I) (M := M) g hdim rho v hv hvpos hτc hcd hdD
              hlowerUpper hmeasure hvpde k hp hpp₀))
      hsummable
  simpa only [bombieriGiustiDescendingLevel_zero,
    bombieriGiustiIncreasingLevel_zero, v, rate, center] using hbound

end DifferentialGeometry.Analysis.Parabolic.Moser

end
