import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCrossover
import DifferentialGeometry.Analysis.Parabolic.Moser.SmallExponentLocalBoundedness

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

def separatedCylinderHarnackFactor
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho averagingCutoff : SmoothScalar g)
    (C p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ) : ℝ :=
  moserPositiveExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p A earlyLower earlyUpper b innerLower innerUpper *
    moserPositiveExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p c lateLower lateUpper d innerLower innerUpper *
    canonicalBombieriGiustiCrossoverBound (I := I) (M := M)
      g hdim rho averagingCutoff C p A b τ c d D B lower upper

theorem separatedCylinderHarnackFactor_nonneg
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho averagingCutoff : SmoothScalar g)
    {C p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ} (hp : 0 < p) :
    0 ≤ separatedCylinderHarnackFactor (I := I) (M := M)
      g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
        lateLower lateUpper d D B lower upper innerLower innerUpper := by
  unfold separatedCylinderHarnackFactor
  exact mul_nonneg
    (mul_nonneg
      (moserPositiveExponentLocalBoundFactor_nonneg
        g hdim rho hp)
      (moserPositiveExponentLocalBoundFactor_nonneg
        g hdim rho hp))
    (by unfold canonicalBombieriGiustiCrossoverBound; positivity)

theorem harnack_on_separated_cylinders
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p A earlyLower earlyUpper b τ c lateLower lateUpper d D B
      lower upper innerLower innerUpper : ℝ}
    (hp : 0 < p) (hp_one : p < 1)
    (hAearly : A < earlyLower) (hearly : earlyLower ≤ earlyUpper)
    (hearlyb : earlyUpper < b) (hbτ : b < τ)
    (hτc : τ < c) (hclate : c < lateLower)
    (hlate : lateLower ≤ lateUpper) (hlated : lateUpper < d)
    (hdD : d < D) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) (hupperInner : upper ≤ innerLower)
    (hinner : innerLower < innerUpper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hearlyMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hearlyMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (hlateMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hlateMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      deriv (fun q ↦ u q x) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x) :
    ∀ t ∈ Icc earlyLower earlyUpper, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun x ≠ 0 →
      ∀ q ∈ Icc lateLower lateUpper, ∀ y : M,
        (bombieriGiustiSpatialCutoff rho innerLower innerUpper 0).toFun y ≠ 0 →
        u t x ≤
          separatedCylinderHarnackFactor (I := I) (M := M)
              g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
                lateLower lateUpper d D B lower upper innerLower innerUpper *
            u q y := by
  let v : ℝ → M → ℝ := fun t x ↦ (u t x)⁻¹
  let earlyNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    (bombieriGiustiSpatialCutoff rho lower upper 0) u p A b
  let lateNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    (bombieriGiustiSpatialCutoff rho lower upper 0) v p c d
  let earlyFactor := moserPositiveExponentLocalBoundFactor (I := I) (M := M)
    g hdim rho p A earlyLower earlyUpper b innerLower innerUpper
  let lateFactor := moserPositiveExponentLocalBoundFactor (I := I) (M := M)
    g hdim rho p c lateLower lateUpper d innerLower innerUpper
  let crossoverBound := canonicalBombieriGiustiCrossoverBound (I := I) (M := M)
    g hdim rho averagingCutoff C p A b τ c d D B lower upper
  have houterSpatial :
      bombieriGiustiDescendingLevel lower upper 1 < upper := by
    simpa only [bombieriGiustiDescendingLevel_zero] using
      bombieriGiustiDescendingLevel_strictAnti hlowerUpper
        (Nat.zero_lt_succ 0)
  have hbD : b ≤ D :=
    hbτ.le.trans (hτc.le.trans (hclate.le.trans
      (hlate.trans (hlated.le.trans hdD.le))))
  have hAc : A ≤ c :=
    hAearly.le.trans (hearly.trans (hearlyb.le.trans (hbτ.le.trans hτc.le)))
  have hv : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M ↦ v z.1 z.2) := by
    simpa only [v, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hvpos : ∀ t x, 0 < v t x := fun t x ↦ inv_pos.mpr (hpos t x)
  have hvpde : ∀ t ∈ Icc c d, ∀ x : M,
      deriv (fun s ↦ v s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).smooth x := by
    intro t ht x
    have h := rpow_subsolution_of_supersolution
      (I := I) (M := M) g u (fun _ _ ↦ 0) hu hpos
      (q := -1) (by norm_num) (t := t) (x := x)
      (by simpa using (hpde t ⟨hAc.trans ht.1, ht.2.trans hdD.le⟩ x).ge)
    simpa only [v, Real.rpow_neg_one, rpowSource, mul_zero, add_zero] using h
  have hnorm : earlyNorm * lateNorm ≤ crossoverBound := by
    simpa only [earlyNorm, lateNorm, v, crossoverBound] using
      localizedSpacetimeRpowNorm_mul_inv_le_canonicalBombieriGiustiCrossover_of_supersolution
        (I := I) (M := M) g hdim rho outer averagingCutoff C hC hP
          u hu hpos hp hp_one (hAearly.le.trans (hearly.trans hearlyb.le)) hbτ
          hτc (hclate.le.trans (hlate.trans hlated.le)) hdD hB hlowerUpper
          hrho hearlyMeasure hearlyMeasure_le_one hlateMeasure
          hlateMeasure_le_one houter hmass
          (fun t ht x ↦ (hpde t ht x).ge)
  have hearlyFactor : 0 ≤ earlyFactor := by
    exact moserPositiveExponentLocalBoundFactor_nonneg g hdim rho hp
  have hlateFactor : 0 ≤ lateFactor := by
    exact moserPositiveExponentLocalBoundFactor_nonneg g hdim rho hp
  have hearlyNorm : 0 ≤ earlyNorm := by
    exact localizedSpacetimeRpowNorm_nonneg _ u (fun t x ↦ (hpos t x).le) p A b
  intro t ht x hx q hq y hy
  have hlocalEarly : u t x ≤ earlyFactor * earlyNorm := by
    simpa [earlyFactor, earlyNorm, bombieriGiustiSpatialCutoff] using
      local_boundedness_of_subsolution_rpow
        (I := I) (M := M) g hdim rho u hu hpos hp hAearly hearly hearlyb
          houterSpatial hupperInner hinner
          (fun s hs z ↦ (hpde s ⟨hs.1, hs.2.trans hbD⟩ z).le)
          t ht x hx
  have hlocalLate : (u q y)⁻¹ ≤ lateFactor * lateNorm := by
    simpa [lateFactor, lateNorm, v, bombieriGiustiSpatialCutoff] using
      local_boundedness_of_subsolution_rpow
        (I := I) (M := M) g hdim rho v hv hvpos hp hclate hlate hlated
          houterSpatial hupperInner hinner hvpde q hq y hy
  have hpointProduct : u t x * (u q y)⁻¹ ≤
      (earlyFactor * earlyNorm) * (lateFactor * lateNorm) :=
    mul_le_mul hlocalEarly hlocalLate (inv_pos.mpr (hpos q y)).le
      (mul_nonneg hearlyFactor hearlyNorm)
  have hbound : u t x * (u q y)⁻¹ ≤
      earlyFactor * lateFactor * crossoverBound := by
    calc
      u t x * (u q y)⁻¹ ≤
          (earlyFactor * earlyNorm) * (lateFactor * lateNorm) := hpointProduct
      _ = (earlyFactor * lateFactor) * (earlyNorm * lateNorm) := by ring
      _ ≤ (earlyFactor * lateFactor) * crossoverBound :=
        mul_le_mul_of_nonneg_left hnorm (mul_nonneg hearlyFactor hlateFactor)
  calc
    u t x = (u t x * (u q y)⁻¹) * u q y := by
      field_simp [ne_of_gt (hpos q y)]
    _ ≤ (earlyFactor * lateFactor * crossoverBound) * u q y :=
      mul_le_mul_of_nonneg_right hbound (hpos q y).le
    _ = separatedCylinderHarnackFactor (I := I) (M := M)
          g hdim rho averagingCutoff C p A earlyLower earlyUpper b τ c
            lateLower lateUpper d D B lower upper innerLower innerUpper *
          u q y := by
      rfl

end DifferentialGeometry.Analysis.Parabolic.Moser

end
