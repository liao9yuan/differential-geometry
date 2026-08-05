import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCylinder
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.ForwardIteration

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

def canonicalEarlyBombieriGiustiReverseCost
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ A b τ B lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalForwardMoserReverseCost (I := I) (M := M) n g hdim p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem one_le_canonicalEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ A b τ B lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
      n g hdim p₀ A b τ B lower upper k := by
  exact one_le_canonicalForwardMoserReverseCost n g hdim p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem localizedSpacetimeRpowNorm_le_canonicalEarlyBombieriGiustiReverseCost_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ B lower upper : ℝ}
    (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) u p₀ A
            (bombieriGiustiIncreasingLevel b τ k) ≤
        canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k ^
              (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1)) u p A
              (bombieriGiustiIncreasingLevel b τ (k + 1)) := by
  intro k p hp hpp₀
  let localLower := bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let localUpper := bombieriGiustiDescendingLevel lower upper (2 * k + 1)
  let pivot := bombieriGiustiIncreasingLevel b τ k
  let endpoint := bombieriGiustiIncreasingLevel b τ (k + 1)
  have htime := bombieriGiustiIncreasingLevel_strictMono hbτ
  have hpivotEndpoint : pivot < endpoint := htime (Nat.lt_succ_self k)
  have hApivot : A ≤ pivot := hAb.trans
    (bombieriGiustiIncreasingLevel_ge hbτ k)
  have hendpointτ : endpoint < τ :=
    bombieriGiustiIncreasingLevel_lt hbτ (k + 1)
  have hlocal : localLower < localUpper :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)
  apply localizedSpacetimeRpowNorm_le_canonicalForwardMoserReverseCost_of_supersolution_of_lt
    (I := I) (M := M) g hdim rho
      (bombieriGiustiSpatialCutoff rho lower upper k)
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
      u hu hpos hp hpp₀ hp₀_one hApivot hpivotEndpoint hB hlocal hrho
  · intro t ht x
    exact hpde t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
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

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
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
    {p₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t)
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k) / 4))) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k) / 4)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).smooth x ≤
        deriv (fun q => v q x) t := by
    intro t ht x
    exact centered_exponential_time_rescale_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos τ (hpde t ht x)
  dsimp only
  conv_lhs =>
    rw [show b = bombieriGiustiIncreasingLevel b τ 0 by
      exact (bombieriGiustiIncreasingLevel_zero b τ).symm]
  apply early_localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
    (I := I) (M := M) g
      (bombieriGiustiSpatialCutoff rho lower upper) outer averagingCutoff
      (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
        n g hdim p₀ A b τ B lower upper)
      (fun _ => A) (bombieriGiustiIncreasingLevel b τ)
      C hC hP u hu hpos (A := A) (τ := τ) hp₀
  · intro k
    exact one_le_canonicalEarlyBombieriGiustiReverseCost
      n g hdim p₀ A b τ B lower upper k
  · exact hmeasure
  · exact hmeasure_le_one
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_strictMono hbτ
      (Nat.lt_succ_self k)).le
  · exact bombieriGiustiSpatialCutoff_mono rho hlowerUpper
  · exact hAb.trans hbτ.le
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_lt hbτ k).le
  · exact houter
  · exact hmass
  · exact hpde
  · intro k p hp hpp₀
    simpa only [v, rate, center, n] using
      (localizedSpacetimeRpowNorm_le_canonicalEarlyBombieriGiustiReverseCost_of_supersolution
        (I := I) (M := M) g hdim rho v hv hvpos hp₀_one hAb hbτ hB
          hlowerUpper hrho hvpde k hp hpp₀)
  · simpa only [n] using hsummable

end DifferentialGeometry.Analysis.Parabolic.Moser

end
