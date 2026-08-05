import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder

set_option autoImplicit false

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

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def forwardMoserLocalizedMass
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  ∫ t in a..moserUpperTimeLevel τ b k,
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 *
      u t x ^ parabolicMoserExponent n p₀ k
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def forwardMoserNormalizedMass
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k ^
    (1 / parabolicMoserExponent n p₀ k)

def forwardMoserStepCoefficient (q a t₁ t₂ K : ℝ) : ℝ :=
  (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K) + K

def forwardMoserStepFactor
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  localizedSobolevConstant (I := I) (M := M) g hdim ^
      (1 / parabolicMoserExponent n p₀ (k + 1)) *
    forwardMoserStepCoefficient
        (parabolicMoserExponent n p₀ k) a
        (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
        (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) ^
      (1 / parabolicMoserExponent n p₀ k)

theorem forwardMoserStepCoefficient_nonneg
    {q a t₁ t₂ K : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (hat₁ : a ≤ t₁) (ht₁t₂ : t₁ < t₂) (hK : 0 ≤ K) :
    0 ≤ forwardMoserStepCoefficient q a t₁ t₂ K := by
  have hdenom : 0 ≤ 1 - q := sub_nonneg.mpr hq_one.le
  have htime : 0 ≤ timeCutoffDerivConstant / (t₂ - t₁) :=
    div_nonneg timeCutoffDerivConstant_nonneg (sub_nonneg.mpr ht₁t₂.le)
  have hpower : 0 ≤ 2 * q / (1 - q) :=
    div_nonneg (mul_nonneg (by norm_num) hq_pos.le) hdenom
  have hmax : 0 ≤ max 1 (q / (2 * (1 - q))) :=
    zero_le_one.trans (le_max_left _ _)
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith : 0 ≤ t₁ - a + 1) hmax)
      (add_nonneg htime (mul_nonneg hpower hK))) hK

omit [I.Boundaryless] [CompactSpace M] in
theorem forwardMoserLocalizedMass_nonneg
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) {p₀ a τ b : ℝ}
    (haτ : a ≤ τ) (hτb : τ < b) (hu : ∀ t x, 0 ≤ u t x) (k : ℕ) :
    0 ≤ forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k := by
  apply intervalIntegral.integral_nonneg
  · exact haτ.trans (moserUpperTimeLevel_lt hτb k).le
  · intro t _
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hu t x) _)

omit [I.Boundaryless] in
theorem forwardMoserLocalizedMass_succ_le
    (n : ℕ) [NeZero n]
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (haτ : a ≤ τ) (hτb : τ < b) (k : ℕ) :
    forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b (k + 1) ≤
      ∫ t in a..moserUpperTimeLevel τ b (k + 1),
        ∫ x,
          |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
              u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^
            (2 + 4 / (n : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let upper := moserUpperTimeLevel τ b (k + 1)
  let p := parabolicMoserExponent n p₀ (k + 1)
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p ∂μ
  let right : ℝ → ℝ := fun t =>
    ∫ x, |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
      u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcritical : 0 ≤ critical := by
    dsimp only [critical]
    positivity
  have hleft_joint : Continuous (fun z : ℝ × M =>
      (spatialMoserCutoff rho (2 * (k + 1))).toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.comp
      continuous_snd).pow 2 |>.mul
        (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))
  have hright_base : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)|) :=
    (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.comp continuous_snd).mul
      (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))).abs
  have hright_joint : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
    hright_base.rpow_const (fun _ => Or.inr hcritical)
  have haupper : a ≤ upper :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have hleft_cont : ContinuousOn left (Icc a upper) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a upper) μ
      (fun t x => (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hleft_joint.continuousOn
    simpa only [left] using h
  have hright_cont : ContinuousOn right (Icc a upper) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a upper) μ
      (fun t x => |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
        u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical)
      isCompact_Icc hright_joint.continuousOn
    simpa only [right] using h
  have hleft_int : IntervalIntegrable left volume a upper := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le haupper] using hleft_cont
  have hright_int : IntervalIntegrable right volume a upper := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le haupper] using hright_cont
  have hpoint : ∀ t ∈ Icc a upper, left t ≤ right t := by
    intro t _
    have hu_slice : Continuous (u t) :=
      hu.continuous.comp (continuous_const.prodMk continuous_id)
    have hleft_slice : Continuous (fun x : M =>
        (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p) :=
      ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.pow 2).mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))
    have hright_slice : Continuous (fun x : M =>
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
      (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))).abs).rpow_const
          (fun _ => Or.inr hcritical)
    apply integral_mono
      (hleft_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    have heta := spatialMoserCutoff_add_two_sq_le_rpow
      rho (2 * k) x critical
    have hu_pow : 0 ≤ u t x ^ p := Real.rpow_nonneg (hpos t x).le p
    have hidentity := abs_mul_rpow_half_critical n
      (spatialMoserCutoff_mem_Icc rho (2 * k + 1) x).1 (hpos t x) k
      (p₀ := p₀)
    change
      (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p ≤
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    calc
      _ ≤ (spatialMoserCutoff rho (2 * k + 1)).toFun x ^ critical *
          u t x ^ p := mul_le_mul_of_nonneg_right heta hu_pow
      _ = _ := by simpa only [p, critical] using hidentity.symm
  have htime := intervalIntegral.integral_mono_on haupper hleft_int hright_int hpoint
  simpa only [forwardMoserLocalizedMass, left, right, upper, p, critical] using htime

theorem forwardMoserLocalizedMass_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (((moserUpperTimeLevel τ b (k + 1) - a + 1) *
            positiveRpowCommonEnergyBound
              (parabolicMoserExponent (Module.finrank ℝ E) p₀ k)
              (moserUpperTimeLevel τ b (k + 1))
              (moserUpperTimeLevel τ b k)
              (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k))
              (forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
                rho u p₀ a τ b k) +
          (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) *
            forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
              rho u p₀ a τ b k) ^
          parabolicMoserGain (Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let inner := spatialMoserCutoff rho (2 * k + 1)
  let outer := spatialMoserCutoff rho (2 * k)
  let t₁ := moserUpperTimeLevel τ b (k + 1)
  let t₂ := moserUpperTimeLevel τ b k
  let K := spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)
  let L := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hat₁ : a ≤ t₁ := haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have ht₁t₂ : t₁ < t₂ := moserUpperTimeLevel_succ_lt hτb k
  have hK : 0 ≤ K := mul_nonneg
    (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
    (pow_nonneg (by norm_num) _)
  have hL : 0 ≤ L :=
    forwardMoserLocalizedMass_nonneg n rho u haτ hτb
      (fun t x => (hpos t x).le) k
  have hbridge := forwardMoserLocalizedMass_succ_le n rho u hu hpos
    (p₀ := p₀) (a := a) (τ := τ) (b := b) haτ hτb k
  have hreverse := positive_rpow_reverse_holder_step
    (I := I) (M := M) g hdim inner outer u hu hpos
    hq_pos (by simpa only [q, n] using hexponent_one)
    hat₁ ht₁t₂ hK hL
    (fun t ht x => hpde t
      ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩ x)
    (fun x => by
      simpa only [inner, outer] using spatialMoserCutoff_succ_sq_le rho (2 * k) x)
    (fun x => by
      simpa only [inner, outer, K] using
        spatialMoserCutoff_gradient_le (I := I) g rho (2 * k) x)
    (by
      have heq :
          (∫ t in a..t₂,
            localizedL2Mass (I := I) (M := M) outer
              (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
                (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) = L := by
        dsimp only [L, t₂]
        rw [forwardMoserLocalizedMass]
        apply intervalIntegral.integral_congr
        intro t _
        simpa only [outer, q] using localizedL2Mass_rpow_half
          (I := I) (M := M) g (spatialMoserCutoff rho (2 * k))
            u hu hpos (parabolicMoserExponent n p₀ k) t
      exact heq.le)
  calc
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b (k + 1) ≤
        ∫ t in a..t₁,
          ∫ x, |inner.toFun x * u t x ^ (q / 2)| ^
            (2 + 4 / (n : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [n, q, inner, t₁] using hbridge
    _ ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - a + 1) * positiveRpowCommonEnergyBound q t₁ t₂ K L +
          K * L) ^ parabolicMoserGain n) := by
      simpa only [n, parabolicMoserGain] using hreverse
    _ = _ := by
      rfl

theorem forwardMoserLocalizedMass_succ_le_homogeneous_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient
            (parabolicMoserExponent (Module.finrank ℝ E) p₀ k) a
            (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
            (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) *
          forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
            rho u p₀ a τ b k) ^
          parabolicMoserGain (Module.finrank ℝ E) := by
  have h := forwardMoserLocalizedMass_succ_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k hexponent_one
  convert h using 1
  unfold forwardMoserStepCoefficient positiveRpowCommonEnergyBound
    positiveRpowEnergyBound
  ring_nf

theorem forwardMoserNormalizedMass_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      forwardMoserStepFactor (I := I) (M := M) (Module.finrank ℝ E)
        g hdim rho p₀ a τ b k *
        forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let K := spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)
  let coefficient := forwardMoserStepCoefficient q a
    (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k) K
  let L := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  let L' := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b (k + 1)
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hK : 0 ≤ K := mul_nonneg
    (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
    (pow_nonneg (by norm_num) _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq_pos
      (by simpa only [q, n] using hexponent_one)
      (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
      (moserUpperTimeLevel_succ_lt hτb k) hK
  have hL : 0 ≤ L := forwardMoserLocalizedMass_nonneg n rho u haτ hτb
    (fun t x => (hpos t x).le) k
  have hL' : 0 ≤ L' := forwardMoserLocalizedMass_nonneg n rho u haτ hτb
    (fun t x => (hpos t x).le) (k + 1)
  have hstep := forwardMoserLocalizedMass_succ_le_homogeneous_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k hexponent_one
  have hnormalized := normalized_exponent_gain_step
    hL hL' (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim)
    hcoefficient (parabolicMoserGain_pos n) hq_pos
    (by simpa only [L, L', coefficient, q, K, n] using hstep)
  have hexponent : parabolicMoserGain n * q =
      parabolicMoserExponent n p₀ (k + 1) := by
    simpa only [q] using (parabolicMoserExponent_succ n p₀ k).symm
  simpa only [forwardMoserNormalizedMass, forwardMoserStepFactor,
    n, q, K, coefficient, L, L', hexponent, mul_assoc] using hnormalized

theorem forwardMoserStepFactor_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) {p₀ a τ b : ℝ}
    (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b) (k : ℕ)
    (hexponent_one : parabolicMoserExponent n p₀ k < 1) :
    0 ≤ forwardMoserStepFactor (I := I) (M := M) n g hdim rho p₀ a τ b k := by
  have hK : 0 ≤ spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k) :=
    mul_nonneg (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
      (pow_nonneg (by norm_num) _)
  have hcoefficient := forwardMoserStepCoefficient_nonneg
    (parabolicMoserExponent_pos n hp₀ k) hexponent_one
    (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
    (moserUpperTimeLevel_succ_lt hτb k) hK
  exact mul_nonneg (Real.rpow_nonneg
    (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim) _)
    (Real.rpow_nonneg hcoefficient _)

theorem forwardMoserNormalizedMass_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (m : ℕ)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b m ≤
      (∏ k ∈ Finset.range m,
        forwardMoserStepFactor (I := I) (M := M) (Module.finrank ℝ E)
          g hdim rho p₀ a τ b k) *
        forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let X : ℕ → ℝ := fun k =>
    forwardMoserNormalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  let factor : ℕ → ℝ := fun k =>
    forwardMoserStepFactor (I := I) (M := M) n g hdim rho p₀ a τ b k
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    exact forwardMoserStepFactor_nonneg (I := I) (M := M) n g hdim rho
      hp₀ haτ hτb k (by simpa only [n] using hexponents k hk)
  have hstep : ∀ k < m, X (k + 1) ≤ factor k * X k := by
    intro k hk
    exact forwardMoserNormalizedMass_succ_le_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k
      (by simpa only [n] using hexponents k hk)
  simpa only [X, factor, n] using
    (finite_multiplicative_iteration m hfactor hstep)

theorem forward_moser_iteration_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a τ b : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (m : ℕ) :
    let n := Module.finrank ℝ E
    let p₀ := q * parabolicMoserDecay n ^ m
    forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b m ^ (1 / q) ≤
      (∏ k ∈ Finset.range m,
        forwardMoserStepFactor (I := I) (M := M) n
          g hdim rho p₀ a τ b k) *
        forwardMoserLocalizedMass (I := I) (M := M) n
          rho u p₀ a τ b 0 ^ (1 / p₀) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p₀ := q * parabolicMoserDecay n ^ m
  have hp₀ : 0 < p₀ := mul_pos hq_pos (pow_pos (parabolicMoserDecay_pos n) m)
  have hexponents : ∀ k < m, parabolicMoserExponent n p₀ k < 1 := by
    intro k hk
    calc
      parabolicMoserExponent n p₀ k < parabolicMoserExponent n p₀ m :=
        parabolicMoserExponent_strictMono n hp₀ hk
      _ = q := by
        simpa only [p₀] using parabolicMoserExponent_decay_mul_self n q m
      _ < 1 := hq_one
  have h := forwardMoserNormalizedMass_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde m hexponents
  simpa only [forwardMoserNormalizedMass, parabolicMoserExponent_zero,
    p₀, n, parabolicMoserExponent_decay_mul_self] using h

end DifferentialGeometry.Analysis.Parabolic.Moser

end
