import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure

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

def forwardMoserStepCoefficientEnvelope (q a b T K : ℝ) : ℝ :=
  (b - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant * T + (2 * q / (1 - q)) * K) + K

theorem div_one_sub_mono
    {p q : ℝ} (hpq : p ≤ q) (hq : q < 1) :
    p / (1 - p) ≤ q / (1 - q) := by
  rw [div_le_div_iff₀ (sub_pos.mpr (hpq.trans_lt hq)) (sub_pos.mpr hq)]
  nlinarith

theorem forwardMoserStepCoefficient_le_envelope_mul_pow
    {q qbar a t₁ t₂ b T K Kbar : ℝ} (k : ℕ)
    (hq : 0 ≤ q) (hqqbar : q ≤ qbar) (hqbar_one : qbar < 1)
    (hat₁ : a ≤ t₁) (ht₁b : t₁ ≤ b) (ht₁t₂ : t₁ < t₂)
    (hK : 0 ≤ K)
    (htime : (t₂ - t₁)⁻¹ ≤ T * 16 ^ k)
    (hgradient : K ≤ Kbar * 16 ^ k) :
    forwardMoserStepCoefficient q a t₁ t₂ K ≤
      forwardMoserStepCoefficientEnvelope qbar a b T Kbar * 16 ^ k := by
  have hqbar : 0 ≤ qbar := hq.trans hqqbar
  have hq_one : q < 1 := hqqbar.trans_lt hqbar_one
  have hratio : q / (1 - q) ≤ qbar / (1 - qbar) :=
    div_one_sub_mono hqqbar hqbar_one
  have hratio_nonneg : 0 ≤ q / (1 - q) :=
    div_nonneg hq (sub_pos.mpr hq_one).le
  have hratio_bar_nonneg : 0 ≤ qbar / (1 - qbar) :=
    div_nonneg hqbar (sub_pos.mpr hqbar_one).le
  have hsmallRatio : q / (2 * (1 - q)) ≤ qbar / (2 * (1 - qbar)) := by
    rw [div_le_div_iff₀
      (mul_pos (by norm_num) (sub_pos.mpr hq_one))
      (mul_pos (by norm_num) (sub_pos.mpr hqbar_one))]
    nlinarith
  have hmax : max 1 (q / (2 * (1 - q))) ≤
      max 1 (qbar / (2 * (1 - qbar))) := max_le_max_left 1 hsmallRatio
  have hpow_nonneg : 0 ≤ (16 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have htime_nonneg : 0 ≤ timeCutoffDerivConstant / (t₂ - t₁) :=
    div_nonneg timeCutoffDerivConstant_nonneg (sub_pos.mpr ht₁t₂).le
  have htime_bound : timeCutoffDerivConstant / (t₂ - t₁) ≤
      (timeCutoffDerivConstant * T) * 16 ^ k := by
    calc
      timeCutoffDerivConstant / (t₂ - t₁) =
          timeCutoffDerivConstant * (t₂ - t₁)⁻¹ := div_eq_mul_inv _ _
      _ ≤ timeCutoffDerivConstant * (T * 16 ^ k) :=
        mul_le_mul_of_nonneg_left htime timeCutoffDerivConstant_nonneg
      _ = (timeCutoffDerivConstant * T) * 16 ^ k := by ring
  have hlargeRatio : 2 * q / (1 - q) ≤ 2 * qbar / (1 - qbar) := by
    calc
      2 * q / (1 - q) = 2 * (q / (1 - q)) := by ring
      _ ≤ 2 * (qbar / (1 - qbar)) := by gcongr
      _ = 2 * qbar / (1 - qbar) := by ring
  have hlargeRatio_nonneg : 0 ≤ 2 * q / (1 - q) := by
    simpa only [mul_div_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hratio_nonneg
  have hlargeRatio_bar_nonneg : 0 ≤ 2 * qbar / (1 - qbar) := by
    simpa only [mul_div_assoc] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hratio_bar_nonneg
  have hgradient_bound : (2 * q / (1 - q)) * K ≤
      ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by
    calc
      (2 * q / (1 - q)) * K ≤ (2 * qbar / (1 - qbar)) * K :=
        mul_le_mul_of_nonneg_right hlargeRatio hK
      _ ≤ (2 * qbar / (1 - qbar)) * (Kbar * 16 ^ k) :=
        mul_le_mul_of_nonneg_left hgradient hlargeRatio_bar_nonneg
      _ = ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by ring
  have hinside_nonneg : 0 ≤
      timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K :=
    add_nonneg htime_nonneg (mul_nonneg hlargeRatio_nonneg hK)
  have hinside :
      timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K ≤
        (timeCutoffDerivConstant * T +
          (2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by
    calc
      _ ≤ (timeCutoffDerivConstant * T) * 16 ^ k +
          ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k :=
        add_le_add htime_bound hgradient_bound
      _ = _ := by ring
  have houter :
      (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) ≤
        (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) := by
    exact mul_le_mul (by linarith) hmax
      (zero_le_one.trans (le_max_left _ _)) (by linarith)
  have houter_bar_nonneg : 0 ≤
      (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) :=
    mul_nonneg (by linarith) (zero_le_one.trans (le_max_left _ _))
  unfold forwardMoserStepCoefficient forwardMoserStepCoefficientEnvelope
  calc
    (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) *
          (timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K) + K ≤
        ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar)))) *
          ((timeCutoffDerivConstant * T +
            (2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k) +
          Kbar * 16 ^ k := by
      exact add_le_add
        (mul_le_mul houter hinside hinside_nonneg houter_bar_nonneg) hgradient
    _ = ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) *
          (timeCutoffDerivConstant * T +
            (2 * qbar / (1 - qbar)) * Kbar) + Kbar) * 16 ^ k := by ring

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

def nestedForwardMoserMoment
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a : ℝ)
    (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  localizedSpacetimeRpowMoment (I := I) (M := M)
    (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1))) u
    (parabolicMoserExponent n p₀ k) a (upperTime k)

def nestedForwardMoserNorm
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a : ℝ)
    (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  nestedForwardMoserMoment (I := I) (M := M) n rho u p₀ a level upperTime k ^
    (1 / parabolicMoserExponent n p₀ k)

def nestedForwardMoserGradientCost
    (B : ℝ) (level : ℕ → ℝ) (k : ℕ) : ℝ :=
  CutoffProfile.derivBound ^ 2 * B /
    (level (2 * k + 2) - level (2 * k + 1)) ^ 2

def nestedForwardMoserStepFactor
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (B p₀ a : ℝ) (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  localizedSobolevConstant (I := I) (M := M) g hdim ^
      (1 / parabolicMoserExponent n p₀ (k + 1)) *
    forwardMoserStepCoefficient
        (parabolicMoserExponent n p₀ k) a
        (upperTime (k + 1)) (upperTime k)
        (nestedForwardMoserGradientCost B level k) ^
      (1 / parabolicMoserExponent n p₀ k)

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowMoment_gain_le
    (n : ℕ) [NeZero n]
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a b level₁ level₂ level₃ : ℝ}
    (hab : a ≤ b) (hlevel₁₂ : level₁ < level₂)
    (hlevel₂₃ : level₂ < level₃) :
    localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialCutoffBetween rho level₂ level₃) u
        (parabolicMoserGain n * q) a b ≤
      ∫ t in a..b, ∫ x,
        |(spatialCutoffBetween rho level₁ level₂).toFun x *
            u t x ^ (q / 2)| ^ (2 + 4 / (n : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let inner := spatialCutoffBetween rho level₂ level₃
  let middle := spatialCutoffBetween rho level₁ level₂
  let p := parabolicMoserGain n * q
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, inner.toFun x ^ 2 * u t x ^ p ∂μ
  let right : ℝ → ℝ := fun t =>
    ∫ x, |middle.toFun x * u t x ^ (q / 2)| ^ critical ∂μ
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
      inner.toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    (inner.smooth.continuous.comp continuous_snd).pow 2 |>.mul
      (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne')
  have hright_base : Continuous (fun z : ℝ × M =>
      |middle.toFun z.2 * u z.1 z.2 ^ (q / 2)|) :=
    (((middle.smooth.continuous.comp continuous_snd).mul
      (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne'))).abs
  have hright_joint : Continuous (fun z : ℝ × M =>
      |middle.toFun z.2 * u z.1 z.2 ^ (q / 2)| ^ critical) :=
    hright_base.rpow_const fun _ => Or.inr hcritical
  have hleft_cont : ContinuousOn left (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ
      (fun t x => inner.toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hleft_joint.continuousOn
    simpa only [left] using h
  have hright_cont : ContinuousOn right (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ
      (fun t x => |middle.toFun x * u t x ^ (q / 2)| ^ critical)
      isCompact_Icc hright_joint.continuousOn
    simpa only [right] using h
  have hleft_int : IntervalIntegrable left volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hleft_cont
  have hright_int : IntervalIntegrable right volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hright_cont
  have hpoint : ∀ t ∈ Icc a b, left t ≤ right t := by
    intro t _
    have hu_slice : Continuous (u t) :=
      hu.continuous.comp (continuous_const.prodMk continuous_id)
    have hleft_slice : Continuous (fun x : M =>
        inner.toFun x ^ 2 * u t x ^ p) :=
      (inner.smooth.continuous.pow 2).mul
        (hu_slice.rpow_const fun x => Or.inl (hpos t x).ne')
    have hright_slice : Continuous (fun x : M =>
        |middle.toFun x * u t x ^ (q / 2)| ^ critical) :=
      (((middle.smooth.continuous.mul
        (hu_slice.rpow_const fun x => Or.inl (hpos t x).ne')).abs).rpow_const
          fun _ => Or.inr hcritical)
    apply integral_mono
      (hleft_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    have hcutoff := spatialCutoffBetween_sq_le_rpow rho
      hlevel₁₂ hlevel₂₃ critical x
    have hu_pow : 0 ≤ u t x ^ p := Real.rpow_nonneg (hpos t x).le p
    have hidentity := abs_mul_rpow_half_parabolic_gain n
      (spatialCutoffBetween_mem_Icc rho level₁ level₂ x).1 (hpos t x)
      (q := q)
    change inner.toFun x ^ 2 * u t x ^ p ≤
      |middle.toFun x * u t x ^ (q / 2)| ^ critical
    calc
      _ ≤ middle.toFun x ^ critical * u t x ^ p :=
        mul_le_mul_of_nonneg_right (by
          simpa only [inner, middle] using hcutoff) hu_pow
      _ = _ := by
        simpa only [p, critical, middle] using hidentity.symm
  rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
    (I := I) (M := M) inner u hu.continuous hpos hab]
  exact intervalIntegral.integral_mono_on hab hleft_int hright_int hpoint

theorem localizedSpacetimeRpowMoment_gain_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a innerTime outerTime level₀ level₁ level₂ level₃ B : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (haInner : a ≤ innerTime) (hinnerOuter : innerTime < outerTime)
    (hlevel₀₁ : level₀ < level₁) (hlevel₁₂ : level₁ < level₂)
    (hlevel₂₃ : level₂ < level₃) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a outerTime, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    let n := Module.finrank ℝ E
    let K := CutoffProfile.derivBound ^ 2 * B / (level₂ - level₁) ^ 2
    localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialCutoffBetween rho level₂ level₃) u
        (parabolicMoserGain n * q) a innerTime ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient q a innerTime outerTime K *
          localizedSpacetimeRpowMoment (I := I) (M := M)
            (spatialCutoffBetween rho level₀ level₁) u q a outerTime) ^
          parabolicMoserGain n := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let outer := spatialCutoffBetween rho level₀ level₁
  let middle := spatialCutoffBetween rho level₁ level₂
  let inner := spatialCutoffBetween rho level₂ level₃
  let K := CutoffProfile.derivBound ^ 2 * B / (level₂ - level₁) ^ 2
  let L := localizedSpacetimeRpowMoment (I := I) (M := M)
    outer u q a outerTime
  have haOuter : a ≤ outerTime := haInner.trans hinnerOuter.le
  have hK : 0 ≤ K := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      outer u (fun t x => (hpos t x).le) q a outerTime
  have houterMass :
      (∫ t in a..outerTime,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) = L := by
    dsimp only [L]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) outer u hu.continuous hpos haOuter]
    apply intervalIntegral.integral_congr
    intro t _
    simpa only [outer] using localizedL2Mass_rpow_half
      (I := I) (M := M) g
        (spatialCutoffBetween rho level₀ level₁) u hu hpos q t
  have hreverse := positive_rpow_reverse_holder_step
    (I := I) (M := M) g hdim middle outer u hu hpos
      hq_pos hq_one haInner hinnerOuter hK hL hpde
      (fun x => by
        simpa only [middle, outer] using
          spatialCutoffBetween_sq_le rho hlevel₀₁ hlevel₁₂ x)
      (fun x => by
        simpa only [middle, outer, K] using
          spatialCutoffBetween_gradient_le (I := I) g rho
            hlevel₀₁ hlevel₁₂ hB hrho x)
      houterMass.le
  have hbridge := localizedSpacetimeRpowMoment_gain_le n rho u hu hpos
    haInner hlevel₁₂ hlevel₂₃ (q := q)
  change localizedSpacetimeRpowMoment (I := I) (M := M) inner u
      (parabolicMoserGain n * q) a innerTime ≤
    localizedSobolevConstant (I := I) (M := M) g hdim *
      (forwardMoserStepCoefficient q a innerTime outerTime K * L) ^
        parabolicMoserGain n
  calc
    localizedSpacetimeRpowMoment (I := I) (M := M) inner u
          (parabolicMoserGain n * q) a innerTime ≤
        ∫ t in a..innerTime, ∫ x,
          |middle.toFun x * u t x ^ (q / 2)| ^ (2 + 4 / (n : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [inner, middle] using hbridge
    _ ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
        (((innerTime - a + 1) *
            positiveRpowCommonEnergyBound q innerTime outerTime K L + K * L) ^
          parabolicMoserGain n) := by
      simpa only [n, parabolicMoserGain] using hreverse
    _ = localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient q a innerTime outerTime K * L) ^
          parabolicMoserGain n := by
      congr 2
      unfold forwardMoserStepCoefficient positiveRpowCommonEnergyBound
        positiveRpowEnergyBound
      ring

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

theorem nestedForwardMoserNorm_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a B : ℝ} (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (haTime : a ≤ upperTime (k + 1))
    (htime : upperTime (k + 1) < upperTime k)
    (hlevel₀₁ : level (2 * k) < level (2 * k + 1))
    (hlevel₁₂ : level (2 * k + 1) < level (2 * k + 2))
    (hlevel₂₃ : level (2 * k + 2) < level (2 * k + 3))
    (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime (k + 1) ≤
      nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost B level k
  let coefficient := forwardMoserStepCoefficient q a
    (upperTime (k + 1)) (upperTime k) K
  let L := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime k
  let L' := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime (k + 1)
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq_pos
      (by simpa only [q, n] using hexponent_one) haTime htime hK
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ k)
      a (upperTime k)
  have hL' : 0 ≤ L' := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * (k + 1)))
        (level (2 * (k + 1) + 1)))
      u (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ (k + 1))
      a (upperTime (k + 1))
  have hstep₀ := localizedSpacetimeRpowMoment_gain_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hq_pos
      (by simpa only [q, n] using hexponent_one) haTime htime
      hlevel₀₁ hlevel₁₂ hlevel₂₃ hB hrho hpde
  have hstep : L' ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (coefficient * L) ^ parabolicMoserGain n := by
    simpa only [L, L', coefficient, K, q, nestedForwardMoserMoment,
      parabolicMoserExponent_succ, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      n] using hstep₀
  have hnormalized := normalized_exponent_gain_step
    hL hL' (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim)
      hcoefficient (parabolicMoserGain_pos n) hq_pos hstep
  simpa only [nestedForwardMoserNorm, nestedForwardMoserStepFactor,
    L, L', coefficient, K, q, parabolicMoserExponent_succ, n, mul_assoc] using
      hnormalized

theorem nestedForwardMoserStepFactor_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {B p₀ a : ℝ} (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_one : parabolicMoserExponent n p₀ k < 1)
    (haTime : a ≤ upperTime (k + 1))
    (htime : upperTime (k + 1) < upperTime k)
    (hB : 0 ≤ B) :
    0 ≤ nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k := by
  have hK : 0 ≤ nestedForwardMoserGradientCost B level k := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient := forwardMoserStepCoefficient_nonneg
    (parabolicMoserExponent_pos n hp₀ k) hexponent_one haTime htime hK
  exact mul_nonneg
    (Real.rpow_nonneg
      (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim) _)
    (Real.rpow_nonneg hcoefficient _)

theorem nestedForwardMoserNorm_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a B : ℝ} (level upperTime : ℕ → ℝ) (m : ℕ)
    (hp₀ : 0 < p₀)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : a ≤ upperTime m) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime m ≤
      (∏ k ∈ Finset.range m,
        nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let X : ℕ → ℝ := fun k =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime k
  let factor : ℕ → ℝ := fun k =>
    nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserStepFactor_nonneg (I := I) (M := M)
      n g hdim level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k)) hB
  have hstep : ∀ k < m, X (k + 1) ≤ factor k * X k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserNorm_succ_le_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k))
        (hlevel (Nat.lt_succ_self (2 * k)))
        (hlevel (Nat.lt_succ_self (2 * k + 1)))
        (hlevel (Nat.lt_succ_self (2 * k + 2)))
        hB hrho
        (fun t ht x => hpde t
          ⟨ht.1, ht.2.trans (htime.antitone (Nat.zero_le k))⟩ x)
  simpa only [X, factor, n] using
    (finite_multiplicative_iteration m hfactor hstep)

theorem nestedForwardMoserNorm_le_rpowNorm_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ p a B : ℝ} (level upperTime : ℕ → ℝ) (m : ℕ)
    (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : a ≤ upperTime m) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) a (upperTime 0)).real
          Set.univ ≤ 1) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime m ≤
      (∏ k ∈ Finset.range m,
        nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let factor : ℕ → ℝ := fun k =>
    nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k
  let P := ∏ k ∈ Finset.range m, factor k
  have hiteration := nestedForwardMoserNorm_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos level upperTime m hp₀
      hlevel htime haTime hB hrho hpde hexponents
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserStepFactor_nonneg (I := I) (M := M)
      n g hdim level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k)) hB
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro k hk
    exact hfactor k (Finset.mem_range.mp hk)
  have hmono := localizedSpacetimeRpowNorm_mono
    (I := I) (M := M)
      (spatialCutoffBetween rho (level 0) (level 1)) u
      hu.continuous hpos hp₀ hp₀p hmass
      (a := a) (b := upperTime 0)
  have hzero :
      nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime 0 ≤
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) := by
    simpa only [nestedForwardMoserNorm, nestedForwardMoserMoment,
      parabolicMoserExponent_zero, zero_mul, zero_add] using hmono
  calc
    nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime m ≤
        P * nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime 0 := by
      simpa only [P, factor, n] using hiteration
    _ ≤ P * localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) :=
      mul_le_mul_of_nonneg_left hzero hP
    _ = _ := by rfl

theorem exists_nested_forward_moser_iteration_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a B : ℝ} (level upperTime : ℕ → ℝ)
    (hp : 0 < p) (hpq : p < q) (hq_one : q < 1)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : ∀ k, a ≤ upperTime k) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) a (upperTime 0)).real
          Set.univ ≤ 1) :
    let n := Module.finrank ℝ E
    ∃ m : ℕ,
      let p₀ := q * parabolicMoserDecay n ^ m
      p₀ < p ∧ p ≤ parabolicMoserGain n * p₀ ∧
        parabolicMoserExponent n p₀ m = q ∧
        nestedForwardMoserNorm (I := I) (M := M) n
            rho u p₀ a level upperTime m ≤
          (∏ k ∈ Finset.range m,
            nestedForwardMoserStepFactor (I := I) (M := M)
              n g hdim B p₀ a level upperTime k) *
            localizedSpacetimeRpowNorm (I := I) (M := M)
              (spatialCutoffBetween rho (level 0) (level 1)) u
                p a (upperTime 0) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  obtain ⟨m, hp₀p, hpp₀⟩ :=
    exists_parabolic_moser_iteration_depth n hp hpq
  let p₀ := q * parabolicMoserDecay n ^ m
  have hq_pos : 0 < q := hp.trans hpq
  have hp₀ : 0 < p₀ :=
    mul_pos hq_pos (pow_pos (parabolicMoserDecay_pos n) m)
  have htarget : parabolicMoserExponent n p₀ m = q := by
    simpa only [p₀] using parabolicMoserExponent_decay_mul_self n q m
  have hexponents : ∀ k < m, parabolicMoserExponent n p₀ k < 1 := by
    intro k hk
    calc
      parabolicMoserExponent n p₀ k < parabolicMoserExponent n p₀ m :=
        parabolicMoserExponent_strictMono n hp₀ hk
      _ = q := htarget
      _ < 1 := hq_one
  have hbound := nestedForwardMoserNorm_le_rpowNorm_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos level upperTime m hp₀
      hp₀p.le hlevel htime (haTime m) hB hrho hpde hexponents hmass
  refine ⟨m, ?_⟩
  simpa only [p₀, n] using ⟨hp₀p, hpp₀, htarget, hbound⟩

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
