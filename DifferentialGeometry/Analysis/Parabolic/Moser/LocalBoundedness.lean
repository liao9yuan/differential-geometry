import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff
import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.Power

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def moserLocalizedMass
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  ∫ t in moserTimeLevel a τ k..t₁,
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 *
      u t x ^ parabolicMoserExponent n p₀ k
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def moserTimeDerivativeCost (a τ : ℝ) (k : ℕ) : ℝ :=
  (2 * timeCutoffDerivConstant / (τ - a)) * 2 ^ k

def moserSpatialGradientCost
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) : ℝ :=
  spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)

def moserStepCoefficient
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  (t₁ - moserTimeLevel a τ (k + 1) + 1) *
      (moserTimeDerivativeCost a τ k + 4 * moserSpatialGradientCost rho k) +
    moserSpatialGradientCost rho k

def moserStepConstant
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (a τ t₁ : ℝ) : ℝ :=
  (t₁ - a + 1) *
      (2 * timeCutoffDerivConstant / (τ - a) +
        4 * spatialMoserCutoffGradientConstant (I := I) g rho) +
    spatialMoserCutoffGradientConstant (I := I) g rho

theorem parabolicMoserExponent_half_mul_critical
    (n : ℕ) [NeZero n] (p₀ : ℝ) (k : ℕ) :
    (parabolicMoserExponent n p₀ k / 2) * (2 + 4 / (n : ℝ)) =
      parabolicMoserExponent n p₀ (k + 1) := by
  rw [parabolicMoserExponent_succ, parabolicMoserGain]
  ring

theorem abs_mul_rpow_half_critical
    (n : ℕ) [NeZero n] {a b p₀ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (k : ℕ) :
    |a * b ^ (parabolicMoserExponent n p₀ k / 2)| ^ (2 + 4 / (n : ℝ)) =
      a ^ (2 + 4 / (n : ℝ)) * b ^ parabolicMoserExponent n p₀ (k + 1) := by
  have hbrpow : 0 ≤ b ^ (parabolicMoserExponent n p₀ k / 2) :=
    Real.rpow_nonneg hb.le _
  rw [abs_of_nonneg (mul_nonneg ha hbrpow), Real.mul_rpow ha hbrpow,
    ← Real.rpow_mul hb.le, parabolicMoserExponent_half_mul_critical]

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedL2Mass_rpow_half
    (g : SmoothRiemannianMetric I M) (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x) (p t : ℝ) :
    localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ (p / 2))
          (contMDiff_rpow_of_pos hu hpos (p / 2)) t) =
      ∫ x, cutoff.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  apply integral_congr_ae
  filter_upwards with x
  change cutoff.toFun x ^ 2 * (u t x ^ (p / 2)) ^ 2 =
    cutoff.toFun x ^ 2 * u t x ^ p
  congr 1
  rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
    ← Real.rpow_mul (hpos t x).le]
  congr 1
  ring

omit [I.Boundaryless] [CompactSpace M] in
theorem moserLocalizedMass_nonneg
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) {p₀ a τ t₁ : ℝ}
    (haτ : a < τ) (hτt₁ : τ ≤ t₁) (hu : ∀ t x, 0 ≤ u t x) (k : ℕ) :
    0 ≤ moserLocalizedMass (I := I) (M := M) n rho u p₀ a τ t₁ k := by
  apply intervalIntegral.integral_nonneg
  · exact (moserTimeLevel_lt haτ k).le.trans hτt₁
  · intro t _
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hu t x) _)

omit [I.Boundaryless] in
theorem moserLocalizedMass_succ_le
    (n : ℕ) [NeZero n]
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁) (k : ℕ) :
    moserLocalizedMass (I := I) (M := M) n rho u p₀ a τ t₁ (k + 1) ≤
      ∫ t in moserTimeLevel a τ (k + 1)..t₁,
        ∫ x,
          |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
              u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^
            (2 + 4 / (n : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let lower := moserTimeLevel a τ (k + 1)
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
  have hlower : lower ≤ t₁ := by
    dsimp only [lower]
    exact (moserTimeLevel_lt haτ (k + 1)).le.trans hτt₁
  have hleft_cont : ContinuousOn left (Icc lower t₁) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc lower t₁) μ
      (fun t x => (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hleft_joint.continuousOn
    simpa only [left] using h
  have hright_cont : ContinuousOn right (Icc lower t₁) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc lower t₁) μ
      (fun t x => |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
        u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical)
      isCompact_Icc hright_joint.continuousOn
    simpa only [right] using h
  have hleft_int : IntervalIntegrable left volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hleft_cont
  have hright_int : IntervalIntegrable right volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hright_cont
  have hpoint : ∀ t ∈ Icc lower t₁, left t ≤ right t := by
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
  have htime := intervalIntegral.integral_mono_on hlower hleft_int hright_int hpoint
  simpa only [moserLocalizedMass, left, right, lower, p, critical] using htime

theorem moserLocalizedMass_succ_le_of_subsolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ : ℝ} (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    (k : ℕ) :
    moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ t₁ (k + 1) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (moserStepCoefficient (I := I) rho a τ t₁ k *
          moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
            rho u p₀ a τ t₁ k) ^
          parabolicMoserGain (Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p := parabolicMoserExponent n p₀ k
  let q := p / 2
  let L := moserLocalizedMass (I := I) (M := M) n rho u p₀ a τ t₁ k
  let D := moserTimeDerivativeCost a τ k
  let K := moserSpatialGradientCost (I := I) rho k
  have hp₀_nonneg : 0 ≤ p₀ := (by norm_num : (0 : ℝ) ≤ 2).trans hp₀
  have hp : 2 ≤ p := by
    dsimp only [p, parabolicMoserExponent]
    calc
      2 ≤ p₀ := hp₀
      _ = p₀ * 1 := (mul_one p₀).symm
      _ ≤ p₀ * parabolicMoserGain n ^ k :=
        mul_le_mul_of_nonneg_left
          (one_le_pow₀ (one_lt_parabolicMoserGain n).le) hp₀_nonneg
  have hq : 1 ≤ q := by
    dsimp only [q]
    linarith
  have hL : 0 ≤ L := by
    exact moserLocalizedMass_nonneg n rho u haτ hτt₁
      (fun t x => (hpos t x).le) k
  have hD : 0 ≤ D := by
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
        (sub_pos.mpr haτ).le)
      (pow_nonneg (by norm_num) k)
  have hK : 0 ≤ K := by
    exact mul_nonneg
      (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
      (pow_nonneg (by norm_num) _)
  have hbridge := moserLocalizedMass_succ_le n rho u hu hpos
    (p₀ := p₀) (a := a) (τ := τ) (t₁ := t₁) haτ hτt₁ k
  have hstep := rpow_moser_step_homogeneous_le
    (I := I) (M := M) g hdim
    (spatialMoserCutoff rho (2 * k + 1)) (spatialMoserCutoff rho (2 * k))
    u hu hpos (q := q) hq
    (a := moserTimeLevel a τ k) (t₀ := moserTimeLevel a τ (k + 1))
    (t₁ := t₁) (D := D) (K := K) (L := L)
    (moserTimeLevel_lt_succ haτ k)
    ((moserTimeLevel_lt haτ (k + 1)).le.trans hτt₁) hD hK hL
    (fun t ht x => hpde t
      ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
    (fun x => by
      simpa only [Nat.add_assoc] using
        spatialMoserCutoff_succ_sq_le rho (2 * k) x)
    (fun x => by
      simpa only [K, moserSpatialGradientCost] using
        spatialMoserCutoff_gradient_le (I := I) g rho (2 * k) x)
    (fun t _ => by
      simpa only [D, moserTimeDerivativeCost] using
        timeCutoffDeriv_moserTimeLevel_le_mul_pow haτ k t)
    (by
      have heq :
          (∫ t in moserTimeLevel a τ k..t₁,
            localizedL2Mass (I := I) (M := M) (spatialMoserCutoff rho (2 * k))
              (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
                (contMDiff_rpow_of_pos hu hpos q) t)) = L := by
        dsimp only [L]
        rw [moserLocalizedMass]
        apply intervalIntegral.integral_congr
        intro t _
        simpa only [q, p] using localizedL2Mass_rpow_half
          (I := I) (M := M) g (spatialMoserCutoff rho (2 * k)) u hu hpos p t
      exact heq.le)
  calc
    moserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ t₁ (k + 1) ≤
        ∫ t in moserTimeLevel a τ (k + 1)..t₁,
          ∫ x,
            |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
                u t x ^ q| ^ (2 + 4 / (n : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [n, q, p] using hbridge
    _ ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - moserTimeLevel a τ (k + 1) + 1) * ((D + 4 * K) * L) +
          K * L) ^ (1 + 2 / (n : ℝ))) := by
      simpa only [q, n, parabolicMoserGain] using hstep
    _ = localizedSobolevConstant (I := I) (M := M) g hdim *
        (moserStepCoefficient (I := I) rho a τ t₁ k * L) ^
          parabolicMoserGain n := by
      congr 2
      · rw [moserStepCoefficient]
        change
          (t₁ - moserTimeLevel a τ (k + 1) + 1) * ((D + 4 * K) * L) +
              K * L =
            ((t₁ - moserTimeLevel a τ (k + 1) + 1) * (D + 4 * K) + K) * L
        ring

theorem moserTimeDerivativeCost_nonneg
    {a τ : ℝ} (haτ : a < τ) (k : ℕ) :
    0 ≤ moserTimeDerivativeCost a τ k := by
  exact mul_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
      (sub_pos.mpr haτ).le)
    (pow_nonneg (by norm_num) k)

omit [SigmaCompactSpace M] in
theorem moserSpatialGradientCost_nonneg
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) :
    0 ≤ moserSpatialGradientCost (I := I) rho k := by
  exact mul_nonneg (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
    (pow_nonneg (by norm_num) _)

omit [SigmaCompactSpace M] in
theorem moserStepCoefficient_nonneg
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁) (k : ℕ) :
    0 ≤ moserStepCoefficient (I := I) rho a τ t₁ k := by
  have hduration : 0 ≤ t₁ - moserTimeLevel a τ (k + 1) + 1 := by
    linarith [moserTimeLevel_lt haτ (k + 1)]
  exact add_nonneg
    (mul_nonneg hduration
      (add_nonneg (moserTimeDerivativeCost_nonneg haτ k)
        (mul_nonneg (by norm_num) (moserSpatialGradientCost_nonneg rho k))))
    (moserSpatialGradientCost_nonneg rho k)

omit [SigmaCompactSpace M] in
theorem moserStepConstant_nonneg
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁) :
    0 ≤ moserStepConstant (I := I) rho a τ t₁ := by
  have hduration : 0 ≤ t₁ - a + 1 := by linarith
  exact add_nonneg
    (mul_nonneg hduration
      (add_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
          (sub_pos.mpr haτ).le)
        (mul_nonneg (by norm_num)
          (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho))))
    (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)

omit [SigmaCompactSpace M] in
theorem moserStepCoefficient_le
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {a τ t₁ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁) (k : ℕ) :
    moserStepCoefficient (I := I) rho a τ t₁ k ≤
      moserStepConstant (I := I) rho a τ t₁ * 16 ^ k := by
  let D := 2 * timeCutoffDerivConstant / (τ - a)
  let K := spatialMoserCutoffGradientConstant (I := I) g rho
  have hD : 0 ≤ D := by
    exact div_nonneg
      (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
      (sub_pos.mpr haτ).le
  have hK : 0 ≤ K := spatialMoserCutoffGradientConstant_nonneg (I := I) g rho
  have hpow : (2 : ℝ) ^ k ≤ 16 ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hgradient : moserSpatialGradientCost (I := I) rho k = K * 16 ^ k := by
    rw [moserSpatialGradientCost]
    change K * 4 ^ (2 * k) = K * 16 ^ k
    rw [pow_mul]
    norm_num
  have htime : moserTimeDerivativeCost a τ k = D * 2 ^ k := rfl
  have hduration_nonneg : 0 ≤ t₁ - moserTimeLevel a τ (k + 1) + 1 := by
    linarith [moserTimeLevel_lt haτ (k + 1)]
  have hduration_le :
      t₁ - moserTimeLevel a τ (k + 1) + 1 ≤ t₁ - a + 1 := by
    linarith [moserTimeLevel_le haτ (k + 1)]
  have hduration_max_nonneg : 0 ≤ t₁ - a + 1 := by linarith
  have hcost_le :
      D * 2 ^ k + 4 * (K * 16 ^ k) ≤ (D + 4 * K) * 16 ^ k := by
    calc
      D * 2 ^ k + 4 * (K * 16 ^ k) ≤
          D * 16 ^ k + 4 * (K * 16 ^ k) := by
        gcongr
      _ = (D + 4 * K) * 16 ^ k := by ring
  rw [moserStepCoefficient, moserStepConstant, htime, hgradient]
  change
    (t₁ - moserTimeLevel a τ (k + 1) + 1) *
          (D * 2 ^ k + 4 * (K * 16 ^ k)) + K * 16 ^ k ≤
      ((t₁ - a + 1) * (D + 4 * K) + K) * 16 ^ k
  calc
    _ ≤ (t₁ - a + 1) * ((D + 4 * K) * 16 ^ k) + K * 16 ^ k := by
      gcongr
    _ = ((t₁ - a + 1) * (D + 4 * K) + K) * 16 ^ k := by ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
