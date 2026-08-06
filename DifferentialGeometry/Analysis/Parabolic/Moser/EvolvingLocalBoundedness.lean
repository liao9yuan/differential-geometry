import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingPower
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness


noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

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

def evolvingMoserLocalizedMass
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) (p₀ a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  ∫ t in moserTimeLevel a τ k..t₁,
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 *
      u t x ^ parabolicMoserExponent n p₀ k
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)

def evolvingMoserNormalizedMass
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) (p₀ a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  evolvingMoserLocalizedMass (I := I) (M := M) n g rho u p₀ a τ t₁ k ^
    (1 / parabolicMoserExponent n p₀ k)

def evolvingMoserSpatialGradientCost (G : ℝ) (k : ℕ) : ℝ :=
  G * 4 ^ (2 * k)

def evolvingMoserStepCoefficient
    (G B a τ t₁ : ℝ) (k : ℕ) : ℝ :=
  (t₁ - moserTimeLevel a τ (k + 1) + 1) *
      (moserTimeDerivativeCost a τ k +
        4 * evolvingMoserSpatialGradientCost G k + (1 / 2) * B) +
    evolvingMoserSpatialGradientCost G k

omit [I.Boundaryless] [CompactSpace M] in
theorem evolvingMoserLocalizedMass_nonneg
    (n : ℕ) (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ) {p₀ a τ t₁ : ℝ}
    (haτ : a < τ) (hτt₁ : τ ≤ t₁) (hu : ∀ t x, 0 ≤ u t x) (k : ℕ) :
    0 ≤ evolvingMoserLocalizedMass
      (I := I) (M := M) n g rho u p₀ a τ t₁ k := by
  apply intervalIntegral.integral_nonneg
  · exact (moserTimeLevel_lt haτ k).le.trans hτt₁
  · intro t _
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hu t x) _)

omit [I.Boundaryless] in
theorem evolvingMoserLocalizedMass_succ_le
    (n : ℕ) [NeZero n]
    (g : ℝ → SmoothRiemannianMetric I M)
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ s₀ : ℝ} (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hg : MetricFamilyRegularAt (I := I) g s₀) (k : ℕ) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) n g rho u p₀ a τ t₁ (k + 1) ≤
      ∫ t in moserTimeLevel a τ (k + 1)..t₁,
        ∫ x,
          |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
              u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^
            (2 + 4 / (n : ℝ))
          ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let lower := moserTimeLevel a τ (k + 1)
  let p := parabolicMoserExponent n p₀ (k + 1)
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  let right : ℝ → ℝ := fun t =>
    ∫ x, |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
      u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical
      ∂(riemannianMeasureFamily (I := I) (M := M) g t)
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
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hleft_joint.continuousOn
  have hright_cont : ContinuousOn right (Icc lower t₁) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc lower t₁)) Set.Subset.rfl)
    · exact hright_joint.continuousOn
  have hleft_int : IntervalIntegrable left volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hleft_cont
  have hright_int : IntervalIntegrable right volume lower t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hlower] using hright_cont
  have hpoint : ∀ t ∈ Icc lower t₁, left t ≤ right t := by
    intro t _
    letI : IsFiniteMeasure
        (riemannianMeasureFamily (I := I) (M := M) g t) := by
      dsimp only [riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
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
  simpa only [evolvingMoserLocalizedMass, left, right, lower, p, critical] using htime

theorem evolvingMoserLocalizedMass_succ_le_of_subsolution
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {q : SmoothRiemannianMetric I M} (rho : SmoothScalar q)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ t₁ B C G s₀ : ℝ}
    (hp₀ : 2 ≤ p₀) (haτ : a < τ) (hτt₁ : τ ≤ t₁)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hg : MetricFamilyRegularAt (I := I) g s₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a t₁,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).smooth x)
    (htrace : ∀ t ∈ Icc a t₁, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (k : ℕ)
    (hgradient : ∀ t ∈ Icc a t₁, ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff rho (2 * k + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost G k *
          (spatialMoserCutoff rho (2 * k)).toFun x ^ 2) :
    evolvingMoserLocalizedMass
        (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ (k + 1) ≤
      C * (evolvingMoserStepCoefficient G B a τ t₁ k *
        evolvingMoserLocalizedMass
          (I := I) (M := M) (Module.finrank ℝ E) g rho u p₀ a τ t₁ k) ^
        parabolicMoserGain (Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p := parabolicMoserExponent n p₀ k
  let exponent := p / 2
  let L := evolvingMoserLocalizedMass
    (I := I) (M := M) n g rho u p₀ a τ t₁ k
  let D := moserTimeDerivativeCost a τ k
  let K := evolvingMoserSpatialGradientCost G k
  have hp₀_nonneg : 0 ≤ p₀ := (by norm_num : (0 : ℝ) ≤ 2).trans hp₀
  have hp : 2 ≤ p := by
    dsimp only [p, parabolicMoserExponent]
    calc
      2 ≤ p₀ := hp₀
      _ = p₀ * 1 := (mul_one p₀).symm
      _ ≤ p₀ * parabolicMoserGain n ^ k :=
        mul_le_mul_of_nonneg_left
          (one_le_pow₀ (one_lt_parabolicMoserGain n).le) hp₀_nonneg
  have hexponent : 1 ≤ exponent := by
    dsimp only [exponent]
    linarith
  have hL : 0 ≤ L := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g rho u haτ hτt₁
      (fun t x => (hpos t x).le) k
  have hD : 0 ≤ D := moserTimeDerivativeCost_nonneg haτ k
  have hK : 0 ≤ K := by
    exact mul_nonneg hG (pow_nonneg (by norm_num) _)
  have hbridge := evolvingMoserLocalizedMass_succ_le
    (I := I) (M := M) n g rho u hu hpos
      (p₀ := p₀) haτ hτt₁ hg k
  have hstep := evolving_rpow_moser_step_homogeneous_le
    (I := I) (M := M) g hdim
      (spatialMoserCutoff rho (2 * k + 1)).toFun
      (spatialMoserCutoff rho (2 * k)).toFun
      (spatialMoserCutoff rho (2 * k + 1)).smooth
      (spatialMoserCutoff rho (2 * k)).smooth u hu hpos hexponent hg hgram hC
      (fun t ht => hSobolev t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩)
      (moserTimeLevel_lt_succ haτ k)
      ((moserTimeLevel_lt haτ (k + 1)).le.trans hτt₁)
      hB hD hK hL
      (fun t ht x => hpde t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (fun x => by
        simpa only [Nat.add_assoc] using
          spatialMoserCutoff_succ_sq_le rho (2 * k) x)
      (fun t ht x => hgradient t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (fun t _ => by
        simpa only [D, moserTimeDerivativeCost] using
          timeCutoffDeriv_moserTimeLevel_le_mul_pow haτ k t)
      (fun t ht x => htrace t
        ⟨(moserTimeLevel_le haτ k).trans ht.1, ht.2⟩ x)
      (by
        have heq :
            (∫ t in moserTimeLevel a τ k..t₁,
              evolvingLocalizedL2Mass (I := I) (M := M) g
                (spatialMoserCutoff rho (2 * k)).toFun
                (fun s x => u s x ^ exponent) t) = L := by
          dsimp only [L]
          rw [evolvingMoserLocalizedMass]
          apply intervalIntegral.integral_congr
          intro t _
          simp only [evolvingLocalizedL2Mass]
          apply integral_congr_ae
          filter_upwards with x
          change _ * (u t x ^ exponent) ^ 2 = _ * u t x ^ p
          dsimp only [exponent]
          congr 1
          rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
            ← Real.rpow_mul (hpos t x).le]
          congr 1
          ring
        exact heq.le)
  calc
    evolvingMoserLocalizedMass
          (I := I) (M := M) n g rho u p₀ a τ t₁ (k + 1) ≤
        ∫ t in moserTimeLevel a τ (k + 1)..t₁,
          ∫ x,
            |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
                u t x ^ exponent| ^ (2 + 4 / (n : ℝ))
            ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
      simpa only [n, exponent, p] using hbridge
    _ ≤ C * (((t₁ - moserTimeLevel a τ (k + 1) + 1) *
          ((D + 4 * K + (1 / 2) * B) * L) + K * L) ^
          (1 + 2 / (n : ℝ))) := by
      simpa only [exponent, n] using hstep
    _ = C * (evolvingMoserStepCoefficient G B a τ t₁ k * L) ^
          parabolicMoserGain n := by
      congr 2
      · rw [evolvingMoserStepCoefficient]
        change
          (t₁ - moserTimeLevel a τ (k + 1) + 1) *
                ((D + 4 * K + (1 / 2) * B) * L) + K * L =
            ((t₁ - moserTimeLevel a τ (k + 1) + 1) *
                (D + 4 * K + (1 / 2) * B) + K) * L
        ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
