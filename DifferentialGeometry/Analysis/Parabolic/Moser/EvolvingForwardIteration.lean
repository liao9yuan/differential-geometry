import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingReverseHolder
import DifferentialGeometry.Analysis.Parabolic.Moser.ForwardIteration
import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv

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

omit [I.Boundaryless] in
private theorem intervalIntegral_fixed_le_moving_of_volume_le
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : Continuous (fun z : ℝ × M => f z.1 z.2))
    (hf_nonneg : ∀ t x, 0 ≤ f t x)
    {a b t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianMeasureFamily (I := I) (M := M) g t) :
    (∫ t in a..b, ∫ x, f t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) ≤
      C.toReal * ∫ t in a..b, ∫ x, f t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
  let fixed : ℝ → ℝ := fun t =>
    ∫ x, f t x ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let moving : ℝ → ℝ := fun t =>
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  letI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  have hfixed_cont : ContinuousOn fixed (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b)
      (riemannianVolumeMeasure (I := I) (M := M) q) f
      isCompact_Icc hf.continuousOn
    simpa only [fixed] using h
  have hmoving_cont : ContinuousOn moving (Icc a b) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc a b)) Set.Subset.rfl)
    · exact hf.continuousOn
  have hfixed_int : IntervalIntegrable fixed volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hfixed_cont
  have hmoving_int : IntervalIntegrable moving volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hmoving_cont
  have hpoint : ∀ t ∈ Icc a b, fixed t ≤ C.toReal * moving t := by
    intro t ht
    let μ := riemannianMeasureFamily (I := I) (M := M) g t
    letI : IsFiniteMeasure μ := by
      dsimp only [μ, riemannianMeasureFamily]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) (g t)
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    have hf_slice : Continuous (f t) :=
      hf.comp (continuous_const.prodMk continuous_id)
    have hf_int : Integrable (f t) (C • μ) :=
      hf_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure (hvolume t ht)
      (ae_of_all _ (hf_nonneg t)) hf_int
    rw [integral_smul_measure] at hmono
    simpa only [fixed, moving, μ, smul_eq_mul] using hmono
  have hmono : (∫ t in a..b, fixed t) ≤
      ∫ t in a..b, C.toReal * moving t :=
    intervalIntegral.integral_mono_on hab hfixed_int
      (hmoving_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [fixed, moving] using hmono

omit [I.Boundaryless] in
private theorem intervalIntegral_moving_le_fixed_of_volume_le
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : Continuous (fun z : ℝ × M => f z.1 z.2))
    (hf_nonneg : ∀ t x, 0 ≤ f t x)
    {a b t₀ : ℝ} (hab : a ≤ b)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        C • riemannianVolumeMeasure (I := I) (M := M) q) :
    (∫ t in a..b, ∫ x, f t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g t)) ≤
      C.toReal * ∫ t in a..b, ∫ x, f t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  let moving : ℝ → ℝ := fun t =>
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g t)
  let fixed : ℝ → ℝ := fun t =>
    ∫ x, f t x ∂(riemannianVolumeMeasure (I := I) (M := M) q)
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) q
  have hmoving_cont : ContinuousOn moving (Icc a b) := by
    apply integral_family_cont (I := I) (M := M) isCompact_Icc
    · intro x₀ i j
      exact (hg.continuousOn_chartGramMatrix x₀ i j).mono
        (Set.prod_mono (Set.subset_univ (Icc a b)) Set.Subset.rfl)
    · exact hf.continuousOn
  have hfixed_cont : ContinuousOn fixed (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ f isCompact_Icc hf.continuousOn
    simpa only [fixed, μ] using h
  have hmoving_int : IntervalIntegrable moving volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hmoving_cont
  have hfixed_int : IntervalIntegrable fixed volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hfixed_cont
  have hpoint : ∀ t ∈ Icc a b, moving t ≤ C.toReal * fixed t := by
    intro t ht
    letI : IsFiniteMeasure (C • μ) := μ.smul_finite hC
    have hf_slice : Continuous (f t) :=
      hf.comp (continuous_const.prodMk continuous_id)
    have hf_int : Integrable (f t) (C • μ) :=
      hf_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmono := integral_mono_measure (hvolume t ht)
      (ae_of_all _ (hf_nonneg t)) hf_int
    rw [integral_smul_measure] at hmono
    simpa only [moving, fixed, μ, smul_eq_mul] using hmono
  have hmono : (∫ t in a..b, moving t) ≤
      ∫ t in a..b, C.toReal * fixed t :=
    intervalIntegral.integral_mono_on hab hmoving_int
      (hfixed_int.const_mul C.toReal) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [moving, fixed] using hmono

def evolvingForwardMoserStepCoefficient
    (q a t₁ t₂ K B : ℝ) : ℝ :=
  (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant / (t₂ - t₁) +
        (2 * q / (1 - q)) * K + (1 / 2) * B) + K

theorem evolvingForwardMoserStepCoefficient_nonneg
    {q a t₁ t₂ K B : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (hat₁ : a ≤ t₁) (ht₁t₂ : t₁ < t₂)
    (hK : 0 ≤ K) (hB : 0 ≤ B) :
    0 ≤ evolvingForwardMoserStepCoefficient q a t₁ t₂ K B := by
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
      (add_nonneg (add_nonneg htime (mul_nonneg hpower hK))
        (mul_nonneg (by norm_num) hB))) hK

def evolvingForwardMoserStepCoefficientEnvelope
    (q a b T K B : ℝ) : ℝ :=
  (b - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant * T +
        (2 * q / (1 - q)) * K + (1 / 2) * B) + K

def canonicalEvolvingForwardMoserStepEnvelope
    (V : ℝ≥0∞) (q a τ b G B lower upper : ℝ) : ℝ :=
  max 1 (V.toReal * evolvingForwardMoserStepCoefficientEnvelope q a b
    (2 / (b - τ)) (canonicalForwardMoserGradientCost G lower upper) B)

def canonicalEvolvingForwardMoserIterationCost
    (n : ℕ) (V : ℝ≥0∞) (C p₀ q a τ b G B lower upper : ℝ)
    (k : ℕ) : ℝ :=
  moserIterationCost (parabolicMoserDecay n)
    ((parabolicMoserDecay n * Real.log (max 1 (V.toReal * C)) +
      Real.log (canonicalEvolvingForwardMoserStepEnvelope
        V q a τ b G B lower upper)) / p₀)
    (Real.log 16 / p₀) k

def canonicalEvolvingForwardMoserLogCost
    (n : ℕ) (V : ℝ≥0∞) (C q a τ b G B lower upper : ℝ) : ℝ :=
  let theta := parabolicMoserDecay n
  let C₀ := max 1 (V.toReal * C)
  let A := canonicalEvolvingForwardMoserStepEnvelope V q a τ b G B lower upper
  (theta * Real.log C₀ + Real.log A) / (1 - theta) +
    Real.log 16 * (theta / (1 - theta) ^ 2)

def canonicalEvolvingForwardMoserReverseCost
    (n : ℕ) (V : ℝ≥0∞) (C q a τ b G B lower upper : ℝ) : ℝ :=
  Real.exp (canonicalEvolvingForwardMoserLogCost
    n V C q a τ b G B lower upper / (1 - parabolicMoserDecay n))

theorem evolvingForwardMoserStepCoefficient_canonical_le_mul_pow
    {q qbar a τ b G B lower upper : ℝ} (k : ℕ)
    (hq : 0 ≤ q) (hqqbar : q ≤ qbar) (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    evolvingForwardMoserStepCoefficient q a
        (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
        (nestedForwardMoserGradientCost G
          (moserCutoffLevelBetween lower upper) k) B ≤
      evolvingForwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ))
          (canonicalForwardMoserGradientCost G lower upper) B * 16 ^ k := by
  let t₁ := moserUpperTimeLevel τ b (k + 1)
  let t₂ := moserUpperTimeLevel τ b k
  let K := nestedForwardMoserGradientCost G
    (moserCutoffLevelBetween lower upper) k
  let Kbar := canonicalForwardMoserGradientCost G lower upper
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (sq_nonneg _)
  have hbase := forwardMoserStepCoefficient_le_envelope_mul_pow k
    hq hqqbar hqbar_one
    (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
    (moserUpperTimeLevel_le hτb (k + 1))
    (moserUpperTimeLevel_succ_lt hτb k) hK
    (moserUpperTimeLevel_sub_succ_inv_le_mul_pow hτb k)
    (le_of_eq (nestedForwardMoserGradientCost_canonical hlowerUpper k))
  have hqbar : 0 ≤ qbar := hq.trans hqqbar
  have hq_one : q < 1 := hqqbar.trans_lt hqbar_one
  have hsmallRatio : q / (2 * (1 - q)) ≤
      qbar / (2 * (1 - qbar)) := by
    rw [div_le_div_iff₀
      (mul_pos (by norm_num) (sub_pos.mpr hq_one))
      (mul_pos (by norm_num) (sub_pos.mpr hqbar_one))]
    nlinarith
  have hmax : max 1 (q / (2 * (1 - q))) ≤
      max 1 (qbar / (2 * (1 - qbar))) := max_le_max_left 1 hsmallRatio
  have ht₁ : a ≤ t₁ :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have ht₁b : t₁ ≤ b := moserUpperTimeLevel_le hτb (k + 1)
  have houter :
      (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) ≤
        (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) := by
    exact mul_le_mul (by linarith) hmax
      (zero_le_one.trans (le_max_left _ _)) (by linarith)
  have htrace_nonneg : 0 ≤ (1 / 2) * B := mul_nonneg (by norm_num) hB
  have htrace :
      (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) * ((1 / 2) * B) ≤
        ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) *
          ((1 / 2) * B)) * 16 ^ k := by
    calc
      _ ≤ (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) *
          ((1 / 2) * B) := mul_le_mul_of_nonneg_right houter htrace_nonneg
      _ ≤ _ := by
        exact le_mul_of_one_le_right
          (mul_nonneg
            (mul_nonneg (by linarith)
              (zero_le_one.trans (le_max_left _ _))) htrace_nonneg)
          (one_le_pow₀ (by norm_num))
  change evolvingForwardMoserStepCoefficient q a t₁ t₂ K B ≤
    evolvingForwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ)) Kbar B *
      16 ^ k
  calc
    evolvingForwardMoserStepCoefficient q a t₁ t₂ K B =
        forwardMoserStepCoefficient q a t₁ t₂ K +
          (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) * ((1 / 2) * B) := by
      unfold evolvingForwardMoserStepCoefficient forwardMoserStepCoefficient
      ring
    _ ≤ forwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ)) Kbar *
          16 ^ k +
        ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) *
          ((1 / 2) * B)) * 16 ^ k := by
      exact add_le_add (by simpa only [t₁, t₂, K, Kbar] using hbase) htrace
    _ = evolvingForwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ))
          Kbar B * 16 ^ k := by
      unfold evolvingForwardMoserStepCoefficientEnvelope
        forwardMoserStepCoefficientEnvelope
      ring

theorem canonicalEvolvingForwardMoserLogCost_nonneg
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    (C q a τ b G B lower upper : ℝ) :
    0 ≤ canonicalEvolvingForwardMoserLogCost
      n V C q a τ b G B lower upper := by
  have htheta : 0 ≤ parabolicMoserDecay n := (parabolicMoserDecay_pos n).le
  have hdenom : 0 ≤ 1 - parabolicMoserDecay n :=
    sub_nonneg.mpr (parabolicMoserDecay_lt_one n).le
  have hC₀ : 1 ≤ max 1 (V.toReal * C) := le_max_left _ _
  have hA : 1 ≤ canonicalEvolvingForwardMoserStepEnvelope
      V q a τ b G B lower upper := le_max_left _ _
  unfold canonicalEvolvingForwardMoserLogCost
  dsimp only
  exact add_nonneg
    (div_nonneg
      (add_nonneg (mul_nonneg htheta (Real.log_nonneg hC₀))
        (Real.log_nonneg hA)) hdenom)
    (mul_nonneg (Real.log_nonneg (by norm_num))
      (div_nonneg htheta (sq_nonneg _)))

theorem canonicalEvolvingForwardMoserIterationCost_nonneg
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (C q a τ b G B lower upper : ℝ) (k : ℕ) :
    0 ≤ canonicalEvolvingForwardMoserIterationCost
      n V C p₀ q a τ b G B lower upper k := by
  have hC₀ : 1 ≤ max 1 (V.toReal * C) := le_max_left _ _
  have hA : 1 ≤ canonicalEvolvingForwardMoserStepEnvelope
      V q a τ b G B lower upper := le_max_left _ _
  unfold canonicalEvolvingForwardMoserIterationCost
  exact moserIterationCost_nonneg (parabolicMoserDecay_pos n).le
    (div_nonneg
      (add_nonneg
        (mul_nonneg (parabolicMoserDecay_pos n).le (Real.log_nonneg hC₀))
        (Real.log_nonneg hA)) hp₀.le)
    (div_nonneg (Real.log_nonneg (by norm_num)) hp₀.le) k

theorem one_le_canonicalEvolvingForwardMoserReverseCost
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    (C q a τ b G B lower upper : ℝ) :
    1 ≤ canonicalEvolvingForwardMoserReverseCost
      n V C q a τ b G B lower upper := by
  unfold canonicalEvolvingForwardMoserReverseCost
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (canonicalEvolvingForwardMoserLogCost
        n V C q a τ b G B lower upper / (1 - parabolicMoserDecay n)) :=
      Real.exp_le_exp.mpr (div_nonneg
        (canonicalEvolvingForwardMoserLogCost_nonneg
          n V C q a τ b G B lower upper)
        (sub_nonneg.mpr (parabolicMoserDecay_lt_one n).le))

theorem tsum_canonicalEvolvingForwardMoserIterationCost
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (C q a τ b G B lower upper : ℝ) :
    ∑' k, canonicalEvolvingForwardMoserIterationCost
        n V C p₀ q a τ b G B lower upper k =
      canonicalEvolvingForwardMoserLogCost
        n V C q a τ b G B lower upper / p₀ := by
  unfold canonicalEvolvingForwardMoserIterationCost
    canonicalEvolvingForwardMoserLogCost
  dsimp only
  rw [tsum_moserIterationCost (parabolicMoserDecay_pos n).le
    (parabolicMoserDecay_lt_one n)]
  field_simp [hp₀.ne']

theorem localizedSpacetimeRpowMoment_gain_le_of_evolving_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p a innerTime outerTime level₀ level₁ level₂ level₃
      C G B t₀ : ℝ}
    (hp_pos : 0 < p) (hp_one : p < 1)
    (haInner : a ≤ innerTime) (hinnerOuter : innerTime < outerTime)
    (hlevel₀₁ : level₀ < level₁) (hlevel₁₂ : level₁ < level₂)
    (hlevel₂₃ : level₂ < level₃)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a innerTime,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a outerTime, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc a outerTime, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc a outerTime, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (Cfixed Cmoving : ℝ≥0∞)
    (hCfixed : Cfixed ≠ ⊤) (hCmoving : Cmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc a innerTime,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Cfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc a outerTime,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Cmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric) :
    let n := Module.finrank ℝ E
    let K := CutoffProfile.derivBound ^ 2 * G / (level₂ - level₁) ^ 2
    localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialCutoffBetween rho level₂ level₃) u
        (parabolicMoserGain n * p) a innerTime ≤
      Cfixed.toReal * C *
        (evolvingForwardMoserStepCoefficient p a innerTime outerTime K B *
          (Cmoving.toReal * localizedSpacetimeRpowMoment (I := I) (M := M)
            (spatialCutoffBetween rho level₀ level₁) u p a outerTime)) ^
          parabolicMoserGain n := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let outer := spatialCutoffBetween rho level₀ level₁
  let middle := spatialCutoffBetween rho level₁ level₂
  let inner := spatialCutoffBetween rho level₂ level₃
  let K := CutoffProfile.derivBound ^ 2 * G / (level₂ - level₁) ^ 2
  let L := localizedSpacetimeRpowMoment (I := I) (M := M)
    outer u p a outerTime
  let Lmoving := ∫ t in a..outerTime,
    evolvingLocalizedL2Mass
      (I := I) (M := M) g outer.toFun (fun s x => u s x ^ (p / 2)) t
  let critical : ℝ → M → ℝ := fun t x =>
    |middle.toFun x * u t x ^ (p / 2)| ^ (2 + 4 / (n : ℝ))
  have haOuter : a ≤ outerTime := haInner.trans hinnerOuter.le
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcriticalExponent : 0 ≤ 2 + 4 / (n : ℝ) := by positivity
  have hcritical_cont : Continuous (fun z : ℝ × M => critical z.1 z.2) := by
    apply Continuous.rpow_const
    · exact (((middle.smooth.continuous.comp continuous_snd).mul
        (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne'))).abs
    · exact fun _ => Or.inr hcriticalExponent
  have hcritical_nonneg : ∀ t x, 0 ≤ critical t x :=
    fun t x => Real.rpow_nonneg (abs_nonneg _) _
  have hK : 0 ≤ K := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (sq_nonneg _)
  have hL : 0 ≤ L :=
    localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      outer u (fun t x => (hpos t x).le) p a outerTime
  have houterIntegrand_cont : Continuous (fun z : ℝ × M =>
      outer.toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    (outer.smooth.continuous.comp continuous_snd).pow 2 |>.mul
      (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne')
  have houterCompare := intervalIntegral_moving_le_fixed_of_volume_le
    (I := I) (M := M) qMetric g
      (fun t x => outer.toFun x ^ 2 * u t x ^ p)
      houterIntegrand_cont
      (fun t x => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hpos t x).le _))
      haOuter hg Cmoving hCmoving hmovingVolume
  have hLmoving_eq : Lmoving =
      ∫ t in a..outerTime, ∫ x, outer.toFun x ^ 2 * u t x ^ p
        ∂(riemannianMeasureFamily (I := I) (M := M) g t) := by
    dsimp only [Lmoving, evolvingLocalizedL2Mass]
    apply intervalIntegral.integral_congr
    intro t _
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    rw [← Real.rpow_natCast (u t x ^ (p / 2)) 2,
      ← Real.rpow_mul (hpos t x).le]
    congr 1
    ring
  have hfixedOuter_eq :
      (∫ t in a..outerTime, ∫ x, outer.toFun x ^ 2 * u t x ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) = L := by
    dsimp only [L]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) outer u hu.continuous hpos haOuter]
  have hLmoving : Lmoving ≤ Cmoving.toReal * L := by
    calc
      Lmoving =
          ∫ t in a..outerTime, ∫ x, outer.toFun x ^ 2 * u t x ^ p
            ∂(riemannianMeasureFamily (I := I) (M := M) g t) := hLmoving_eq
      _ ≤ Cmoving.toReal *
          (∫ t in a..outerTime, ∫ x, outer.toFun x ^ 2 * u t x ^ p
            ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) := by
        simpa only [] using houterCompare
      _ = Cmoving.toReal * L := congrArg (fun r => Cmoving.toReal * r) hfixedOuter_eq
  have hreverse := evolving_positive_rpow_reverse_holder_step
    (I := I) (M := M) g hdim middle.toFun outer.toFun middle.smooth outer.smooth
      u hu hpos hp_pos hp_one haInner hinnerOuter hC hK hB
      (mul_nonneg ENNReal.toReal_nonneg hL) hg hgram hSobolev htrace hpde
      (fun x => by
        simpa only [middle, outer] using
          spatialCutoffBetween_sq_le rho hlevel₀₁ hlevel₁₂ x)
      (fun t ht x => by
        let rhoAt : SmoothScalar (g t) := ⟨rho.toFun, rho.smooth⟩
        simpa only [middle, outer, K, rhoAt] using
          spatialCutoffBetween_gradient_le (I := I) (g t) rhoAt
            hlevel₀₁ hlevel₁₂ hG (hrho t ht) x)
      hLmoving
  have hbridge := localizedSpacetimeRpowMoment_gain_le n rho u hu hpos
    haInner hlevel₁₂ hlevel₂₃ (q := p)
  have hcriticalCompare := intervalIntegral_fixed_le_moving_of_volume_le
    (I := I) (M := M) qMetric g critical hcritical_cont hcritical_nonneg
      haInner hg Cfixed hCfixed hfixedVolume
  change localizedSpacetimeRpowMoment (I := I) (M := M) inner u
      (parabolicMoserGain n * p) a innerTime ≤
    Cfixed.toReal * C *
      (evolvingForwardMoserStepCoefficient p a innerTime outerTime K B *
        (Cmoving.toReal * L)) ^ parabolicMoserGain n
  calc
    localizedSpacetimeRpowMoment (I := I) (M := M) inner u
          (parabolicMoserGain n * p) a innerTime ≤
        ∫ t in a..innerTime, ∫ x, critical t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric) := by
      simpa only [inner, middle, critical] using hbridge
    _ ≤ Cfixed.toReal *
        (∫ t in a..innerTime, ∫ x, critical t x
          ∂(riemannianMeasureFamily (I := I) (M := M) g t)) :=
      hcriticalCompare
    _ ≤ Cfixed.toReal *
        (C * (((innerTime - a + 1) *
            evolvingPositiveRpowCommonEnergyBound p innerTime outerTime K B
              (Cmoving.toReal * L) + K * (Cmoving.toReal * L)) ^
          parabolicMoserGain n)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [critical, n, parabolicMoserGain] using hreverse)
        ENNReal.toReal_nonneg
    _ = Cfixed.toReal * C *
        (evolvingForwardMoserStepCoefficient p a innerTime outerTime K B *
          (Cmoving.toReal * L)) ^ parabolicMoserGain n := by
      have hfactor :
          (innerTime - a + 1) *
                evolvingPositiveRpowCommonEnergyBound p innerTime outerTime K B
                  (Cmoving.toReal * L) + K * (Cmoving.toReal * L) =
            evolvingForwardMoserStepCoefficient p a innerTime outerTime K B *
              (Cmoving.toReal * L) := by
        unfold evolvingForwardMoserStepCoefficient
          evolvingPositiveRpowCommonEnergyBound evolvingPositiveRpowEnergyBound
        ring
      rw [hfactor]
      ring

def evolvingNestedForwardMoserStepFactor
    (n : ℕ) (V : ℝ≥0∞) (C G B p₀ a : ℝ)
    (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  (V.toReal * C) ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
    (evolvingForwardMoserStepCoefficient
        (parabolicMoserExponent n p₀ k) a
        (upperTime (k + 1)) (upperTime k)
        (nestedForwardMoserGradientCost G level k) B * V.toReal) ^
      (1 / parabolicMoserExponent n p₀ k)

theorem nestedForwardMoserNorm_succ_le_of_evolving_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a C G B t₀ : ℝ} (V : ℝ≥0∞)
    (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (haTime : a ≤ upperTime (k + 1))
    (htime : upperTime (k + 1) < upperTime k)
    (hlevel₀₁ : level (2 * k) < level (2 * k + 1))
    (hlevel₁₂ : level (2 * k + 1) < level (2 * k + 2))
    (hlevel₂₃ : level (2 * k + 2) < level (2 * k + 3))
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a (upperTime k),
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a (upperTime k),
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime (k + 1) ≤
      evolvingNestedForwardMoserStepFactor (Module.finrank ℝ E)
          V C G B p₀ a level upperTime k *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost G level k
  let coefficient :=
    evolvingForwardMoserStepCoefficient p a
      (upperTime (k + 1)) (upperTime k) K B * V.toReal
  let L := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime k
  let L' := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime (k + 1)
  have hp_pos : 0 < p := parabolicMoserExponent_pos n hp₀ k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (sq_nonneg _)
  have hstepCoefficient : 0 ≤
      evolvingForwardMoserStepCoefficient p a
        (upperTime (k + 1)) (upperTime k) K B :=
    evolvingForwardMoserStepCoefficient_nonneg hp_pos
      (by simpa only [p, n] using hexponent_one) haTime htime hK hB
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg hstepCoefficient ENNReal.toReal_nonneg
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) p a (upperTime k)
  have hL' : 0 ≤ L' := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * (k + 1)))
        (level (2 * (k + 1) + 1)))
      u (fun t x => (hpos t x).le)
      (parabolicMoserExponent n p₀ (k + 1)) a (upperTime (k + 1))
  have hstep₀ := localizedSpacetimeRpowMoment_gain_le_of_evolving_supersolution
    (I := I) (M := M) qMetric g hdim rho u hu hpos hp_pos
      (by simpa only [p, n] using hexponent_one) haTime htime
      hlevel₀₁ hlevel₁₂ hlevel₂₃ hC hG hB hg hgram
      (fun t ht => hSobolev t ⟨ht.1, ht.2.trans htime.le⟩)
      htrace hrho hpde V V hVtop hVtop
      (fun t ht => (hvolume t ⟨ht.1, ht.2.trans htime.le⟩).2)
      (fun t ht => (hvolume t ht).1)
  have hstep : L' ≤ V.toReal * C *
      (coefficient * L) ^ parabolicMoserGain n := by
    simpa only [L, L', coefficient, K, p, nestedForwardMoserMoment,
      parabolicMoserExponent_succ, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      n, mul_assoc] using hstep₀
  have hnormalized := normalized_exponent_gain_step
    hL hL' (mul_nonneg ENNReal.toReal_nonneg hC) hcoefficient
      (parabolicMoserGain_pos n) hp_pos hstep
  simpa only [nestedForwardMoserNorm, evolvingNestedForwardMoserStepFactor,
    L, L', coefficient, K, p, parabolicMoserExponent_succ, n, mul_assoc] using
      hnormalized

theorem nestedForwardMoserNorm_succ_le_exp_of_evolving_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ qbar a τ b C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_le :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar)
    (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc a b, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) (k + 1) ≤
      Real.exp
          (canonicalEvolvingForwardMoserIterationCost
            (Module.finrank ℝ E) V C p₀ qbar a τ b G B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let p := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost G level k
  let coefficient := evolvingForwardMoserStepCoefficient p a
    (upperTime (k + 1)) (upperTime k) K B * V.toReal
  let L := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime k
  let L' := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime (k + 1)
  let C₀ := max 1 (V.toReal * C)
  let A := canonicalEvolvingForwardMoserStepEnvelope
    V qbar a τ b G B lower upper
  have hp_pos : 0 < p := parabolicMoserExponent_pos n hp₀ k
  have hp_one : p < 1 := hexponent_le.trans_lt hqbar_one
  have hlevel := moserCutoffLevelBetween_strictMono hlowerUpper
  have haTime : a ≤ upperTime (k + 1) :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have htime : upperTime (k + 1) < upperTime k :=
    moserUpperTimeLevel_succ_lt hτb k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (sq_nonneg _)
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg
      (evolvingForwardMoserStepCoefficient_nonneg hp_pos hp_one
        haTime htime hK hB) ENNReal.toReal_nonneg
  have hcoefficient_bound : coefficient ≤ A * 16 ^ k := by
    have hraw := evolvingForwardMoserStepCoefficient_canonical_le_mul_pow k
      hp_pos.le hexponent_le hqbar_one haτ hτb hG hB hlowerUpper
    calc
      coefficient ≤
          (evolvingForwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ))
            (canonicalForwardMoserGradientCost G lower upper) B * 16 ^ k) *
              V.toReal := mul_le_mul_of_nonneg_right hraw ENNReal.toReal_nonneg
      _ = (V.toReal * evolvingForwardMoserStepCoefficientEnvelope qbar a b
            (2 / (b - τ)) (canonicalForwardMoserGradientCost G lower upper) B) *
          16 ^ k := by ring
      _ ≤ A * 16 ^ k := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (pow_nonneg (by norm_num) k)
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) p a (upperTime k)
  have hL' : 0 ≤ L' := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * (k + 1)))
        (level (2 * (k + 1) + 1)))
      u (fun t x => (hpos t x).le)
      (parabolicMoserExponent n p₀ (k + 1)) a (upperTime (k + 1))
  have hstep₀ := localizedSpacetimeRpowMoment_gain_le_of_evolving_supersolution
    (I := I) (M := M) qMetric g hdim rho u hu hpos hp_pos hp_one
      haTime htime
      (hlevel (Nat.lt_succ_self (2 * k)))
      (hlevel (Nat.lt_succ_self (2 * k + 1)))
      (hlevel (Nat.lt_succ_self (2 * k + 2)))
      hC hG hB hg hgram
      (fun t ht => hSobolev t
        ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb (k + 1))⟩)
      (fun t ht => htrace t ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩)
      (fun t ht => hrho t ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩)
      (fun t ht => hpde t ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩)
      V V hVtop hVtop
      (fun t ht => (hvolume t
        ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb (k + 1))⟩).2)
      (fun t ht => (hvolume t
        ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩).1)
  have hstep : L' ≤ V.toReal * C *
      (coefficient * L) ^ parabolicMoserGain n := by
    simpa only [L, L', coefficient, K, p, level, upperTime,
      nestedForwardMoserMoment, parabolicMoserExponent_succ,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc, n, mul_assoc] using hstep₀
  have hstep_envelope :
      L' ≤ C₀ * ((A * 16 ^ k) * L) ^ parabolicMoserGain n := by
    calc
      L' ≤ V.toReal * C *
          (coefficient * L) ^ parabolicMoserGain n := hstep
      _ ≤ C₀ * ((A * 16 ^ k) * L) ^ parabolicMoserGain n := by
        exact mul_le_mul (le_max_right _ _)
          (Real.rpow_le_rpow (mul_nonneg hcoefficient hL)
            (mul_le_mul_of_nonneg_right hcoefficient_bound hL)
            (parabolicMoserGain_pos n).le)
          (Real.rpow_nonneg (mul_nonneg hcoefficient hL) _)
          (zero_le_one.trans (le_max_left _ _))
  have hnormalized := normalized_moser_step n hp₀
    (show 1 ≤ C₀ from le_max_left _ _)
    (show 1 ≤ A from le_max_left _ _)
    hL hL' k hstep_envelope
  simpa only [nestedForwardMoserNorm, L, L', C₀, A, level, upperTime,
    canonicalEvolvingForwardMoserIterationCost, n] using hnormalized

theorem nestedForwardMoserNorm_le_exp_of_evolving_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ qbar a τ b C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞) (m : ℕ)
    (hp₀ : 0 < p₀) (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc a b, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m ≤
      Real.exp
          (∑' k, canonicalEvolvingForwardMoserIterationCost
            (Module.finrank ℝ E) V C p₀ qbar a τ b G B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let X : ℕ → ℝ := fun k =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime k
  let C₀ := max 1 (V.toReal * C)
  let A := canonicalEvolvingForwardMoserStepEnvelope
    V qbar a τ b G B lower upper
  let theta := parabolicMoserDecay n
  let c₀ := (theta * Real.log C₀ + Real.log A) / p₀
  let c₁ := Real.log 16 / p₀
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  have hA : 1 ≤ A := le_max_left _ _
  have hc₀ : 0 ≤ c₀ := by
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (parabolicMoserDecay_pos n).le (Real.log_nonneg hC₀))
        (Real.log_nonneg hA)) hp₀.le
  have hc₁ : 0 ≤ c₁ :=
    div_nonneg (Real.log_nonneg (by norm_num)) hp₀.le
  have hX_zero : 0 ≤ X 0 := by
    unfold X nestedForwardMoserNorm
    exact Real.rpow_nonneg
      (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) u
        (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ 0)
        a (upperTime 0)) _
  have hstep : ∀ k < m,
      X (k + 1) ≤ Real.exp (moserIterationCost theta c₀ c₁ k) * X k := by
    intro k hk
    have h := nestedForwardMoserNorm_succ_le_exp_of_evolving_supersolution
      (I := I) (M := M) qMetric g hdim rho u hu hpos V k hp₀
        (by simpa only [n] using hexponents k hk) hqbar_one haτ hτb
        hC hG hB hlowerUpper hg hgram hSobolev htrace hrho hpde hVtop hvolume
    simpa only [X, level, upperTime, theta, c₀, c₁, C₀, A,
      canonicalEvolvingForwardMoserIterationCost, n] using h
  have hbound := finite_moser_iteration_bound m hX_zero
    (parabolicMoserDecay_pos n).le (parabolicMoserDecay_lt_one n)
    hc₀ hc₁ hstep
  simpa only [X, level, upperTime, theta, c₀, c₁, C₀, A,
    canonicalEvolvingForwardMoserIterationCost, n] using hbound

theorem nestedForwardMoserNorm_le_evolvingReverseCost_rpow_of_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ q a τ b C G B lower upper t₀ : ℝ} {m : ℕ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc a b,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc a b, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc a b, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) (g t) (smoothScalarSlice (I := I) (g t) u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc a b,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ q)
    (hm : 0 < m)
    (htarget : parabolicMoserExponent (Module.finrank ℝ E) p₀ m = q) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m ≤
      canonicalEvolvingForwardMoserReverseCost
          (Module.finrank ℝ E) V C q a τ b G B lower upper ^
            (1 / p₀ - 1 / q) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let D := canonicalEvolvingForwardMoserLogCost
    n V C q a τ b G B lower upper
  let X₀ := nestedForwardMoserNorm (I := I) (M := M) n
    rho u p₀ a (moserCutoffLevelBetween lower upper)
      (moserUpperTimeLevel τ b) 0
  have hbound := nestedForwardMoserNorm_le_exp_of_evolving_supersolution
    (I := I) (M := M) qMetric g hdim rho u hu hpos V m hp₀ hq_one
      haτ hτb hC hG hB hlowerUpper hg hgram hSobolev htrace hrho hpde
      hVtop hvolume hexponents
  rw [tsum_canonicalEvolvingForwardMoserIterationCost
    n V hp₀ C q a τ b G B lower upper] at hbound
  have hprefactor := exp_div_le_rpow_exponent_gap n
    (canonicalEvolvingForwardMoserLogCost_nonneg
      n V C q a τ b G B lower upper)
    hp₀ hm (by simpa only [n] using htarget)
  have hX₀ : 0 ≤ X₀ := by
    unfold X₀ nestedForwardMoserNorm
    exact Real.rpow_nonneg
      (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper 0)
          (moserCutoffLevelBetween lower upper 1)) u
        (fun t x => (hpos t x).le)
        (parabolicMoserExponent n p₀ 0) a (moserUpperTimeLevel τ b 0)) _
  calc
    nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) m ≤ Real.exp (D / p₀) * X₀ := by
      simpa only [D, X₀, n] using hbound
    _ ≤ canonicalEvolvingForwardMoserReverseCost
          n V C q a τ b G B lower upper ^ (1 / p₀ - 1 / q) * X₀ := by
      exact mul_le_mul_of_nonneg_right (by
        simpa only [D, canonicalEvolvingForwardMoserReverseCost] using hprefactor) hX₀
    _ = _ := by rfl

end DifferentialGeometry.Analysis.Parabolic.Moser

end
