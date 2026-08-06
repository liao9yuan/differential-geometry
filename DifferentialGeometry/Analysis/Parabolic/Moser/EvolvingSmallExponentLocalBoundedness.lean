import DifferentialGeometry.Analysis.HoleFilling
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingBombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeSup

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def evolvingMoserSmallExponentStepFactor
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalEvolvingLateBombieriGiustiReverseCost
    n Vfixed Vmoving C G B τ c d D lower upper k ^ (1 / 2 : ℝ)

def evolvingMoserSmallExponentLocalBoundFactor
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B p τ c d D lower upper : ℝ) : ℝ :=
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  ∑' k : ℕ, theta ^ k *
    (alpha *
      (evolvingMoserSmallExponentStepFactor
          n Vfixed Vmoving C G B τ c d D lower upper k *
        (beta / theta) ^ beta) ^ (1 / alpha))

theorem summable_evolvingMoserSmallExponentLocalBoundCost
    (n : ℕ) [NeZero n] (Vfixed Vmoving : ℝ≥0∞)
    {C G B p τ c d D lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    let alpha := p / 2
    let beta := 1 - alpha
    let theta : ℝ := 1 / 2
    Summable (fun k : ℕ => theta ^ k *
      (alpha *
        (evolvingMoserSmallExponentStepFactor
            n Vfixed Vmoving C G B τ c d D lower upper k *
          (beta / theta) ^ beta) ^ (1 / alpha))) := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  let F : ℕ → ℝ := fun k =>
    evolvingMoserSmallExponentStepFactor
      n Vfixed Vmoving C G B τ c d D lower upper k
  let degree := 2 * (n + 2)
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  have htheta : 0 < theta := by norm_num [theta]
  rcases exists_polynomial_bound_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving hτc hcd hdD hG hB hlowerUpper with
    ⟨L, hL, hcost⟩
  let R := (beta / theta) ^ beta
  let K := alpha * (L * R) ^ (1 / alpha)
  let s := (degree : ℝ) / alpha
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hbeta htheta) _
  have hK : 0 ≤ K := mul_nonneg halpha.le
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hL) hR.le) _)
  have hF : ∀ k, F k ≤ L * (k + 1 : ℝ) ^ degree := by
    intro k
    calc
      F k ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k := by
        exact Real.rpow_le_self_of_one_le
          (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
            n Vfixed Vmoving C G B τ c d D lower upper k)
          (by norm_num)
      _ ≤ L * (k + 1 : ℝ) ^ degree := by
        simpa only [degree] using hcost k
  have hpoint : ∀ k, alpha * (F k * R) ^ (1 / alpha) ≤
      K * (k + 1 : ℝ) ^ s := by
    intro k
    let m : ℝ := k + 1
    have hm : 0 < m := by positivity
    have hFR : F k * R ≤ (L * m ^ degree) * R :=
      mul_le_mul_of_nonneg_right (by simpa only [m] using hF k) hR.le
    have hrpow := Real.rpow_le_rpow
      (mul_nonneg
        (Real.rpow_nonneg
          (zero_le_one.trans
            (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
              n Vfixed Vmoving C G B τ c d D lower upper k)) _)
        hR.le)
      hFR (div_pos one_pos halpha).le
    calc
      alpha * (F k * R) ^ (1 / alpha) ≤
          alpha * ((L * m ^ degree) * R) ^ (1 / alpha) :=
        mul_le_mul_of_nonneg_left hrpow halpha.le
      _ = K * m ^ s := by
        have hpower : ((L * m ^ degree) * R) ^ (1 / alpha) =
            (L * R) ^ (1 / alpha) *
              m ^ ((degree : ℝ) * (1 / alpha)) := by
          rw [show (L * m ^ degree) * R = (L * R) * m ^ degree by ring,
            Real.mul_rpow (mul_nonneg (zero_le_one.trans hL) hR.le)
              (pow_nonneg hm.le degree),
            ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
        have hexponent : (degree : ℝ) * (1 / alpha) =
            (degree : ℝ) / alpha := by
          field_simp [halpha.ne']
        rw [hpower, hexponent]
        dsimp only [K, s]
        ring
      _ = K * (k + 1 : ℝ) ^ s := by rfl
  have hmajor : Summable (fun k : ℕ =>
      theta ^ k * (K * (k + 1 : ℝ) ^ s)) := by
    have hs := summable_geometric_mul_nat_add_rpow
      (r := theta) (by norm_num [theta])
      (by norm_num [theta, Real.norm_eq_abs]) s
    refine (hs.mul_right K).congr ?_
    intro k
    ring
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg htheta.le k)
      (mul_nonneg halpha.le (Real.rpow_nonneg
        (mul_nonneg
          (Real.rpow_nonneg
            (zero_le_one.trans
              (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
                n Vfixed Vmoving C G B τ c d D lower upper k)) _)
          hR.le) _))
  · intro k
    exact mul_le_mul_of_nonneg_left (hpoint k) (pow_nonneg htheta.le k)
  · simpa only [alpha, beta, theta, F, R] using hmajor

theorem evolvingMoserSmallExponentLocalBoundFactor_nonneg
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B : ℝ) {p τ c d D lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2) :
    0 ≤ evolvingMoserSmallExponentLocalBoundFactor
      n Vfixed Vmoving C G B p τ c d D lower upper := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  unfold evolvingMoserSmallExponentLocalBoundFactor
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k)
    (mul_nonneg halpha.le (Real.rpow_nonneg
      (mul_nonneg
        (Real.rpow_nonneg
          (zero_le_one.trans
            (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
              n Vfixed Vmoving C G B τ c d D lower upper k)) _)
        (Real.rpow_nonneg (div_nonneg hbeta.le (by norm_num)) _)) _))

end DifferentialGeometry.Analysis.Parabolic.Moser

end
